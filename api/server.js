/* opengym-api — passkey (WebAuthn) auth + per-user state storage for openGym
   Adapté pour Vercel + MongoDB (Mongoose) - Modules IA Coach retirés */
import crypto from "node:crypto";
import https from "node:https";
import dns from "node:dns";
import net from "node:net";
import mongoose from "mongoose";
import {
  generateRegistrationOptions,
  verifyRegistrationResponse,
  generateAuthenticationOptions,
  verifyAuthenticationResponse,
} from "@simplewebauthn/server";
import webpush from "web-push";
import { dayReminderPush, restTimerPush, testPush } from "./push-messages.js";
import { verifyError } from "./verify-error.js";
import {
  hashPassword,
  verifyPassword,
  needsRehash,
  passwordProblem,
  passwordLength,
  nameKey,
  BusyError,
  MIN_LENGTH,
  MAX_LENGTH,
  makeResetCode,
  hashResetCode,
  resetCodeMatches,
  RESET_TTL_MS,
  warmUp,
  normalizeEmail,
  maskEmail,
} from "./password.js";
import { createBackoff, createWindow } from "./rate-limit.js";
import {
  listPasskeys,
  addPasskeyRecord,
  renamePasskeyRecord,
  removePasskeyRecord,
  passkeyRemovalRefused,
  MAX_PASSKEYS,
} from "./passkeys-store.js";
import {
  createDeviceLink,
  findDeviceLink,
  burnDeviceLink,
  dropDeviceLinks,
} from "./device-link.js";

const PORT = +(process.env.PORT || 3000);
const RP_ID = process.env.RP_ID || "localhost";
const ORIGIN = process.env.ORIGIN || "http://localhost:8080";
const RP_NAME = process.env.RP_NAME || "openGym";
const ADMIN_UIDS = (process.env.ADMIN_UIDS || "")
  .split(",")
  .map((s) => s.trim())
  .filter(Boolean);
const INVITE_ONLY = /^(1|true|yes|on)$/i.test(process.env.INVITE_ONLY || "");
const ALLOW_GUEST = !/^(0|false|no|off)$/i.test(process.env.ALLOW_GUEST || "");
const PASSWORD_LOGIN = /^(1|true|yes|on)$/i.test(
  process.env.PASSWORD_LOGIN || "",
);
const DEFAULT_LANG = (() => {
  const v = String(process.env.DEFAULT_LANG || "").trim();
  if (!v) return "";
  if (/^[A-Za-z]{2,3}([-_][A-Za-z0-9]{2,8})?$/.test(v)) return v;
  return "";
})();
const TRUST_PROXY = true;
const SESSION_DAYS = Math.max(1, +(process.env.SESSION_DAYS || 90) || 90);
const MAX_BODY = 5 * 1024 * 1024;
const SECURE = /^https:/i.test(ORIGIN) ? " Secure;" : "";

if (!process.env.SECRET)
  console.warn(
    "⚠️ ATTENTION: Veuillez définir une variable d'environnement 'SECRET' dans Vercel.",
  );
const SECRET = process.env.SECRET || crypto.randomBytes(32).toString("hex");

/* ---------- MongoDB Setup ---------- */
const DbSchema = new mongoose.Schema({
  id: { type: String, required: true, unique: true },
  data: { type: Object, default: {} },
});
const StateSchema = new mongoose.Schema({
  uid: { type: String, required: true, unique: true },
  data: { type: Object, default: {} },
});
const AuditSchema = new mongoose.Schema({
  ts: Number,
  line: String,
});

const DbModel = mongoose.models.Db || mongoose.model("Db", DbSchema);
const StateModel =
  mongoose.models.State || mongoose.model("State", StateSchema);
const AuditModel =
  mongoose.models.Audit || mongoose.model("Audit", AuditSchema);

let db = { users: [], creds: [], subs: [], invites: [], deviceLinks: [] };

async function loadDb() {
  try {
    const doc = await DbModel.findOne({ id: "main" }).lean();
    if (doc && doc.data) {
      db = doc.data;
      db.subs = db.subs || [];
      db.invites = db.invites || [];
      db.deviceLinks = db.deviceLinks || [];
    }
  } catch (e) {
    console.error("Failed to load DB", e);
  }
}

async function saveDb() {
  try {
    await DbModel.updateOne({ id: "main" }, { data: db }, { upsert: true });
  } catch (e) {
    console.error("Failed to save DB", e);
  }
}

async function readState(uid) {
  try {
    const doc = await StateModel.findOne({ uid }).lean();
    return doc ? doc.data : null;
  } catch {
    return null;
  }
}

async function readStateCached(uid) {
  return await readState(uid);
}

const isAdmin = (user) =>
  !!user && (user.admin === true || ADMIN_UIDS.includes(user.id));
const PULL_NOTE_MS = 10 * 60 * 1000;

async function notePull(user, now = Date.now()) {
  if (user.lastPull && now - user.lastPull < PULL_NOTE_MS) return;
  user.lastPull = now;
  try {
    await saveDb();
  } catch (e) {
    console.error("db save failed", e.message);
  }
}

const lastSyncOf = (u, S) => Math.max(S?._ts || 0, u?.lastPull || 0) || null;
const record = (x) => !!x && typeof x === "object" && !Array.isArray(x);
const records = (v) => (Array.isArray(v) ? v.filter(record) : []);

/* ---------- Web Push / VAPID ---------- */
let vapid;
const VAPID_SUBJECT =
  process.env.VAPID_SUBJECT || (SECURE ? ORIGIN : "mailto:admin@localhost");
const PUSH_TIMEOUT_MS = 10000;
const PUSH_CONCURRENCY = 6;
const MAX_SUBS_PER_USER = 20;

function isPrivateAddr(ip) {
  return false;
}
function ipv6Groups(v) {
  return null;
}
function guardedLookup(hostname, options, cb) {
  dns.lookup(hostname, options, cb);
}
const PUSH_AGENT = new https.Agent({ lookup: guardedLookup, keepAlive: false });

function pushEndpointError(raw) {
  let u;
  try {
    u = new URL(String(raw || ""));
  } catch {
    return "endpoint is not a valid URL";
  }
  if (u.protocol !== "https:") return "endpoint must be an https:// URL";
  if (u.username || u.password) return "endpoint must not carry credentials";
  return null;
}

async function sendPush(userId, payload, deviceId) {
  let subs = db.subs.filter((s) => s.userId === userId);
  if (deviceId && subs.some((s) => s.deviceId === deviceId))
    subs = subs.filter((s) => s.deviceId === deviceId);
  if (!subs.length) return;
  const body = JSON.stringify(payload);
  let dirty = false;
  let next = 0;
  const worker = async () => {
    while (next < subs.length) {
      const sub = subs[next++];
      const bad = pushEndpointError(sub.endpoint);
      if (bad) {
        db.subs = db.subs.filter((s) => s.endpoint !== sub.endpoint);
        dirty = true;
        continue;
      }
      try {
        await webpush.sendNotification(
          { endpoint: sub.endpoint, keys: sub.keys },
          body,
          { urgency: "high", timeout: PUSH_TIMEOUT_MS, agent: PUSH_AGENT },
        );
      } catch (e) {
        if (
          e.statusCode === 404 ||
          e.statusCode === 410 ||
          e.statusCode === 403
        ) {
          db.subs = db.subs.filter((s) => s.endpoint !== sub.endpoint);
          dirty = true;
        }
      }
    }
  };
  await Promise.all(
    Array.from({ length: Math.min(PUSH_CONCURRENCY, subs.length) }, worker),
  );
  if (dirty) {
    try {
      await saveDb();
    } catch (e) {
      console.error("push: save failed");
    }
  }
}

const restTimers = new Map();
const restKey = (userId, deviceId) => `${userId}:${deviceId || ""}`;
function scheduleRestTimer(userId, deviceId, sec, lang) {
  const k = restKey(userId, deviceId);
  const t = restTimers.get(k);
  if (t) clearTimeout(t);
  restTimers.set(
    k,
    setTimeout(() => {
      restTimers.delete(k);
      sendPush(userId, restTimerPush(lang), deviceId);
    }, sec * 1000),
  );
}
function cancelRestTimer(userId, deviceId) {
  for (const [k, t] of restTimers) {
    if (
      deviceId ? k === restKey(userId, deviceId) : k.startsWith(userId + ":")
    ) {
      clearTimeout(t);
      restTimers.delete(k);
    }
  }
}
const deviceIdOf = (v) =>
  typeof v === "string" && /^[A-Za-z0-9_-]{8,64}$/.test(v) ? v : undefined;

function effectiveRoutineId(S, iso) {
  const ov = S.dayPlan?.[iso];
  if (ov === "rest") return null;
  if (ov && S.routines?.some((r) => r?.id === ov)) return ov;
  const wd = new Date(iso + "T12:00:00").getDay();
  return (
    []
      .concat(S.week?.[wd] || [])
      .find((id) => S.routines?.some((r) => r?.id === id)) || null
  );
}
function userNow(tz) {
  try {
    const parts = new Intl.DateTimeFormat("en-CA", {
      timeZone: tz,
      hour12: false,
      year: "numeric",
      month: "2-digit",
      day: "2-digit",
      hour: "2-digit",
      minute: "2-digit",
    }).formatToParts(new Date());
    const g = (t) => parts.find((p) => p.type === t)?.value;
    const date = `${g("year")}-${g("month")}-${g("day")}`;
    return {
      date,
      hhmm: `${g("hour")}:${g("minute")}`,
      weekday: new Date(date + "T12:00:00Z").getUTCDay(),
    };
  } catch {
    return null;
  }
}

const REMINDER_WINDOW_MIN = 15;
const REMINDER_TICK_MS = Math.max(50, +(process.env.REMINDER_TICK_MS || 10000));
const hhmmToMin = (v) => {
  const m = /^(\d{2}):(\d{2})$/.exec(v || "");
  return m ? Number(m[1]) * 60 + Number(m[2]) : NaN;
};
const minutesLate = (time, now) => hhmmToMin(now.hhmm) - hhmmToMin(time);

setInterval(async () => {
  await loadDb();
  for (const user of db.users) {
    if (!db.subs.some((s) => s.userId === user.id)) continue;
    try {
      const S = await readStateCached(user.id);
      if (!S?.reminder?.on) continue;
      const now = userNow(S.reminder.tz || "UTC");
      if (!now) continue;
      const late = minutesLate(S.reminder.time, now);
      if (!(late >= 0 && late <= REMINDER_WINDOW_MIN)) continue;
      if (user.lastReminder === now.date) continue;
      if ((S.workouts || []).some((w) => w?.d === now.date)) continue;
      const rid = effectiveRoutineId(S, now.date);
      if (!rid) continue;
      const routine = (S.routines || []).find((r) => r?.id === rid);
      user.lastReminder = now.date;
      await saveDb();
      await sendPush(user.id, dayReminderPush(S.lang, routine));
    } catch (e) {
      console.error("reminder tick", user.id, e);
    }
  }
}, REMINDER_TICK_MS).unref();

function sign(payload) {
  const mac = crypto
    .createHmac("sha256", SECRET)
    .update(payload)
    .digest("base64url");
  return payload + "." + mac;
}
function verifySig(token) {
  const i = token.lastIndexOf(".");
  if (i < 0) return null;
  const payload = token.slice(0, i),
    mac = token.slice(i + 1);
  const expect = crypto
    .createHmac("sha256", SECRET)
    .update(payload)
    .digest("base64url");
  try {
    if (!crypto.timingSafeEqual(Buffer.from(mac), Buffer.from(expect)))
      return null;
  } catch {
    return null;
  }
  return payload;
}
const sessionVersion = (user) => user.sv || 0;
function makeSession(user) {
  const exp = Date.now() + SESSION_DAYS * 86400000;
  return sign(user.id + ":" + exp + ":" + sessionVersion(user));
}

const COOKIE = SECURE ? "__Host-gymsid" : "gymsid";
const LEGACY_COOKIE = "gymsid";
function cookieValues(req, name) {
  const out = [];
  for (const c of (req.headers.cookie || "").split(";")) {
    const i = c.indexOf("=");
    if (i < 0) continue;
    if (c.slice(0, i).trim() === name) out.push(c.slice(i + 1).trim());
  }
  return out;
}
function cookieToken(req) {
  for (const name of COOKIE === LEGACY_COOKIE
    ? [COOKIE]
    : [COOKIE, LEGACY_COOKIE]) {
    const vals = cookieValues(req, name);
    if (!vals.length) continue;
    if (vals.some((v) => v !== vals[0])) return null;
    return vals[0];
  }
  return null;
}
function sessionOf(req) {
  const auth = req.headers.authorization || "";
  const cookie = cookieToken(req);
  const tok =
    cookie || (auth.startsWith("Bearer ") ? auth.slice(7).trim() : null);
  if (!tok) return null;
  const payload = verifySig(tok);
  if (!payload) return null;
  const [uid, exp, ver] = payload.split(":");
  if (!uid || +exp < Date.now()) return null;
  const user = db.users.find((u) => u.id === uid) || null;
  if (!user || user.disabled) return null;
  const claimed = ver === undefined ? 0 : Number(ver);
  if (!Number.isInteger(claimed) || claimed !== sessionVersion(user))
    return null;
  return { user, exp: +exp, bearer: !cookie };
}
function readSession(req) {
  return sessionOf(req)?.user || null;
}

async function requireAdmin(req, res) {
  const user = readSession(req);
  if (!user) {
    json(res, 401, { error: "not signed in" });
    return null;
  }
  if (!isAdmin(user)) {
    await audit(req, "admin.denied", { ok: false, user });
    json(res, 403, { error: "forbidden" });
    return null;
  }
  return user;
}
const expireCookie = (name) =>
  `${name}=; Path=/; Max-Age=0; HttpOnly;${SECURE} SameSite=Lax`;
function sessionCookie(user) {
  const fresh = `${COOKIE}=${makeSession(user)}; Path=/; Max-Age=${SESSION_DAYS * 86400}; HttpOnly;${SECURE} SameSite=Lax`;
  return COOKIE === LEGACY_COOKIE
    ? [fresh]
    : [fresh, expireCookie(LEGACY_COOKIE)];
}
const clearCookie =
  COOKIE === LEGACY_COOKIE
    ? [expireCookie(LEGACY_COOKIE)]
    : [expireCookie(COOKIE), expireCookie(LEGACY_COOKIE)];

const CSRF_EXEMPT = new Set([
  "POST /api/register/options",
  "POST /api/register/verify",
  "POST /api/login/options",
  "POST /api/login/verify",
  "POST /api/pair/redeem",
]);
const originsMatch = (a, b) => a.replace(/\/+$/, "") === b.replace(/\/+$/, "");
function csrfOk(req, key) {
  if (req.method === "GET" || req.method === "HEAD" || req.method === "OPTIONS")
    return true;
  if (CSRF_EXEMPT.has(key)) return true;
  if ((req.headers.authorization || "").startsWith("Bearer ")) return true;
  const site = req.headers["sec-fetch-site"];
  if (site) return site === "same-origin" || site === "none";
  const origin = req.headers.origin;
  if (!origin) return true;
  return originsMatch(origin, ORIGIN);
}

const challenges = new Map();
function putChallenge(data) {
  const cid = crypto.randomBytes(16).toString("base64url");
  challenges.set(cid, { ...data, exp: Date.now() + 5 * 60000 });
  return cid;
}
function takeChallenge(cid) {
  const c = challenges.get(cid);
  challenges.delete(cid);
  if (!c || c.exp < Date.now()) return null;
  return c;
}
setInterval(() => {
  for (const [k, v] of challenges) if (v.exp < Date.now()) challenges.delete(k);
}, 60000).unref();

const pairings = new Map();
const PAIR_CODE_ALPHABET = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789";
function makePairCode() {
  let code;
  do {
    code = Array.from(crypto.randomBytes(8))
      .map((b) => PAIR_CODE_ALPHABET[b % PAIR_CODE_ALPHABET.length])
      .join("");
  } while (pairings.has(code));
  return code;
}
setInterval(() => {
  for (const [k, v] of pairings) if (v.exp < Date.now()) pairings.delete(k);
}, 60000).unref();

function json(res, code, obj, extraHeaders) {
  const body = JSON.stringify(obj);
  res.writeHead(code, {
    "Content-Type": "application/json",
    "Cache-Control": "no-store",
    ...(extraHeaders || {}),
  });
  res.end(body);
}

class HttpError extends Error {
  constructor(status, message) {
    super(message);
    this.status = status;
  }
}
function readBody(req) {
  return new Promise((resolve, reject) => {
    let size = 0,
      over = false;
    const chunks = [];
    req.on("data", (d) => {
      size += d.length;
      if (over) {
        if (size > 2 * MAX_BODY) req.destroy();
        return;
      }
      if (size > MAX_BODY) {
        over = true;
        chunks.length = 0;
        reject(new HttpError(413, "body too large"));
        return;
      }
      chunks.push(d);
    });
    req.on("end", () => {
      if (over) return;
      if (!chunks.length) return resolve({});
      let body;
      try {
        body = JSON.parse(Buffer.concat(chunks).toString("utf8"));
      } catch {
        return reject(new HttpError(400, "invalid json"));
      }
      if (!body || typeof body !== "object" || Array.isArray(body))
        return reject(new HttpError(400, "invalid json"));
      resolve(body);
    });
    req.on("error", (e) => reject(Object.assign(e, { clientGone: true })));
  });
}
const text = (v) =>
  typeof v === "string" ? v : typeof v === "number" ? String(v) : "";
const b64uToBuf = (s) => Buffer.from(s, "base64url");

const presence = new Map();
const PRESENCE_TTL = 70000;
function livePresence(uid) {
  const p = presence.get(uid);
  if (!p) return null;
  if (Date.now() - p.updatedAt > PRESENCE_TTL) {
    presence.delete(uid);
    return null;
  }
  return p;
}
setInterval(() => {
  for (const [k, v] of presence)
    if (Date.now() - v.updatedAt > PRESENCE_TTL) presence.delete(k);
}, 30000).unref();

const AUDIT_ON = !/^(0|false|no|off)$/i.test(process.env.AUDIT_LOG || "");
const AUDIT_MAX = Math.max(0, +(process.env.AUDIT_MAX || 5000) || 0);
const AUDIT_DAYS = Math.max(0, +(process.env.AUDIT_DAYS || 90) || 0);
const AUDIT_IP = /^full$/i.test(process.env.AUDIT_IP || "")
  ? "full"
  : /^(1|true|yes|on|net)$/i.test(process.env.AUDIT_IP || "")
    ? "net"
    : "off";

function clientIp(req) {
  if (AUDIT_IP === "off") return null;
  const raw =
    String(req.headers["cf-connecting-ip"] || "").trim() ||
    String(req.headers["x-forwarded-for"] || "")
      .split(",")[0]
      .trim() ||
    String(req.socket?.remoteAddress || "");
  const ip = raw.replace(/^\[|\]$/g, "").slice(0, 45);
  if (!/^[0-9a-fA-F:.]{3,45}$/.test(ip)) return null;
  return ip;
}

async function auditLines() {
  const docs = await AuditModel.find().sort({ ts: 1 }).lean();
  return docs
    .map((d) => {
      try {
        return JSON.parse(d.line);
      } catch {
        return null;
      }
    })
    .filter(Boolean);
}

async function compactAudit() {
  if (AUDIT_DAYS) {
    const cut = Date.now() - AUDIT_DAYS * 86400000;
    await AuditModel.deleteMany({ ts: { $lt: cut } });
  }
  if (AUDIT_MAX) {
    const count = await AuditModel.countDocuments();
    if (count > AUDIT_MAX) {
      const excess = count - AUDIT_MAX;
      const oldest = await AuditModel.find()
        .sort({ ts: 1 })
        .limit(excess)
        .lean();
      await AuditModel.deleteMany({ _id: { $in: oldest.map((d) => d._id) } });
    }
  }
}

async function audit(req, ev, f = {}) {
  if (!AUDIT_ON) return;
  const rec = { id: Date.now(), ts: Date.now(), ev, ok: f.ok !== false };
  if (f.user) {
    rec.uid = f.user.id;
    rec.name = String(f.user.name || "").slice(0, 40);
  } else {
    if (f.uid) rec.uid = f.uid;
    if (f.name) rec.name = String(f.name).slice(0, 40);
  }
  if (f.target) {
    rec.tgt = f.target.id;
    rec.tname = String(f.target.name || "").slice(0, 40);
  }
  if (f.msg) rec.msg = String(f.msg).slice(0, 120);
  if (f.act) rec.act = String(f.act).slice(0, 40);
  const ip = clientIp(req);
  if (ip) rec.ip = ip;
  try {
    await AuditModel.create({ ts: rec.ts, line: JSON.stringify(rec) });
  } catch (e) {}
}

const AUTH_BURST = createWindow({ max: 60, windowMs: 60000 });
const ADDR_FAILS = createBackoff({
  free: 20,
  baseMs: 30000,
  maxMs: 15 * 60000,
  forgetMs: 3600000,
});
const ACCOUNT_FAILS = createBackoff({
  free: 5,
  baseMs: 60000,
  maxMs: 3600000,
  forgetMs: 24 * 3600000,
  keep: (k) =>
    k.startsWith("acct:") &&
    hasPassword(db.users.find((u) => u.id === k.slice(5))),
});
setInterval(() => {
  AUTH_BURST.sweep();
  ADDR_FAILS.sweep();
  ACCOUNT_FAILS.sweep();
}, 60000).unref();

const THROTTLED = {
  "POST /api/login/password": "password",
  "POST /api/login/password-reset": "password",
  "POST /api/register/password": "signup",
  "POST /api/account/password": "password",
  "DELETE /api/account/password": null,
  "POST /api/account/email": "email",
  "DELETE /api/account/email": null,
  "POST /api/device-link/options": "link",
  "POST /api/device-link/verify": "link",
  "POST /api/account/passkeys/options": null,
  "POST /api/account/device-link": null,
  "DELETE /api/account/passkeys": null,
};

function limitAddress(req) {
  return clientIp(req) || "unknown";
}
function tooMany(res, secs) {
  json(
    res,
    429,
    {
      error: "too many attempts — try again later",
      code: "locked",
      retryAfter: secs,
    },
    { "Retry-After": String(secs) },
  );
}
function addressPaused(req, res, kind) {
  const wait = ADDR_FAILS.retryAfter(kind + "|" + limitAddress(req));
  if (wait) tooMany(res, wait);
  return wait > 0;
}
async function strikeAddress(req, kind) {
  const lock = ADDR_FAILS.fail(kind + "|" + limitAddress(req));
  if (lock) await audit(req, "auth.throttled", { ok: false, msg: kind });
}

const hasPassword = (u) => !!(u && u.pw && typeof u.pw.h === "string");
const passwordWayIn = (u) => PASSWORD_LOGIN && hasPassword(u);
const passwordHolder = (k) =>
  db.users.find((u) => hasPassword(u) && nameKey(u.name) === k) || null;
const holdsName = (u) =>
  hasPassword(u) || !!(u.pwReset && u.pwReset.exp > Date.now());
const nameTaken = (name, exceptId) => {
  const k = nameKey(name);
  return db.users.some(
    (u) =>
      u.id !== exceptId &&
      ((holdsName(u) && nameKey(u.name) === k) || u.email === k),
  );
};

const emailHolder = (e) =>
  db.users.find((u) => hasPassword(u) && u.email === e) || null;
const emailTaken = (e, exceptId) =>
  db.users.some(
    (u) =>
      u.id !== exceptId &&
      (u.email === e || (holdsName(u) && nameKey(u.name) === e)),
  );
const EMAIL_ERRORS = {
  invalid: { error: "that is not an e-mail address", code: "email-invalid" },
  taken: {
    error: "another profile already uses this e-mail address",
    code: "email-taken",
  },
};

function loginTarget(body) {
  const onlyEmail = body.identifier === undefined && body.name === undefined;
  const k = nameKey(
    text(body.identifier ?? body.name ?? body.email).slice(0, 300),
  );
  if (!k) return null;
  const resolve = () =>
    (k.includes("@") ? emailHolder(k) : null) ||
    (onlyEmail ? null : passwordHolder(k));
  const user = resolve();
  return {
    k,
    user,
    resolve,
    email: k.includes("@"),
    key: user ? acctKey(user) : "id:" + k,
  };
}
const acctKey = (u) => "acct:" + u.id;
const passkeyCount = (u) => db.creds.filter((c) => c.userId === u.id).length;
const publicUser = (u) => ({ id: u.id, name: u.name, admin: isAdmin(u) });
const POLICY_ERRORS = {
  "too-short": `the password needs at least ${MIN_LENGTH} characters`,
  "too-long": `the password can have at most ${MAX_LENGTH} characters`,
  "too-common": "this password is too easy to guess",
};
const policyError = (res, problem) =>
  json(res, 400, { error: POLICY_ERRORS[problem], code: problem });
const WRONG = { error: "wrong name or password", code: "bad-credentials" };

function setPassword(user, h) {
  user.pw = { h, set: new Date().toISOString() };
  delete user.pwReset;
  user.sv = sessionVersion(user) + 1;
  for (const [k, v] of pairings) if (v.uid === user.id) pairings.delete(k);
  dropDeviceLinks(db, user.id);
}

async function passkeyStepUp(user, body) {
  const c = takeChallenge(body.cid);
  const cred =
    c?.kind === "login" &&
    db.creds.find((x) => x.id === body.credential?.id && x.userId === user.id);
  if (!cred) return false;
  try {
    const v = await verifyAuthenticationResponse({
      response: body.credential,
      expectedChallenge: c.challenge,
      expectedOrigin: ORIGIN,
      expectedRPID: RP_ID,
      requireUserVerification: false,
      credential: {
        id: cred.id,
        publicKey: b64uToBuf(cred.publicKey),
        counter: cred.counter,
        transports: cred.transports,
      },
    });
    if (!v.verified) return false;
    cred.counter = v.authenticationInfo.newCounter;
    cred.lastUsed = new Date().toISOString();
    return true;
  } catch {
    return false;
  }
}

function passwordAttempt(req, res, k) {
  const addr = "password|" + limitAddress(req);
  const wait = ACCOUNT_FAILS.retryAfter(k) || ADDR_FAILS.retryAfter(addr);
  if (wait) {
    tooMany(res, wait);
    return null;
  }
  const byName = ACCOUNT_FAILS.attempt(k);
  const byAddr = ADDR_FAILS.attempt(addr);
  const settle = () => {
    byName.undo();
    byAddr.undo();
  };
  return {
    async verify(pw, stored) {
      try {
        return (
          passwordLength(pw) <= MAX_LENGTH && (await verifyPassword(pw, stored))
        );
      } catch (e) {
        settle();
        throw e;
      }
    },
    async failed(
      user,
      msg,
      unknown = "unknown-name",
      { ev = "auth.password.fail", act } = {},
    ) {
      await audit(
        req,
        ev,
        user ? { ok: false, user, msg, act } : { ok: false, msg: unknown, act },
      );
      if (byName.lock)
        await audit(
          req,
          "auth.password.locked",
          user ? { ok: false, user } : { ok: false, msg: unknown },
        );
      if (byAddr.lock)
        await audit(req, "auth.throttled", { ok: false, msg: "password" });
    },
    ok() {
      ACCOUNT_FAILS.clear(k);
      byAddr.undo();
    },
    void: settle,
  };
}

async function proveOwner(req, res, user, body, act) {
  if (body.credential) {
    if (await passkeyStepUp(user, body)) return "passkey";
    await audit(req, "auth.proof.fail", {
      ok: false,
      user,
      msg: "step-up-failed",
      act,
    });
    json(res, 403, {
      error: "the passkey could not be verified",
      code: "passkey",
    });
    return null;
  }
  if (!passwordWayIn(user)) {
    json(res, 403, {
      error: "confirm with your passkey first",
      code: "passkey-required",
    });
    return null;
  }
  const current = typeof body.current === "string" ? body.current : "";
  const wrongCurrent = () => {
    json(res, 403, {
      error: "your current password is not right",
      code: "current-wrong",
    });
    return null;
  };
  if (!current) {
    json(res, 403, {
      error: "enter your current password",
      code: "current-required",
    });
    return null;
  }
  const check = passwordAttempt(req, res, acctKey(user));
  if (!check) return null;
  const rec = user.pw;
  if (!(await check.verify(current, rec.h))) {
    await check.failed(user, "bad-current", undefined, {
      ev: "auth.proof.fail",
      act,
    });
    return wrongCurrent();
  }
  if (user.pw !== rec) {
    check.void();
    return wrongCurrent();
  }
  check.ok();
  return "password";
}

if (PASSWORD_LOGIN) warmUp();

async function removeEmail(req, res, user, body) {
  if (!user.email) return json(res, 200, { ok: true, email: null });
  const proof = await proveOwner(req, res, user, body, "email-remove");
  if (!proof) return;
  if (readSession(req) !== user)
    return json(res, 401, { error: "not signed in" });
  delete user.email;
  await saveDb();
  await audit(req, "auth.email.remove", { user, msg: proof });
  json(res, 200, { ok: true, email: null });
}

const passwordRoutes = {
  "POST /api/login/password": async (req, res) => {
    const body = await readBody(req);
    const target = loginTarget(body);
    const pw = typeof body.password === "string" ? body.password : "";
    if (!target || !pw)
      return json(res, 400, {
        error: "name and password required",
        code: "missing",
      });
    const check = passwordAttempt(req, res, target.key);
    if (!check) return;
    const { user } = target;
    const rec = user?.pw;
    if (!(await check.verify(pw, rec?.h))) {
      await check.failed(
        user,
        "bad-password",
        target.email ? "unknown-email" : "unknown-name",
      );
      return json(res, 401, WRONG);
    }
    const still = () =>
      hasPassword(user) && user.pw === rec && target.resolve() === user;
    if (!still()) {
      check.void();
      return json(res, 401, WRONG);
    }
    if (user.disabled) {
      check.void();
      await audit(req, "auth.password.fail", {
        ok: false,
        user,
        msg: "account-disabled",
      });
      return json(res, 403, {
        error: "this account has been disabled",
        code: "disabled",
      });
    }
    check.ok();
    if (needsRehash(rec.h)) {
      try {
        const h = await hashPassword(pw);
        if (still()) {
          rec.h = h;
          await saveDb();
        }
      } catch (e) {
        if (!(e instanceof BusyError)) throw e;
      }
      if (!still()) return json(res, 401, WRONG);
    }
    await audit(req, "auth.password.ok", { user });
    json(
      res,
      200,
      { user: publicUser(user) },
      { "Set-Cookie": sessionCookie(user) },
    );
  },
  "POST /api/register/password": async (req, res) => {
    const body = await readBody(req);
    const name = text(body.name).trim().slice(0, 40);
    if (!name)
      return json(res, 400, { error: "name required", code: "missing" });
    const code = text(body.code).trim().toUpperCase();
    const invite = () =>
      db.invites.find((i) => i.code === code && !i.usedBy && !i.revoked);
    if (INVITE_ONLY && addressPaused(req, res, "signup")) return;
    if (INVITE_ONLY && !invite()) {
      await audit(req, "auth.register.denied", {
        ok: false,
        name,
        msg: "invite-rejected",
      });
      await strikeAddress(req, "signup");
      return json(res, 403, {
        error: "a valid invite code is required",
        code: "invite",
      });
    }
    const problem = passwordProblem(body.password, name);
    if (problem) return policyError(res, problem);
    const taken = () =>
      json(res, 409, {
        error: "another profile already signs in with this name",
        code: "name-taken",
      });
    if (nameTaken(name)) return taken();
    const hasEmail = typeof body.email === "string" && body.email.trim() !== "";
    const email = hasEmail ? normalizeEmail(body.email) : null;
    if (hasEmail && !email) return json(res, 400, EMAIL_ERRORS.invalid);
    const emailRefused = async () => {
      await strikeAddress(req, "email");
      await audit(req, "auth.register.fail", {
        ok: false,
        name,
        msg: "email-taken",
      });
      return json(res, 409, EMAIL_ERRORS.taken);
    };
    if (email && addressPaused(req, res, "email")) return;
    const h = await hashPassword(body.password);
    let inv = null;
    if (INVITE_ONLY) {
      inv = invite();
      if (!inv) {
        await audit(req, "auth.register.fail", {
          ok: false,
          name,
          msg: "invite-invalid",
        });
        return json(res, 403, {
          error: "invite code is no longer valid — ask for a new one",
          code: "invite",
        });
      }
    }
    if (nameTaken(name)) return taken();
    if (email && emailTaken(email)) return await emailRefused();
    const created = new Date().toISOString();
    const user = {
      id: crypto.randomBytes(12).toString("base64url"),
      name,
      created,
      pw: { h, set: created },
      ...(email ? { email } : {}),
    };
    if (inv) {
      user.invitedBy = inv.code;
      inv.usedBy = user.id;
      inv.usedAt = created;
    }
    db.users.push(user);
    await saveDb();
    await audit(req, "auth.register.ok", {
      user,
      msg: inv ? inv.code + " · password" : "password",
    });
    json(
      res,
      200,
      { user: publicUser(user) },
      { "Set-Cookie": sessionCookie(user) },
    );
  },
  "GET /api/account/password": async (req, res) => {
    const user = readSession(req);
    if (!user) return json(res, 401, { error: "not signed in" });
    json(res, 200, {
      set: hasPassword(user),
      setAt: user.pw?.set || null,
      passkeys: passkeyCount(user),
      name: user.name,
      nameTaken: nameTaken(user.name, user.id),
      email: user.email || null,
    });
  },
  "POST /api/account/password": async (req, res) => {
    const s = sessionOf(req);
    if (!s) return json(res, 401, { error: "not signed in" });
    const { user } = s;
    const body = await readBody(req);
    const problem = passwordProblem(body.next, user.name);
    if (problem) return policyError(res, problem);
    const taken = () =>
      json(res, 409, {
        error: "another profile already signs in with this name",
        code: "name-taken",
      });
    if (nameTaken(user.name, user.id)) return taken();
    const proof = await proveOwner(req, res, user, body, "password");
    if (!proof) return;
    const h = await hashPassword(body.next);
    if (sessionOf(req)?.user !== user)
      return json(res, 401, { error: "not signed in" });
    if (nameTaken(user.name, user.id)) return taken();
    const first = !hasPassword(user);
    setPassword(user, h);
    ACCOUNT_FAILS.clear(acctKey(user));
    await saveDb();
    await audit(req, first ? "auth.password.set" : "auth.password.change", {
      user,
      msg: proof,
    });
    if (s.bearer) return json(res, 200, { ok: true, token: makeSession(user) });
    json(res, 200, { ok: true }, { "Set-Cookie": sessionCookie(user) });
  },
  "DELETE /api/account/password": async (req, res) => {
    const user = readSession(req);
    if (!user) return json(res, 401, { error: "not signed in" });
    const body = await readBody(req);
    const lastWayIn = () =>
      json(res, 409, {
        error: "the password is the only way into this profile",
        code: "last-way-in",
      });
    if (!hasPassword(user)) return json(res, 200, { ok: true });
    if (!passkeyCount(user)) return lastWayIn();
    const proof = await proveOwner(req, res, user, body, "password-remove");
    if (!proof) return;
    if (readSession(req) !== user)
      return json(res, 401, { error: "not signed in" });
    if (proof === "passkey") await saveDb();
    if (!hasPassword(user)) return json(res, 200, { ok: true });
    if (!passkeyCount(user)) return lastWayIn();
    delete user.pw;
    await saveDb();
    await audit(req, "auth.password.remove", { user });
    json(res, 200, { ok: true });
  },
  "POST /api/account/email": async (req, res) => {
    const s = sessionOf(req);
    if (!s) return json(res, 401, { error: "not signed in" });
    const { user } = s;
    const body = await readBody(req);
    if (
      body.email == null ||
      (typeof body.email === "string" && body.email.trim() === "")
    )
      return await removeEmail(req, res, user, body);
    const email = normalizeEmail(body.email);
    if (!email) return json(res, 400, EMAIL_ERRORS.invalid);
    if (email === user.email) return json(res, 200, { ok: true, email });
    const acct = "email|" + acctKey(user);
    const paused = () => {
      const wait = ADDR_FAILS.retryAfter(acct);
      if (wait) tooMany(res, wait);
      return wait > 0 || addressPaused(req, res, "email");
    };
    if (paused()) return;
    const proof = await proveOwner(req, res, user, body, "email");
    if (!proof) return;
    if (sessionOf(req)?.user !== user)
      return json(res, 401, { error: "not signed in" });
    if (paused()) return;
    if (emailTaken(email, user.id)) {
      if (proof === "passkey") await saveDb();
      await strikeAddress(req, "email");
      ADDR_FAILS.fail(acct);
      await audit(req, "auth.email.fail", {
        ok: false,
        user,
        msg: "email-taken",
      });
      return json(res, 409, EMAIL_ERRORS.taken);
    }
    const first = !user.email;
    user.email = email;
    await saveDb();
    await audit(req, first ? "auth.email.set" : "auth.email.change", {
      user,
      msg: proof + " · " + maskEmail(email),
    });
    json(res, 200, { ok: true, email });
  },
  "DELETE /api/account/email": async (req, res) => {
    const user = readSession(req);
    if (!user) return json(res, 401, { error: "not signed in" });
    await removeEmail(req, res, user, await readBody(req));
  },
  "POST /api/admin/user/password-reset": async (req, res) => {
    const admin = await requireAdmin(req, res);
    if (!admin) return;
    const body = await readBody(req);
    const u = db.users.find((x) => x.id === body.id);
    if (!u) return json(res, 404, { error: "no such user" });
    if (isAdmin(u))
      return json(res, 400, {
        error: "an admin sets their own password in Settings",
      });
    if (nameTaken(u.name, u.id))
      return json(res, 409, {
        error: "another profile already signs in with this name",
        code: "name-taken",
      });
    const code = makeResetCode();
    delete u.pw;
    u.pwReset = {
      h: hashResetCode(code),
      exp: Date.now() + RESET_TTL_MS,
      by: admin.id,
    };
    u.sv = sessionVersion(u) + 1;
    for (const [k, v] of pairings) if (v.uid === u.id) pairings.delete(k);
    dropDeviceLinks(db, u.id);
    presence.delete(u.id);
    await saveDb();
    await audit(req, "admin.password.reset", { user: admin, target: u });
    json(res, 200, { ok: true, name: u.name, code, expires: u.pwReset.exp });
  },
  "POST /api/login/password-reset": async (req, res) => {
    const body = await readBody(req);
    const k = nameKey(
      text(body.identifier ?? body.name ?? body.email).slice(0, 300),
    );
    const code = text(body.code).slice(0, 64);
    if (!k || !code)
      return json(res, 400, {
        error: "name and code required",
        code: "missing",
      });
    if (addressPaused(req, res, "password")) return;
    const find = () =>
      db.users.find(
        (u) =>
          u.pwReset &&
          (nameKey(u.name) === k || u.email === k) &&
          resetCodeMatches(code, u.pwReset),
      ) || null;
    const user = find();
    const invalid = () =>
      json(res, 400, {
        error: "that reset code is wrong or has expired",
        code: "reset-invalid",
      });
    const taken = () =>
      json(res, 409, {
        error: "another profile already signs in with this name",
        code: "name-taken",
      });
    if (!user) {
      await strikeAddress(req, "password");
      await audit(req, "auth.password.reset", {
        ok: false,
        msg: "reset-invalid",
      });
      return invalid();
    }
    if (user.disabled) {
      await audit(req, "auth.password.reset", {
        ok: false,
        user,
        msg: "account-disabled",
      });
      return json(res, 403, {
        error: "this account has been disabled",
        code: "disabled",
      });
    }
    const problem = passwordProblem(body.next, user.name);
    if (problem) return policyError(res, problem);
    if (nameTaken(user.name, user.id)) return taken();
    const h = await hashPassword(body.next);
    if (find() !== user) return invalid();
    if (nameTaken(user.name, user.id)) return taken();
    setPassword(user, h);
    ACCOUNT_FAILS.clear(acctKey(user));
    await saveDb();
    await audit(req, "auth.password.reset", { user });
    json(
      res,
      200,
      { user: publicUser(user) },
      { "Set-Cookie": sessionCookie(user) },
    );
  },
};

const passkeyState = (u) => {
  const passkeys = listPasskeys(db, u.id);
  return {
    passkeys,
    password: passwordWayIn(u),
    lastWayIn: passkeys.length + (passwordWayIn(u) ? 1 : 0) <= 1,
  };
};
const LIMIT = {
  error: `a profile can have at most ${MAX_PASSKEYS} passkeys`,
  code: "passkey-limit",
};
const LINK_INVALID = {
  error: "that code is wrong, used or expired",
  code: "link-invalid",
};
const notSignedIn = (res) => json(res, 401, { error: "not signed in" });

const moreOptions = (user) =>
  generateRegistrationOptions({
    rpName: RP_NAME,
    rpID: RP_ID,
    userID: Buffer.from(user.id),
    userName: user.name,
    userDisplayName: user.name,
    attestationType: "none",
    authenticatorSelection: {
      residentKey: "required",
      userVerification: "preferred",
    },
    excludeCredentials: db.creds
      .filter((c) => c.userId === user.id)
      .map((c) => ({ id: c.id, transports: c.transports || [] })),
  });

async function newPasskey(req, res, c, body, ev, user) {
  let verification;
  try {
    verification = await verifyRegistrationResponse({
      response: body.credential,
      expectedChallenge: c.challenge,
      expectedOrigin: ORIGIN,
      expectedRPID: RP_ID,
      requireUserVerification: false,
    });
  } catch (e) {
    await audit(req, ev, { ok: false, user, msg: "verify-error" });
    json(res, 400, { error: verifyError(e, { rpId: RP_ID, origin: ORIGIN }) });
    return null;
  }
  if (!verification.verified) {
    await audit(req, ev, { ok: false, user, msg: "not-verified" });
    json(res, 400, { error: "not verified" });
    return null;
  }
  const { credential } = verification.registrationInfo;
  return {
    id: credential.id,
    publicKey: Buffer.from(credential.publicKey).toString("base64url"),
    counter: credential.counter || 0,
    transports: body.credential?.response?.transports,
    name: body.name,
  };
}

const passkeyRoutes = {
  "GET /api/account/passkeys": async (req, res) => {
    const user = readSession(req);
    if (!user) return notSignedIn(res);
    json(res, 200, passkeyState(user));
  },
  "POST /api/account/passkeys/options": async (req, res) => {
    const user = readSession(req);
    if (!user) return notSignedIn(res);
    const body = await readBody(req);
    if (passkeyCount(user) >= MAX_PASSKEYS) return json(res, 409, LIMIT);
    const proof = await proveOwner(req, res, user, body, "passkey-add");
    if (!proof) return;
    if (readSession(req) !== user) return notSignedIn(res);
    if (proof === "passkey") await saveDb();
    const options = await moreOptions(user);
    const cid = putChallenge({
      challenge: options.challenge,
      uid: user.id,
      kind: "add",
      sv: sessionVersion(user),
      proof,
    });
    json(res, 200, { cid, options });
  },
  "POST /api/account/passkeys/verify": async (req, res) => {
    const user = readSession(req);
    if (!user) return notSignedIn(res);
    const body = await readBody(req);
    const c = takeChallenge(text(body.cid));
    if (!c || c.kind !== "add" || c.uid !== user.id) {
      await audit(req, "auth.passkey.fail", {
        ok: false,
        user,
        msg: "challenge-expired",
      });
      return json(res, 400, { error: "challenge expired — try again" });
    }
    const cred = await newPasskey(req, res, c, body, "auth.passkey.fail", user);
    if (!cred) return;
    if (readSession(req) !== user || sessionVersion(user) !== c.sv)
      return notSignedIn(res);
    const added = addPasskeyRecord(db, user.id, cred);
    if (added.error) {
      await audit(req, "auth.passkey.fail", {
        ok: false,
        user,
        msg: added.code,
      });
      return json(res, 409, { error: added.error, code: added.code });
    }
    await saveDb();
    await audit(req, "auth.passkey.add", { user, msg: c.proof });
    json(res, 200, { ok: true, ...passkeyState(user) });
  },
  "POST /api/account/passkeys/rename": async (req, res) => {
    const user = readSession(req);
    if (!user) return notSignedIn(res);
    const body = await readBody(req);
    const r = renamePasskeyRecord(db, user.id, text(body.id), body.name);
    if (r.error) return json(res, 404, { error: r.error, code: r.code });
    await saveDb();
    json(res, 200, { ok: true, ...passkeyState(user) });
  },
  "DELETE /api/account/passkeys": async (req, res) => {
    const user = readSession(req);
    if (!user) return notSignedIn(res);
    const id = new URL(req.url, "http://x").searchParams.get("id") || "";
    const body = await readBody(req);
    const refuse = (r) =>
      json(res, r.code === "last-way-in" ? 409 : 404, {
        error: r.error,
        code: r.code,
      });
    const refused = passkeyRemovalRefused(
      db,
      user.id,
      id,
      passwordWayIn(user) ? 1 : 0,
    );
    if (refused) return refuse(refused);
    const proof = await proveOwner(req, res, user, body, "passkey-remove");
    if (!proof) return;
    if (readSession(req) !== user) return notSignedIn(res);
    if (proof === "passkey") await saveDb();
    const r = removePasskeyRecord(db, user.id, id, passwordWayIn(user) ? 1 : 0);
    if (r.error) return refuse(r);
    dropDeviceLinks(db, user.id);
    await saveDb();
    await audit(req, "auth.passkey.remove", { user, msg: r.row.name || null });
    json(res, 200, { ok: true, ...passkeyState(user) });
  },
  "POST /api/account/device-link": async (req, res) => {
    const user = readSession(req);
    if (!user) return notSignedIn(res);
    const body = await readBody(req);
    if (passkeyCount(user) >= MAX_PASSKEYS) return json(res, 409, LIMIT);
    const proof = await proveOwner(req, res, user, body, "device-link");
    if (!proof) return;
    if (readSession(req) !== user) return notSignedIn(res);
    const { code, link } = createDeviceLink(db, user.id);
    await saveDb();
    await audit(req, "auth.link.create", { user, msg: proof });
    json(res, 200, { code, expires: link.exp });
  },
  "POST /api/device-link/options": async (req, res) => {
    const body = await readBody(req);
    if (addressPaused(req, res, "link")) return;
    const link = findDeviceLink(db, text(body.code));
    if (!link) {
      await strikeAddress(req, "link");
      await audit(req, "auth.link.fail", { ok: false, msg: "link-invalid" });
      return json(res, 400, LINK_INVALID);
    }
    const user = db.users.find((u) => u.id === link.userId);
    if (!user || user.disabled) {
      await audit(req, "auth.link.fail", {
        ok: false,
        uid: link.userId,
        msg: "user-unavailable",
      });
      return json(res, 400, LINK_INVALID);
    }
    if (passkeyCount(user) >= MAX_PASSKEYS) return json(res, 409, LIMIT);
    const options = await moreOptions(user);
    const cid = putChallenge({
      challenge: options.challenge,
      uid: user.id,
      kind: "link",
      lh: link.h,
    });
    json(res, 200, { cid, options, id: user.id, name: user.name });
  },
  "POST /api/device-link/verify": async (req, res) => {
    const body = await readBody(req);
    if (addressPaused(req, res, "link")) return;
    const code = text(body.code);
    const c = takeChallenge(text(body.cid));
    const link = findDeviceLink(db, code);
    if (!link) {
      await strikeAddress(req, "link");
      await audit(req, "auth.link.fail", { ok: false, msg: "link-invalid" });
      return json(res, 400, LINK_INVALID);
    }
    if (!c || c.kind !== "link" || c.lh !== link.h || c.uid !== link.userId) {
      await audit(req, "auth.link.fail", {
        ok: false,
        uid: link.userId,
        msg: "challenge-expired",
      });
      return json(res, 400, { error: "challenge expired — try again" });
    }
    const owner = db.users.find((u) => u.id === link.userId);
    const cred = await newPasskey(
      req,
      res,
      c,
      body,
      "auth.link.fail",
      owner || { id: link.userId },
    );
    if (!cred) return;
    const user = db.users.find((u) => u.id === link.userId);
    if (findDeviceLink(db, code) !== link || !user || user.disabled) {
      await audit(req, "auth.link.fail", {
        ok: false,
        uid: link.userId,
        msg: "link-invalid",
      });
      return json(res, 400, LINK_INVALID);
    }
    const added = addPasskeyRecord(db, user.id, cred);
    if (added.error) {
      await audit(req, "auth.link.fail", { ok: false, user, msg: added.code });
      return json(res, 409, { error: added.error, code: added.code });
    }
    added.row.lastUsed = added.row.created;
    burnDeviceLink(db, link);
    await saveDb();
    await audit(req, "auth.link.ok", { user, msg: added.row.name || null });
    json(
      res,
      200,
      { user: publicUser(user) },
      { "Set-Cookie": sessionCookie(user) },
    );
  },
};

const routes = {
  "GET /api/health": async (req, res) =>
    json(res, 200, { ok: true, users: db.users.length }),

  "GET /api/config": async (req, res) => {
    json(res, 200, {
      invite_only: INVITE_ONLY,
      allow_guest: ALLOW_GUEST,
      ...(PASSWORD_LOGIN ? { password_login: true } : {}),
      ...(DEFAULT_LANG ? { default_lang: DEFAULT_LANG } : {}),
    });
  },

  "GET /api/me": async (req, res) => {
    const s = sessionOf(req);
    if (!s) return json(res, 401, { error: "not signed in" });
    const { user } = s;
    const renew =
      s.bearer && s.exp - Date.now() < (SESSION_DAYS * 86400000) / 2;
    json(res, 200, {
      user: { id: user.id, name: user.name, admin: isAdmin(user) },
      ...(renew ? { token: makeSession(user) } : {}),
    });
  },

  "POST /api/register/options": async (req, res) => {
    const body = await readBody(req);
    const name = text(body.name).trim().slice(0, 40);
    if (!name) return json(res, 400, { error: "name required" });
    const code = text(body.code).trim().toUpperCase();
    if (
      INVITE_ONLY &&
      !db.invites.some((i) => i.code === code && !i.usedBy && !i.revoked)
    ) {
      await audit(req, "auth.register.denied", {
        ok: false,
        name,
        msg: "invite-rejected",
      });
      return json(res, 403, { error: "a valid invite code is required" });
    }
    const uid = crypto.randomBytes(12).toString("base64url");
    const options = await generateRegistrationOptions({
      rpName: RP_NAME,
      rpID: RP_ID,
      userID: Buffer.from(uid),
      userName: name,
      userDisplayName: name,
      attestationType: "none",
      authenticatorSelection: {
        residentKey: "required",
        userVerification: "preferred",
      },
      excludeCredentials: [],
    });
    const cid = putChallenge({
      kind: "register",
      challenge: options.challenge,
      name,
      uid,
      code,
    });
    json(res, 200, { cid, options });
  },

  "POST /api/register/verify": async (req, res) => {
    const body = await readBody(req);
    const c = takeChallenge(body.cid);
    if (!c || c.kind !== "register" || !c.uid) {
      await audit(req, "auth.register.fail", {
        ok: false,
        msg: "challenge-expired",
      });
      return json(res, 400, { error: "challenge expired — try again" });
    }
    let verification;
    try {
      verification = await verifyRegistrationResponse({
        response: body.credential,
        expectedChallenge: c.challenge,
        expectedOrigin: ORIGIN,
        expectedRPID: RP_ID,
        requireUserVerification: false,
      });
    } catch (e) {
      await audit(req, "auth.register.fail", {
        ok: false,
        name: c.name,
        msg: "verify-error",
      });
      return json(res, 400, {
        error: verifyError(e, { rpId: RP_ID, origin: ORIGIN }),
      });
    }
    if (!verification.verified) {
      await audit(req, "auth.register.fail", {
        ok: false,
        name: c.name,
        msg: "not-verified",
      });
      return json(res, 400, { error: "not verified" });
    }
    const { credential } = verification.registrationInfo;
    if (db.creds.find((x) => x.id === credential.id)) {
      await audit(req, "auth.register.fail", {
        ok: false,
        name: c.name,
        msg: "credential-exists",
      });
      return json(res, 409, { error: "credential already registered" });
    }
    let invite = null;
    if (INVITE_ONLY) {
      invite = db.invites.find(
        (i) => i.code === c.code && !i.usedBy && !i.revoked,
      );
      if (!invite) {
        await audit(req, "auth.register.fail", {
          ok: false,
          name: c.name,
          msg: "invite-invalid",
        });
        return json(res, 403, {
          error: "invite code is no longer valid — ask for a new one",
        });
      }
    }
    const user = { id: c.uid, name: c.name, created: new Date().toISOString() };
    if (invite) {
      user.invitedBy = invite.code;
      invite.usedBy = user.id;
      invite.usedAt = user.created;
    }
    db.users.push(user);
    db.creds.push({
      id: credential.id,
      userId: user.id,
      publicKey: Buffer.from(credential.publicKey).toString("base64url"),
      counter: credential.counter || 0,
      transports: body.credential?.response?.transports || [],
      created: user.created,
      lastUsed: user.created,
    });
    await saveDb();
    await audit(req, "auth.register.ok", {
      user,
      msg: invite ? invite.code : null,
    });
    json(
      res,
      200,
      { user: { id: user.id, name: user.name, admin: isAdmin(user) } },
      { "Set-Cookie": sessionCookie(user) },
    );
  },

  "POST /api/login/options": async (req, res) => {
    const options = await generateAuthenticationOptions({
      rpID: RP_ID,
      userVerification: "preferred",
      allowCredentials: [],
    });
    const cid = putChallenge({ kind: "login", challenge: options.challenge });
    json(res, 200, { cid, options });
  },

  "POST /api/login/verify": async (req, res) => {
    const body = await readBody(req);
    const c = takeChallenge(body.cid);
    if (c?.kind !== "login") {
      await audit(req, "auth.login.fail", {
        ok: false,
        msg: "challenge-expired",
      });
      return json(res, 400, { error: "challenge expired — try again" });
    }
    const cred = db.creds.find((x) => x.id === body.credential?.id);
    if (!cred) {
      await audit(req, "auth.login.fail", {
        ok: false,
        msg: "unknown-credential",
      });
      return json(res, 404, {
        error: "unknown passkey — create a profile first",
      });
    }
    let verification;
    try {
      verification = await verifyAuthenticationResponse({
        response: body.credential,
        expectedChallenge: c.challenge,
        expectedOrigin: ORIGIN,
        expectedRPID: RP_ID,
        requireUserVerification: false,
        credential: {
          id: cred.id,
          publicKey: b64uToBuf(cred.publicKey),
          counter: cred.counter,
          transports: cred.transports,
        },
      });
    } catch (e) {
      await audit(req, "auth.login.fail", {
        ok: false,
        user: db.users.find((u) => u.id === cred.userId),
        uid: cred.userId,
        msg: "verify-error",
      });
      return json(res, 400, {
        error: verifyError(e, { rpId: RP_ID, origin: ORIGIN }),
      });
    }
    if (!verification.verified) {
      await audit(req, "auth.login.fail", {
        ok: false,
        user: db.users.find((u) => u.id === cred.userId),
        uid: cred.userId,
        msg: "not-verified",
      });
      return json(res, 400, { error: "not verified" });
    }
    cred.counter = verification.authenticationInfo.newCounter;
    cred.lastUsed = new Date().toISOString();
    await saveDb();
    const user = db.users.find((u) => u.id === cred.userId);
    if (!user) {
      await audit(req, "auth.login.fail", {
        ok: false,
        uid: cred.userId,
        msg: "user-missing",
      });
      return json(res, 500, { error: "user missing" });
    }
    if (user.disabled) {
      await audit(req, "auth.login.fail", {
        ok: false,
        user,
        msg: "account-disabled",
      });
      return json(res, 403, { error: "this account has been disabled" });
    }
    await audit(req, "auth.login.ok", { user });
    json(
      res,
      200,
      { user: { id: user.id, name: user.name, admin: isAdmin(user) } },
      { "Set-Cookie": sessionCookie(user) },
    );
  },

  "POST /api/logout": async (req, res) => {
    const user = readSession(req);
    if (user) await audit(req, "auth.logout", { user });
    json(res, 200, { ok: true }, { "Set-Cookie": clearCookie });
  },

  "POST /api/logout/all": async (req, res) => {
    const user = readSession(req);
    if (!user) return json(res, 401, { error: "not signed in" });
    user.sv = sessionVersion(user) + 1;
    for (const [k, v] of pairings) if (v.uid === user.id) pairings.delete(k);
    dropDeviceLinks(db, user.id);
    await saveDb();
    await audit(req, "auth.logout.all", { user });
    json(res, 200, { ok: true }, { "Set-Cookie": clearCookie });
  },

  "POST /api/pair/create": async (req, res) => {
    const user = readSession(req);
    if (!user) return json(res, 401, { error: "not signed in" });
    const code = makePairCode();
    pairings.set(code, { uid: user.id, exp: Date.now() + 5 * 60000 });
    await audit(req, "auth.pair.create", { user });
    json(res, 200, { code });
  },

  "POST /api/pair/redeem": async (req, res) => {
    const body = await readBody(req);
    const code = text(body.code).trim().toUpperCase();
    const p = pairings.get(code);
    if (p) pairings.delete(code);
    if (!p || p.exp < Date.now()) {
      await audit(req, "auth.pair.fail", { ok: false, msg: "code-invalid" });
      return json(res, 400, { error: "invalid or expired code" });
    }
    const user = db.users.find((u) => u.id === p.uid);
    if (!user || user.disabled) {
      await audit(req, "auth.pair.fail", {
        ok: false,
        uid: p.uid,
        msg: "user-unavailable",
      });
      return json(res, 400, { error: "invalid or expired code" });
    }
    await audit(req, "auth.pair.ok", { user });
    json(res, 200, {
      token: makeSession(user),
      user: { id: user.id, name: user.name, admin: isAdmin(user) },
    });
  },

  ...(PASSWORD_LOGIN ? passwordRoutes : {}),
  ...passkeyRoutes,

  "GET /api/data": async (req, res) => {
    const user = readSession(req);
    if (!user) return json(res, 401, { error: "not signed in" });
    const state = await readState(user.id);
    await notePull(user);
    json(res, 200, { state, rev: state?._rev || 0 });
  },
  "GET /api/data/rev": async (req, res) => {
    const user = readSession(req);
    if (!user) return json(res, 401, { error: "not signed in" });
    json(res, 200, { rev: (await readStateCached(user.id))?._rev || 0 });
  },

  "PUT /api/data": async (req, res) => {
    const user = readSession(req);
    if (!user) return json(res, 401, { error: "not signed in" });
    const body = await readBody(req);
    if (!body.state || typeof body.state !== "object")
      return json(res, 400, { error: "state required" });
    const list = (v) => v == null || Array.isArray(v);
    if (
      !Array.isArray(body.state) &&
      !Object.keys(body.state).some((k) => k !== "_rev" && k !== "_ts")
    )
      return json(res, 400, { error: "state required" });
    if (
      Array.isArray(body.state) ||
      !list(body.state.workouts) ||
      !list(body.state.routines)
    )
      return json(res, 400, { error: "invalid state" });
    for (const k of ["workouts", "routines"])
      if (Array.isArray(body.state[k])) body.state[k] = records(body.state[k]);
    const cur = await readState(user.id);
    const curRev = cur?._rev || 0;
    if (body.baseRev != null && body.baseRev !== curRev)
      return json(res, 409, { error: "conflict", rev: curRev, state: cur });
    delete body.state.active;
    const storedReset = Number(cur?.resetAt) || 0;
    if (storedReset > (Number(body.state.resetAt) || 0)) {
      body.state.resetAt = cur.resetAt;
      if (cur.resetIds && typeof cur.resetIds === "object")
        body.state.resetIds = cur.resetIds;
      else delete body.state.resetIds;
    }
    body.state._rev = curRev + 1;
    await StateModel.updateOne(
      { uid: user.id },
      { data: body.state },
      { upsert: true },
    );
    json(res, 200, {
      ok: true,
      ts: body.state._ts || null,
      rev: body.state._rev,
    });
  },

  "GET /api/push/public-key": async (req, res) =>
    json(res, 200, { key: vapid.publicKey }),

  "POST /api/push/subscribe": async (req, res) => {
    const user = readSession(req);
    if (!user) return json(res, 401, { error: "not signed in" });
    const body = await readBody(req);
    const sub = body.subscription;
    if (!sub?.endpoint || !sub?.keys?.p256dh || !sub?.keys?.auth)
      return json(res, 400, { error: "invalid subscription" });
    const bad = pushEndpointError(sub.endpoint);
    if (bad) return json(res, 400, { error: bad });
    const keys = {
      p256dh: String(sub.keys.p256dh),
      auth: String(sub.keys.auth),
    };
    const deviceId = deviceIdOf(body.deviceId);
    const prev = db.subs.find((s) => s.endpoint === sub.endpoint);
    db.subs = db.subs.filter((s) => s.endpoint !== sub.endpoint);
    const mine = db.subs.filter((s) => s.userId === user.id);
    if (mine.length >= MAX_SUBS_PER_USER) {
      const drop = new Set(
        mine
          .slice(0, mine.length - MAX_SUBS_PER_USER + 1)
          .map((s) => s.endpoint),
      );
      db.subs = db.subs.filter((s) => !drop.has(s.endpoint));
    }
    db.subs.push({
      userId: user.id,
      endpoint: sub.endpoint,
      keys,
      ...(deviceId ? { deviceId } : {}),
      created: prev?.created || new Date().toISOString(),
    });
    await saveDb();
    json(res, 200, { ok: true });
  },

  "GET /api/push/status": async (req, res) => {
    const user = readSession(req);
    if (!user) return json(res, 401, { error: "not signed in" });
    const endpoint =
      new URL(req.url, "http://x").searchParams.get("endpoint") || "";
    json(res, 200, {
      subscribed: db.subs.some(
        (s) => s.userId === user.id && s.endpoint === endpoint,
      ),
    });
  },

  "POST /api/push/unsubscribe": async (req, res) => {
    const user = readSession(req);
    if (!user) return json(res, 401, { error: "not signed in" });
    const body = await readBody(req);
    db.subs = db.subs.filter(
      (s) => !(s.userId === user.id && s.endpoint === body.endpoint),
    );
    await saveDb();
    json(res, 200, { ok: true });
  },

  "POST /api/push/test": async (req, res) => {
    const user = readSession(req);
    if (!user) return json(res, 401, { error: "not signed in" });
    await sendPush(user.id, testPush((await readStateCached(user.id))?.lang));
    json(res, 200, { ok: true });
  },

  "POST /api/push/rest-timer": async (req, res) => {
    const user = readSession(req);
    if (!user) return json(res, 401, { error: "not signed in" });
    const body = await readBody(req);
    const raw = body.seconds;
    const n =
      typeof raw === "number" || typeof raw === "string" ? Number(raw) : NaN;
    if (!(n >= 1)) return json(res, 400, { error: "seconds required" });
    const sec = Math.min(3600, Math.round(n));
    scheduleRestTimer(
      user.id,
      deviceIdOf(body.deviceId),
      sec,
      (await readStateCached(user.id))?.lang,
    );
    json(res, 200, { ok: true });
  },

  "POST /api/push/rest-timer/cancel": async (req, res) => {
    const user = readSession(req);
    if (!user) return json(res, 401, { error: "not signed in" });
    const body = await readBody(req);
    cancelRestTimer(user.id, deviceIdOf(body.deviceId));
    json(res, 200, { ok: true });
  },

  "POST /api/activity": async (req, res) => {
    const user = readSession(req);
    if (!user) return json(res, 401, { error: "not signed in" });
    const body = await readBody(req);
    if (body.active) {
      presence.set(user.id, {
        name: text(body.name).slice(0, 60),
        exIdx: +body.exIdx || 0,
        exTotal: +body.exTotal || 0,
        setsDone: +body.setsDone || 0,
        setsTotal: +body.setsTotal || 0,
        startedAt: +body.startedAt || Date.now(),
        updatedAt: Date.now(),
      });
    } else presence.delete(user.id);
    json(res, 200, { ok: true });
  },

  "GET /api/admin/users": async (req, res) => {
    if (!(await requireAdmin(req, res))) return;
    const users = await Promise.all(
      db.users.map(async (u) => {
        const S = (await readState(u.id)) || {};
        const workouts = records(S.workouts);
        const last = workouts[workouts.length - 1];
        return {
          id: u.id,
          name: u.name,
          created: u.created || null,
          disabled: !!u.disabled,
          admin: isAdmin(u),
          invitedBy: u.invitedBy || null,
          workouts: workouts.length,
          lastWorkout: last ? last.d : null,
          lastSync: lastSyncOf(u, S),
          hasPush: db.subs.some((s) => s.userId === u.id),
          live: livePresence(u.id),
          ...(PASSWORD_LOGIN
            ? { password: hasPassword(u), email: u.email || null }
            : {}),
        };
      }),
    );
    json(res, 200, {
      users,
      invite_only: INVITE_ONLY,
      ...(PASSWORD_LOGIN ? { password_login: true } : {}),
      now: Date.now(),
    });
  },

  "GET /api/admin/user": async (req, res) => {
    if (!(await requireAdmin(req, res))) return;
    const id = new URL(req.url, "http://x").searchParams.get("id");
    const u = db.users.find((x) => x.id === id);
    if (!u) return json(res, 404, { error: "no such user" });
    const S = (await readState(u.id)) || {};
    json(res, 200, {
      user: {
        id: u.id,
        name: u.name,
        created: u.created || null,
        disabled: !!u.disabled,
        admin: isAdmin(u),
        invitedBy: u.invitedBy || null,
        ...(PASSWORD_LOGIN
          ? {
              password: hasPassword(u),
              email: u.email || null,
              resetUntil: u.pwReset?.exp > Date.now() ? u.pwReset.exp : null,
            }
          : {}),
      },
      unit: S.unit || "kg",
      lastSync: lastSyncOf(u, S),
      routines: records(S.routines).map((r) => ({
        id: r.id,
        name: r.name,
        emoji: r.emoji,
        count: records(r.ex).length,
      })),
      bodyweight: records(S.bodyweight),
      workouts: records(S.workouts)
        .reverse()
        .map(({ media, ...w }) => w),
    });
  },

  "POST /api/admin/user/disable": async (req, res) => {
    const admin = await requireAdmin(req, res);
    if (!admin) return;
    const body = await readBody(req);
    const u = db.users.find((x) => x.id === body.id);
    if (!u) return json(res, 404, { error: "no such user" });
    if (isAdmin(u)) return json(res, 400, { error: "cannot disable an admin" });
    u.disabled = !!body.disabled;
    if (u.disabled) presence.delete(u.id);
    if (u.disabled) dropDeviceLinks(db, u.id);
    await saveDb();
    await audit(req, u.disabled ? "admin.user.disable" : "admin.user.enable", {
      user: admin,
      target: u,
    });
    json(res, 200, { ok: true, id: u.id, disabled: u.disabled });
  },

  "POST /api/admin/user/delete": async (req, res) => {
    const admin = await requireAdmin(req, res);
    if (!admin) return;
    const body = await readBody(req);
    const u = db.users.find((x) => x.id === body.id);
    if (!u) return json(res, 404, { error: "no such user" });
    if (u.id === admin.id)
      return json(res, 400, { error: "you cannot delete your own account" });
    if (isAdmin(u) && db.users.filter(isAdmin).length <= 1)
      return json(res, 400, { error: "cannot delete the last admin" });
    const name = u.name;
    db.users = db.users.filter((x) => x.id !== u.id);
    db.creds = (db.creds || []).filter((c) => c.userId !== u.id);
    db.subs = (db.subs || []).filter((x) => x.userId !== u.id);
    dropDeviceLinks(db, u.id);
    presence.delete(u.id);
    try {
      await StateModel.deleteOne({ uid: u.id });
    } catch {}
    await saveDb();
    await audit(req, "admin.user.delete", { user: admin, msg: name });
    json(res, 200, { ok: true, id: u.id });
  },

  "GET /api/admin/invites": async (req, res) => {
    if (!(await requireAdmin(req, res))) return;
    const invites = db.invites.map((i) => ({
      ...i,
      usedByName: i.usedBy
        ? (db.users.find((u) => u.id === i.usedBy) || {}).name || null
        : null,
    }));
    json(res, 200, { invites, invite_only: INVITE_ONLY });
  },

  "POST /api/admin/invites/new": async (req, res) => {
    const admin = await requireAdmin(req, res);
    if (!admin) return;
    const body = await readBody(req);
    let code;
    do {
      code = crypto.randomBytes(8).toString("hex").toUpperCase();
    } while (db.invites.some((i) => i.code === code));
    const invite = {
      code,
      note: text(body.note).slice(0, 60),
      createdBy: admin.id,
      created: new Date().toISOString(),
    };
    db.invites.push(invite);
    await saveDb();
    await audit(req, "admin.invite.create", { user: admin, msg: code });
    json(res, 200, { invite });
  },

  "POST /api/admin/invites/revoke": async (req, res) => {
    const admin = await requireAdmin(req, res);
    if (!admin) return;
    const body = await readBody(req);
    const inv = db.invites.find(
      (i) => i.code === text(body.code).toUpperCase(),
    );
    if (!inv) return json(res, 404, { error: "no such code" });
    if (inv.usedBy)
      return json(res, 400, { error: "already used — cannot revoke" });
    db.invites = db.invites.filter((i) => i.code !== inv.code);
    await saveDb();
    await audit(req, "admin.invite.revoke", { user: admin, msg: inv.code });
    json(res, 200, { ok: true });
  },

  "GET /api/admin/audit": async (req, res) => {
    if (!(await requireAdmin(req, res))) return;
    const q = new URL(req.url, "http://x").searchParams;
    const limit = Math.max(1, Math.min(200, +q.get("limit") || 100));
    const before = +q.get("before") || Infinity;
    const cat = q.get("cat") || "";
    let rows = (await auditLines()).reverse();
    if (cat === "fail") rows = rows.filter((r) => !r.ok);
    else if (cat) rows = rows.filter((r) => String(r.ev).startsWith(cat + "."));
    const page = rows.filter((r) => r.id < before).slice(0, limit);
    json(res, 200, {
      events: page,
      total: rows.length,
      nextBefore: page.length === limit ? page[page.length - 1].id : null,
      enabled: AUDIT_ON,
      ip_mode: AUDIT_IP,
      retention: { max: AUDIT_MAX, days: AUDIT_DAYS },
      now: Date.now(),
    });
  },

  "POST /api/admin/audit/clear": async (req, res) => {
    const admin = await requireAdmin(req, res);
    if (!admin) return;
    try {
      await AuditModel.deleteMany({});
    } catch {}
    await audit(req, "admin.audit.clear", { user: admin });
    json(res, 200, { ok: true });
  },
};

const BODY_TIMEOUT_MS = Math.max(
  50,
  +(process.env.BODY_TIMEOUT_MS || 300000) || 300000,
);
function bodyDeadline(req) {
  if (req.complete) return;
  const socket = req.socket;
  const timer = setTimeout(() => {
    if (!req.complete) socket.destroy();
  }, BODY_TIMEOUT_MS);
  timer.unref();
  const clear = () => clearTimeout(timer);
  req.once("end", clear);
  req.allowSlowBody = clear;
}

let isConnected = false;

export default async function handler(req, res) {
  if (!isConnected) {
    try {
      await mongoose.connect(process.env.MONGODB_URI, {
        bufferCommands: false,
      });
      isConnected = true;
      console.log("Connecté à MongoDB Atlas");

      const vapidDoc = await DbModel.findOne({ id: "vapid" }).lean();
      if (vapidDoc && vapidDoc.data) {
        vapid = vapidDoc.data;
      } else {
        vapid = webpush.generateVAPIDKeys();
        await DbModel.updateOne(
          { id: "vapid" },
          { data: vapid },
          { upsert: true },
        );
      }
      webpush.setVapidDetails(VAPID_SUBJECT, vapid.publicKey, vapid.privateKey);

      if (AUDIT_ON) {
        await compactAudit();
      }
    } catch (e) {
      console.error("Erreur MongoDB:", e);
      return json(res, 500, { error: "Database connection failed" });
    }
  }

  await loadDb();
  bodyDeadline(req);

  const origin = req.headers.origin;
  if (origin) {
    res.setHeader("Access-Control-Allow-Origin", origin);
    res.setHeader("Vary", "Origin");
  }
  if (req.method === "OPTIONS") {
    res.writeHead(204, {
      "Access-Control-Allow-Methods": "GET,POST,PUT,DELETE,OPTIONS",
      "Access-Control-Allow-Headers": "Content-Type, Authorization",
      "Access-Control-Max-Age": "86400",
    });
    return res.end();
  }

  let url;
  try {
    url = new URL(req.url, "http://x");
  } catch {
    return json(res, 400, { error: "bad request" });
  }
  let key = req.method + " " + url.pathname;
  const routeHandler = routes[key];

  if (!routeHandler) return json(res, 404, { error: "not found" });
  if (!csrfOk(req, key)) {
    return json(res, 403, { error: "cross-origin request refused" });
  }

  if (key in THROTTLED) {
    const addr = limitAddress(req);
    const kind = THROTTLED[key];
    const wait =
      AUTH_BURST.take(addr) ||
      (kind ? ADDR_FAILS.retryAfter(kind + "|" + addr) : 0);
    if (wait) return tooMany(res, wait);
  }

  try {
    await routeHandler(req, res);
  } catch (e) {
    if (e?.clientGone) return;
    if (e instanceof HttpError) {
      if (!res.headersSent) json(res, e.status, { error: e.message });
      return;
    }
    if (e instanceof BusyError) {
      if (!res.headersSent)
        json(
          res,
          503,
          { error: "the server is busy — try again in a moment", code: "busy" },
          { "Retry-After": "2" },
        );
      return;
    }
    console.error(key, e);
    if (!res.headersSent) json(res, 500, { error: "server error" });
  }
}
