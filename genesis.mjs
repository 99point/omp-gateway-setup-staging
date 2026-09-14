#!/usr/bin/env node
// genesis: the client CLI for a Genesis gateway. One file, Node.js 18 or newer,
// no dependencies. It stores the endpoint and personal key the user logs in
// with, drives the reviewed agent-auth-setup.sh installer for every client
// change, and talks to the gateway's bearer-authenticated CLI door
// (/admin/api/cli/*). Nothing privileged lives here: the server decides what a
// key may do from its role.
import { AsyncLocalStorage } from 'node:async_hooks';
import { execFile, spawn } from 'node:child_process';
import crypto from 'node:crypto';
import { once } from 'node:events';
import fs from 'node:fs';
import http from 'node:http';
import os from 'node:os';
import path from 'node:path';
import { emitKeypressEvents } from 'node:readline';
import ttyModule from 'node:tty';
import { fileURLToPath, pathToFileURL } from 'node:url';

// A personal key: the s99dev. prefix and 20-512 URL-safe characters. Anything
// else is refused before it can reach a request, and no key bytes are echoed.
const KEY = /^s99dev\.[A-Za-z0-9_-]{20,512}$/;
const KEY_SHAPE = 'those start with s99dev. followed by 20-512 letters, digits, _ or -';
const ROLES = new Set(['owner', 'admin', 'viewer', 'client']);
const IDENTITY_CLASSES = new Set(['internal', 'external']);
const identityClassOf = value => value === undefined ? 'internal' : IDENTITY_CLASSES.has(value) ? value : null;
const HTTP_TIMEOUT_MS = 30_000;
const LINK_POLL_MS = 2_000;
const LOCAL_BODY_CAP = 16 * 1024;
const ATTEMPT_ID = /^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/;
const LINK_STATUSES = new Set(['starting', 'awaiting-browser', 'exchanging', 'done', 'failed', 'cancelled']);
const LINK_TERMINAL = new Set(['done', 'failed', 'cancelled']);
const PROFILE = /^[a-z0-9][a-z0-9._-]{0,63}$/;
const MODEL_ID = /^[\x21-\x7e]{1,256}$/;
const PROVIDER_LABELS = { anthropic: 'Anthropic', 'openai-codex': 'OpenAI' };
const WINDOWS = ['today', '7d', '30d', 'all'];

// Two environments, each with its own gateway URL and personal key. `prod` is
// the one every install creates; its URL defaults to the canonical Genesis
// gateway but is whatever the person logs into. `staging` is a developer's
// second gateway, gated on prod's identity.
const PROD_ENDPOINT = 'https://genesis.99point.co';
const ENVIRONMENTS = Object.freeze({
  prod: { label: 'Prod', endpoint: PROD_ENDPOINT },
  staging: { label: 'Staging' },
});
function environmentId(value) {
  if (typeof value !== 'string' || !Object.hasOwn(ENVIRONMENTS, value)) throw usage('environment must be prod or staging');
  return value;
}
const environmentLabel = environment => ENVIRONMENTS[environment].label;
// One row per supported client. `providers` are the gateway providers whose
// models the client can use; `binary` is what the installer requires on PATH.
export const CLIENTS = Object.freeze([
  { id: 'omp', label: 'OMP', binary: 'omp', providers: ['anthropic', 'openai-codex'] },
  { id: 'claude-code', label: 'Claude Code', binary: 'claude', providers: ['anthropic'] },
  { id: 'codex', label: 'Codex', binary: 'codex', providers: ['openai-codex'] },
  { id: 'opencode', label: 'OpenCode', binary: 'opencode', providers: ['anthropic', 'openai-codex'] },
  { id: 'pi', label: 'Pi', binary: 'pi', providers: ['anthropic', 'openai-codex'] },
]);

// ── errors ──────────────────────────────────────────────────────────────────
// Exit codes: 0 ok, 1 failure, 2 usage, 130 interrupted. An empty message
// suppresses a duplicate error after acknowledgement, or marks an interrupt.
export class CliError extends Error {
  constructor(message, exitCode = 1) { super(message); this.exitCode = exitCode; }
}
class HttpError extends CliError {
  constructor(status, message) { super(message); this.status = status; }
}
class Interrupt extends CliError {
  constructor() { super('', 130); }
}
const usage = message => new CliError(message, 2);
const record = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const hostOf = endpoint => endpoint.replace(/^[a-z]+:\/\//, '');

// ── key hygiene ─────────────────────────────────────────────────────────────
// Every key this process has held is registered here; everything the CLI
// prints passes through redact(), which replaces those bytes with <key>.
const secrets = [];
function redact(text) {
  let value = String(text);
  for (const secret of secrets) value = value.split(secret).join('<key>');
  return value;
}
// True when TOKEN is a personal key; a well-formed key is registered for
// redaction. A malformed one is never registered, sent, or echoed.
function acceptKey(token) {
  if (typeof token !== 'string' || !KEY.test(token)) return false;
  if (!secrets.includes(token)) {
    const before = secrets.findIndex(secret => secret.length < token.length);
    secrets.splice(before === -1 ? secrets.length : before, 0, token);
  }
  return true;
}
// Before anything is printed, the exported AGENT_AUTH_TOKEN and the stored
// session keys are registered, so a key pasted into the wrong prompt, typed
// into a URL or quoted by a child is rendered as <key>. Nothing is reported
// here; the command that needs the session explains what is wrong with it.
function primeSecrets() {
  acceptKey(process.env.AGENT_AUTH_TOKEN);
  let text = null;
  try { text = readSessionText(); } catch { return; }
  if (text === null) return;
  try {
    const value = JSON.parse(text);
    acceptKey(value?.token);
    if (record(value?.sessions)) for (const session of Object.values(value.sessions)) acceptKey(session?.token);
  } catch { /* loadStore reports */ }
}

// ── install layout ──────────────────────────────────────────────────────────
const here = path.dirname(fileURLToPath(import.meta.url));
const octal = mode => (mode & 0o777).toString(8).padStart(4, '0');
// release.json is trusted only when nobody else could have written it: opened
// without following a link and without blocking (a FIFO in its place is
// refused, never waited on), then judged by fstat as a regular file owned by
// this user that only this user may write, inside an install directory with
// the same properties. Absent (a source checkout) is null.
function releaseInfo() {
  const file = path.join(here, 'release.json');
  let fd;
  try { fd = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK); } catch (error) {
    if (error.code === 'ENOENT') return null;
    if (error.code === 'ELOOP') throw new CliError(`${file} must not be a symlink; remove it and rerun the published install line`);
    throw error;
  }
  let text;
  try {
    const directory = fs.statSync(here);
    if (directory.uid !== process.getuid()) throw new CliError(`${here} is not owned by this user; fix it and rerun the published install line`);
    if ((directory.mode & 0o022) !== 0) throw new CliError(`${here} must not be writable by others, found ${octal(directory.mode)}; run chmod 0755 on it`);
    const stat = fs.fstatSync(fd);
    if (!stat.isFile()) throw new CliError(`${file} is not a regular file; remove it and rerun the published install line`);
    if (stat.uid !== process.getuid()) throw new CliError(`${file} is not owned by this user; remove it and rerun the published install line`);
    if ((stat.mode & 0o022) !== 0) throw new CliError(`${file} must not be writable by others, found ${octal(stat.mode)}; run chmod 0644 on it`);
    text = fs.readFileSync(fd, 'utf8');
  } finally { fs.closeSync(fd); }
  let value;
  try { value = JSON.parse(text); } catch { throw new CliError(`${file} is not valid JSON; rerun the published install line`); }
  if (!record(value)) throw new CliError(`${file} is not a release record; rerun the published install line`);
  return value;
}
// Installed: beside genesis.mjs. Source checkout: the assembled artifact one directory up.
function setupScript() {
  for (const candidate of [path.join(here, 'agent-auth-setup.sh'), path.join(here, '..', 'agent-auth-setup.sh')]) {
    if (fs.existsSync(candidate)) return candidate;
  }
  throw new CliError('agent-auth-setup.sh is missing beside genesis.mjs; run genesis update');
}

// ── session store ───────────────────────────────────────────────────────────
// ${XDG_CONFIG_HOME:-~/.config}/genesis/session.json (0600, dir 0700) holds
// {version: 3, environment, sessions: {prod?, staging?}}, replaced by rename.
export function configDir() {
  const xdg = process.env.XDG_CONFIG_HOME;
  return path.join(xdg && path.isAbsolute(xdg) ? xdg : path.join(os.homedir(), '.config'), 'genesis');
}
export const sessionFile = () => path.join(configDir(), 'session.json');
// The directory must be a real directory owned by this user, mode exactly
// 0700; null when absent.
function checkSessionDir(directory) {
  let stat;
  try { stat = fs.lstatSync(directory); } catch (error) { if (error.code === 'ENOENT') return null; throw error; }
  if (stat.isSymbolicLink() || !stat.isDirectory()) throw new CliError(`${directory} must be a directory, not a symlink; fix it and run genesis login`);
  if (stat.uid !== process.getuid()) throw new CliError(`${directory} is not owned by this user; fix it and run genesis login`);
  if ((stat.mode & 0o777) !== 0o700) throw new CliError(`${directory} must be mode 0700, found ${octal(stat.mode)}; run chmod 0700 on it`);
  return stat;
}
function refuseSymlink(file) {
  let stat;
  try { stat = fs.lstatSync(file); } catch (error) { if (error.code === 'ENOENT') return; throw error; }
  if (stat.isSymbolicLink()) throw new CliError(`${file} must not be a symlink`);
}
function readPrivate(file) {
  refuseSymlink(file);
  try { return fs.readFileSync(file, 'utf8'); } catch (error) { if (error.code === 'ENOENT') return null; throw error; }
}
// Opened without following a link and without blocking (a FIFO in its place
// is refused, never waited on), then judged by fstat: a regular file, owned
// by this user, mode exactly 0600. Anything else is refused in one line.
function readSessionText() {
  const file = sessionFile();
  if (checkSessionDir(path.dirname(file)) === null) return null;
  let fd;
  try { fd = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK); } catch (error) {
    if (error.code === 'ENOENT') return null;
    if (error.code === 'ELOOP') throw new CliError(`${file} must not be a symlink; remove it and run genesis login`);
    throw error;
  }
  try {
    const stat = fs.fstatSync(fd);
    if (!stat.isFile()) throw new CliError(`${file} is not a regular file; remove it and run genesis login`);
    if (stat.uid !== process.getuid()) throw new CliError(`${file} is not owned by this user; remove it and run genesis login`);
    if ((stat.mode & 0o777) !== 0o600) throw new CliError(`${file} must be mode 0600, found ${octal(stat.mode)}; run chmod 0600 on it or genesis login`);
    return fs.readFileSync(fd, 'utf8');
  } finally { fs.closeSync(fd); }
}
// Created 0600 under a 0700 directory owned by this user, then renamed into place.
function writeSessionText(text) {
  const file = sessionFile();
  const directory = path.dirname(file);
  if (checkSessionDir(directory) === null) { fs.mkdirSync(directory, { recursive: true, mode: 0o700 }); fs.chmodSync(directory, 0o700); }
  refuseSymlink(file);
  const temporary = `${file}.${process.pid}.tmp`;
  const fd = fs.openSync(temporary, fs.constants.O_CREAT | fs.constants.O_EXCL | fs.constants.O_WRONLY, 0o600);
  try { fs.writeFileSync(fd, text); fs.fsyncSync(fd); } finally { fs.closeSync(fd); }
  fs.renameSync(temporary, file);
}
function storedSession(value) {
  const file = sessionFile();
  if (!record(value) || typeof value.endpoint !== 'string' || typeof value.name !== 'string'
    || !ROLES.has(value.role)
    || (value.email !== null && typeof value.email !== 'string') || typeof value.updatedAt !== 'string') {
    throw new CliError(`${file} is not a genesis session store; remove it and run genesis login`);
  }
  if (!acceptKey(value.token)) throw new CliError(`${file} does not hold a personal gateway key; run genesis login`);
  return {
    endpoint: environmentEndpoint(value.endpoint), name: value.name, role: value.role,
    email: value.email, token: value.token, updatedAt: value.updatedAt, identityClass: identityClassOf(value.identityClass),
  };
}
function checkSessionIsolation(store, environment, endpoint, token) {
  for (const [other, session] of Object.entries(store.sessions)) {
    if (other === environment) {
      if (session.endpoint !== endpoint && session.token === token) throw new CliError(`${endpoint} needs its own key; the supplied key belongs to ${session.endpoint}`);
      continue;
    }
    if (session.endpoint === endpoint) throw new CliError(`${environmentLabel(environment)} needs its own gateway; ${endpoint} belongs to ${environmentLabel(other)}`);
    if (session.token === token) throw new CliError(`${environmentLabel(environment)} needs its own key; the supplied key belongs to ${environmentLabel(other)}`);
  }
}
// Version 1 held one login; version 2 named the environments main/staging.
// Both convert once: the canonical gateway (or `main`) becomes prod.
function loadStore() {
  const text = readSessionText();
  if (text === null) return { version: 3, environment: 'prod', sessions: {} };
  const file = sessionFile();
  let value;
  try { value = JSON.parse(text); } catch { throw new CliError(`${file} is not valid JSON; remove it and run genesis login`); }
  const invalid = () => new CliError(`${file} is not a genesis session store; remove it and run genesis login`);
  if (!record(value)) throw invalid();
  let converted = false;
  if (value.version === 1) {
    const environment = environmentEndpoint(value.endpoint) === PROD_ENDPOINT ? 'prod' : 'staging';
    value = { version: 3, environment, sessions: { [environment]: value } };
    converted = true;
  } else if (value.version === 2) {
    const legacy = new Set(['main', 'staging']);
    if (!record(value.sessions) || !legacy.has(value.environment) || Object.keys(value.sessions).some(key => !legacy.has(key))) throw invalid();
    const renamed = key => (key === 'main' ? 'prod' : key);
    value = { version: 3, environment: renamed(value.environment), sessions: Object.fromEntries(Object.entries(value.sessions).map(([key, session]) => [renamed(key), session])) };
    converted = true;
  }
  if (value.version !== 3 || typeof value.environment !== 'string' || !Object.hasOwn(ENVIRONMENTS, value.environment) || !record(value.sessions)
    || Object.keys(value.sessions).some(environment => !Object.hasOwn(ENVIRONMENTS, environment))) {
    throw invalid();
  }
  for (const [environment, session] of Object.entries(value.sessions)) value.sessions[environment] = storedSession(session);
  for (const [environment, session] of Object.entries(value.sessions)) checkSessionIsolation(value, environment, session.endpoint, session.token);
  if (converted) writeSessionText(JSON.stringify(value, null, 2) + '\n');
  return value;
}
export function loadSession(environment) {
  const store = loadStore();
  const selected = environmentId(environment ?? store.environment);
  const session = store.sessions[selected];
  return session === undefined ? null : { environment: selected, ...session };
}
function saveSession(session) {
  const store = loadStore();
  checkSessionIsolation(store, session.environment, session.endpoint, session.token);
  store.sessions[session.environment] = storedSession({ ...session, updatedAt: new Date().toISOString() });
  writeSessionText(JSON.stringify(store, null, 2) + '\n');
}
async function selectEnvironment(environment, view = null) {
  environmentId(environment);
  let session = loadSession(environment);
  if (environment !== 'prod') {
    if (session === null) session = await login({ environment }, view);
    else await requireProdDev(view);
  }
  const store = loadStore();
  store.environment = environment;
  writeSessionText(JSON.stringify(store, null, 2) + '\n');
  return session;
}
// Logout keeps the selected environment and the other login, never client files.
function clearSession(environment) {
  const store = loadStore();
  const selected = environmentId(environment ?? store.environment);
  if (Object.hasOwn(store.sessions, selected)) {
    delete store.sessions[selected];
    writeSessionText(JSON.stringify(store, null, 2) + '\n');
  }
  return selected;
}
async function requireSession(flags) {
  const store = loadStore();
  const environment = environmentId(flags.environment ?? store.environment);
  if (environment !== 'prod') {
    await runAction('Prod access', async view => { await requireProdDev(view); return false; }, true);
  }
  const session = store.sessions[environment];
  if (session === undefined) throw new CliError(`${environmentLabel(environment)} is not logged in; run genesis login --environment ${environment}`);
  return { environment, ...session };
}

// ── endpoint ────────────────────────────────────────────────────────────────
// Same rules as the installer: a bare host means HTTPS; cleartext HTTP only on loopback.
export function normalizeEndpoint(input) {
  let value = String(input ?? '').trim();
  if (value === '') return { error: 'enter the gateway host or URL, for example gateway.example.com' };
  if (/\s/.test(value)) return { error: 'the gateway URL must not contain spaces' };
  if (!value.includes('://')) value = `https://${value}`;
  value = value.replace(/\/+$/, '');
  if (value.includes('?') || value.includes('#')) return { error: 'the gateway URL must not contain a query or fragment' };
  const secure = /^https:\/\/([^/]+)(\/.*)?$/.exec(value);
  if (secure !== null) {
    if (secure[1].includes('@')) return { error: 'the gateway URL must not contain credentials' };
    return { value };
  }
  if (/^http:\/\/(localhost|127\.0\.0\.1|\[::1\])(:[0-9]+)?(\/.*)?$/.test(value)) return { value };
  if (value.startsWith('http://')) return { error: 'cleartext http:// is accepted only for localhost; use https://' };
  return { error: 'use https://HOST (or a bare host); other schemes are not gateways' };
}
// Anything key-shaped anywhere in the typed URL (a bare key, an embedded or
// percent-encoded one) is registered for redaction and refused before the
// URL is canonicalized, resolved or printed.
const KEY_LIKE = /s99dev\.[A-Za-z0-9_-]{20,512}/gi;
function refuseKeyInUrl(text) {
  const matches = text.match(KEY_LIKE);
  if (matches === null) return;
  for (const match of matches) if (!acceptKey(match) && !secrets.includes(match)) secrets.unshift(match);
  throw usage('the gateway URL must not contain a key');
}
function environmentEndpoint(input) {
  const raw = String(input ?? '');
  refuseKeyInUrl(raw);
  try { refuseKeyInUrl(decodeURIComponent(raw)); } catch (error) { if (error instanceof CliError) throw error; }
  const result = normalizeEndpoint(raw);
  if (result.error !== undefined) throw usage(result.error);
  try { return new URL(result.value).href.replace(/\/+$/, ''); } catch { throw usage('the gateway URL is invalid'); }
}

// ── HTTP ────────────────────────────────────────────────────────────────────
function reasonOf(error) {
  if (error?.name === 'TimeoutError') return `timed out after ${HTTP_TIMEOUT_MS / 1000} s`;
  const cause = error?.cause;
  if (typeof cause?.code === 'string') return cause.code;
  return String(cause?.message ?? error?.message ?? error);
}
function requestDeadline(timeoutMs, interruptible = true) {
  const controller = new AbortController();
  const operation = interruptible ? workContext.getStore()?.signal : null;
  const abort = () => controller.abort();
  const timer = setTimeout(() => controller.abort(new DOMException('Request timed out', 'TimeoutError')), timeoutMs);
  if (operation?.aborted) abort();
  else operation?.addEventListener('abort', abort, { once: true });
  return {
    signal: controller.signal,
    close() { clearTimeout(timer); operation?.removeEventListener('abort', abort); },
  };
}
// JSON in, JSON out. Failures become one line naming the host and the server's
// `error`; a bearer is sent only when it is a personal key, and its bytes are
// redacted from every rendered line.
async function request(endpoint, token, method, pathname, body, timeoutMs = HTTP_TIMEOUT_MS) {
  if (workContext.getStore()?.signal.aborted) throw new Interrupt();
  const headers = { Accept: 'application/json' };
  if (token !== null) {
    if (!acceptKey(token)) throw new CliError(`the stored key is not a personal gateway key (${KEY_SHAPE}); run genesis login`);
    headers.Authorization = `Bearer ${token}`;
  }
  if (body !== undefined) headers['Content-Type'] = 'application/json';
  // A dispatched mutation must settle (notably key rotation) so its committed
  // result can be saved. Read requests can stop immediately.
  const deadline = requestDeadline(timeoutMs, method === 'GET');
  try {
    let response;
    try {
      response = await fetch(`${endpoint}${pathname}`, {
        method, headers, body: body === undefined ? undefined : JSON.stringify(body),
        redirect: 'manual', signal: deadline.signal,
      });
    } catch (error) {
      throw new CliError(`could not reach ${hostOf(endpoint)}: ${reasonOf(error)}`);
    }
    if (Number(response.headers.get('content-length') ?? 0) > 4 * 1024 * 1024) {
      throw new CliError(`${hostOf(endpoint)}: response too large for ${pathname}`);
    }
    const text = await response.text();
    let value = null;
    try { value = text === '' ? null : JSON.parse(text); } catch { value = null; }
    if (!response.ok) {
      const detail = typeof value?.error === 'string' ? value.error : `unexpected ${response.status} response`;
      throw new HttpError(response.status, `${hostOf(endpoint)}: ${detail} (HTTP ${response.status})`);
    }
    return value;
  } finally { deadline.close(); }
}
const api = (session, method, pathname, body, timeoutMs) => request(session.endpoint, session.token, method, pathname, body, timeoutMs);

// ── terminal ────────────────────────────────────────────────────────────────
const utf8 = /utf-?8/i.test(process.env.LC_ALL || process.env.LC_CTYPE || process.env.LANG || '');
const glyph = utf8
  ? { ok: '✓', pick: '❯', step: '›', dot: '·', more: '…', range: '–' }
  : { ok: '+', pick: '>', step: '>', dot: '.', more: '...', range: '-' };
const ansi = () => process.env.TERM !== 'dumb';
let screenOutput = null;
let activeWork = null;
// Earlier connection cleanup must not inherit a later menu's cancellation.
const workContext = new AsyncLocalStorage();
const colorOut = () => screenOutput === null && process.stdout.isTTY === true && ansi() && !process.env.NO_COLOR;
const paint = (code, text, enabled = colorOut()) => (enabled ? `\x1b[${code}m${text}\x1b[0m` : text);
const writeOutput = (target, text, encoding = 'utf8') => {
  const safe = redact(text);
  if (screenOutput !== null) screenOutput(encoding === 'latin1' ? Buffer.from(safe, 'latin1').toString('utf8') : safe);
  else target.write(safe, encoding);
};
const out = text => writeOutput(process.stdout, `${text}\n`);
const note = text => out(`${glyph.step} ${text}`);
const done = (label, value) => out(`${paint('32', glyph.ok)} ${label.padEnd(9)} ${value}`);
const warn = text => out(`${paint('33', '!')} ${text}`);
// Child output (the installer) is relayed line by line through redact():
// bytes are held until their newline arrives, so a key split across two
// chunks is still caught, and the remainder is flushed when the stream
// closes. latin1 maps every byte to one character and back, so nothing else
// about the child's bytes changes.
function relay(source, target) {
  let held = '';
  source.setEncoding('latin1');
  source.on('data', chunk => {
    held += chunk;
    const cut = held.lastIndexOf('\n') + 1;
    if (cut === 0) return;
    writeOutput(target, held.slice(0, cut), 'latin1');
    held = held.slice(cut);
  });
  source.on('close', () => { if (held !== '') writeOutput(target, held, 'latin1'); });
}

let terminal = null;
function tty() {
  if (terminal !== null) return terminal;
  let fd;
  try { fd = fs.openSync('/dev/tty', 'r+'); } catch { return null; }
  const input = new ttyModule.ReadStream(fd);
  emitKeypressEvents(input);
  const output = new ttyModule.WriteStream(fd);
  input.pause();
  terminal = { fd, input, output, cursorHidden: false, raw: false, alternateScreen: false };
  return terminal;
}
// Prompts need a terminal for output and /dev/tty for input; stdin may be a pipe.
export const interactive = () => process.stdout.isTTY === true && tty() !== null;
const colorTty = () => ansi() && !process.env.NO_COLOR;
const tint = (code, text) => paint(code, text, colorTty());
// Terminal text — prompts, echoes, menus and summaries — is always redacted.
const term = text => { tty().output.write(redact(text)); };
function restoreTerminal() {
  if (terminal === null) return;
  if (terminal.cursorHidden) { term('\x1b[?25h'); terminal.cursorHidden = false; }
  if (terminal.raw) { terminal.input.setRawMode(false); terminal.raw = false; }
  terminal.input.pause();
}
function closeTerminal() {
  if (terminal === null) return;
  restoreTerminal();
  if (terminal.alternateScreen) fs.writeSync(terminal.fd, '\x1b[?1049l');
  terminal.input.destroy();
  terminal = null;
}
function readChunk() {
  const { input } = tty();
  input.setRawMode(true);
  terminal.raw = true;
  input.resume();
  return new Promise(resolve => {
    input.once('data', chunk => {
      input.pause();
      input.setRawMode(false);
      terminal.raw = false;
      resolve(chunk.toString('utf8'));
    });
  });
}
// One line from the terminal in raw mode: no echo when hidden, backspace and
// Ctrl-U edit, Ctrl-C interrupts, escape sequences (arrows) are ignored.
async function readLine(hidden) {
  let line = '';
  for (;;) {
    const chunk = await readChunk();
    if (chunk.startsWith('\x1b')) continue;
    for (const char of chunk) {
      if (char === '\r' || char === '\n') { term('\n'); return line; }
      if (char === '\x03') { term('\n'); throw new Interrupt(); }
      if (char === '\x04' && line === '') { term('\n'); throw new CliError('cancelled', 1); }
      if (char === '\x7f' || char === '\b') {
        if (line !== '') { line = line.slice(0, -1); if (!hidden) term('\b \b'); }
        continue;
      }
      if (char === '\x15') { if (!hidden) term('\b \b'.repeat(line.length)); line = ''; continue; }
      if (char < ' ') continue;
      line += char;
      if (!hidden) term(char);
    }
  }
}
// Node refreshes stdout's size on SIGWINCH; the /dev/tty stream is never
// refreshed, so every frame measures the terminal stdout is on (interactive
// use requires stdout to be a terminal).
const windowSize = () => {
  const source = process.stdout.isTTY === true ? process.stdout : tty()?.output;
  return { columns: source?.columns || 80, rows: source?.rows || 24 };
};
const columns = () => windowSize().columns;
const summary = (label, value) => term(`${tint('32', glyph.ok)} ${label.padEnd(9)} ${value}\n`);
// ask(label, validate): validate returns {value} or {error}; the typed line is
// replaced by a one-line summary once accepted, or by the error when refused
// (so a key pasted here stays on screen no longer than the prompt). An empty
// line takes `fallback` when one is shown.
async function ask(label, validate, summaryLabel = label, fallback = null) {
  for (;;) {
    const hint = fallback === null ? '' : ` (${fallback})`;
    const prompt = `? ${label}${hint} ${glyph.step} `;
    term(`${tint('36', '?')} ${tint('1', label)}${tint('2', hint)} ${glyph.step} `);
    const line = await readLine(false);
    const result = validate(line.trim() === '' && fallback !== null ? fallback : line);
    if (ansi()) term(`\x1b[${Math.floor((prompt.length + line.length) / columns()) + 1}A\x1b[J`);
    if (result.error === undefined) {
      summary(summaryLabel, result.value);
      return result.value;
    }
    term(`${tint('33', '!')} ${result.error}\n`);
  }
}
async function secret(label, summaryLabel) {
  for (;;) {
    term(`${tint('36', '?')} ${tint('1', label)} ${tint('2', '(hidden)')} ${glyph.step} `);
    const line = await readLine(true);
    if (line === '') { term(`${tint('33', '!')} nothing was entered\n`); continue; }
    if (/\s/.test(line)) { term(`${tint('33', '!')} a key is one word with no spaces\n`); continue; }
    if (ansi()) term('\x1b[1A\x1b[J');
    summary(summaryLabel, 'received');
    return line;
  }
}
async function confirm(question, defaultYes = false) {
  for (;;) {
    term(`${tint('36', '?')} ${question} ${tint('2', defaultYes ? '(Y/n)' : '(y/N)')} ${glyph.step} `);
    const line = (await readLine(false)).trim().toLowerCase();
    if (line === '') return defaultYes;
    if (['y', 'yes'].includes(line)) return true;
    if (['n', 'no'].includes(line)) return false;
    term(`${tint('33', '!')} answer y or n\n`);
  }
}
const BACK = Symbol('back');
const backOption = { value: BACK, label: 'Back' };
// Clipping and wrapping measure visible width: a painted line that fits
// keeps its paint, one that does not is cut as plain text.
const ANSI_PAINT = /\x1b\[[0-9;]*m/g;
const clipLine = (text, width) => {
  const value = String(text);
  const plain = value.replace(ANSI_PAINT, '');
  if (plain.length <= width) return value;
  if (width <= glyph.more.length) return glyph.more.slice(0, width);
  return `${plain.slice(0, width - glyph.more.length)}${glyph.more}`;
};
const wrapLines = (text, width) => String(text ?? '').split('\n').flatMap(line => {
  if (line === '') return [''];
  const plain = line.replace(ANSI_PAINT, '');
  if (plain.length <= width) return [line];
  const wrapped = [];
  for (let offset = 0; offset < plain.length; offset += width) wrapped.push(plain.slice(offset, offset + width));
  return wrapped;
});
const heading = text => tint('1', tint('2', text));
// One frame: title, the step's status line, the Status body, the Menu and
// the key footer. The menu takes the rows it needs first (a long menu
// scrolls behind "N above"/"N more" markers); the body gets the rest and
// scrolls with Page Up/Down. Below sixteen rows the blank separators go, so
// a short pane spends every row on the menu and the body. Everything is
// redacted before it is measured or cut, so a clipped value can never leave
// the head of a key behind.
function renderScreen(view) {
  const size = windowSize();
  const width = Math.max(20, size.columns - 4);
  const height = Math.max(8, size.rows);
  const gap = height < 16 ? [] : [''];
  const options = view.options ?? [];
  if (view.selectionOptions !== options) {
    view.selectionOptions = options;
    view.selected = Math.max(0, options.findIndex(option => option.value !== BACK));
  } else if (!options[view.selected]) view.selected = Math.max(0, options.length - 1);
  const renderedBody = Array.isArray(view.statusRows) ? renderStatus(view.statusRows, Math.min(width, 80)) : view.body;
  const body = [view.identity, renderedBody, view.notice].filter(Boolean).join('\n\n');
  const bodyLines = wrapLines(redact(body), width);
  const head = [tint('1', clipLine(redact(view.title), width)), ...gap];
  if (view.status) {
    head.push(tint(view.failed ? '31' : view.status.startsWith('Complete') ? '32' : '36', clipLine(redact(view.status), width)), ...gap);
  }
  const footer = tint('2', [
    utf8 ? '↑↓ navigate' : 'up/down navigate', utf8 ? '⏎ select' : 'Enter select', view.root ? 'esc quit' : 'esc back',
  ].join(utf8 ? ' • ' : ' . '));
  // Rows that are neither options nor body: the head, the Menu heading and
  // the footer with their gaps, and the cursor's row under the footer.
  const fixedRows = head.length + gap.length + 1 + gap.length + 1 + 1;
  const roomForMenu = Math.max(1, height - fixedRows);
  // A scrolled menu keeps the cursor inside its window; the window gives up
  // one row per marker it actually draws.
  const windowStart = count => (options.length <= count ? 0 : Math.max(0, Math.min(view.selected - count + 1, options.length - count)));
  let visibleCount = Math.max(1, roomForMenu - (options.length > roomForMenu ? 1 : 0));
  let firstOption = windowStart(visibleCount);
  if (firstOption > 0 && firstOption + visibleCount < options.length) {
    visibleCount = Math.max(1, roomForMenu - 2);
    firstOption = windowStart(visibleCount);
  }
  const lastOption = Math.min(options.length, firstOption + visibleCount);
  const labels = options.map(option => redact(String(option.label)));
  const labelWidth = labels.reduce((longest, label) => Math.max(longest, label.length), 0);
  const optionRows = [];
  if (firstOption > 0) optionRows.push(tint('2', `${glyph.more} ${firstOption} above`));
  for (let index = firstOption; index < lastOption; index++) {
    const option = options[index];
    const cursor = index === view.selected ? glyph.pick : ' ';
    const number = String(index + 1).padStart(2, ' ');
    const hint = option.hint ? `  ${tint('2', redact(String(option.hint)))}` : '';
    optionRows.push(clipLine(`${cursor} ${number}  ${labels[index].padEnd(labelWidth, ' ')}${hint}`, width - 2));
  }
  if (lastOption < options.length) optionRows.push(tint('2', `${glyph.more} ${options.length - lastOption} more`));
  let bodyRows = bodyLines.length === 0 ? 0 : Math.max(0, height - fixedRows - optionRows.length - 1);
  const bodyOverflow = bodyRows > 1 && bodyLines.length > bodyRows;
  if (bodyOverflow) bodyRows -= 1;
  const maxOffset = Math.max(0, bodyLines.length - bodyRows);
  view.offset = view.offset === Infinity
    ? maxOffset
    : Math.max(0, Math.min(view.offset ?? 0, maxOffset));
  const bodyFrame = bodyRows > 0 ? bodyLines.slice(view.offset, view.offset + bodyRows) : [];
  if (bodyOverflow) bodyFrame.push(tint('2', `${view.offset + 1}${glyph.range}${Math.min(bodyLines.length, view.offset + bodyRows)}/${bodyLines.length}`));
  const lines = [...head];
  // A Status heading with nothing under it is noise: a pane that gave every
  // row to the menu shows the menu alone.
  if (bodyFrame.length > 0) lines.push(heading('Status'), ...bodyFrame);
  lines.push(...gap, heading('Menu'), ...optionRows, ...gap, footer);
  const margin = line => line === '' ? '' : `  ${line}`;
  term(`${ansi() ? '\x1b[H\x1b[2J' : '\f'}${lines.map(margin).join('\n')}\n`);
}
// Rebuilt menus start at their first action. Movement within one options list
// keeps its cursor; Escape never confirms a highlighted action. A typed
// number moves the cursor at once; when the menu reaches the number a second
// digit would form, the first waits briefly for it (so "12" is item 12, not
// item 1 then item 2).
async function selectScreen(view, signal, renderInitial = true) {
  const { input } = tty();
  if (signal?.aborted) return BACK;
  let keypress, resize, abort, ended;
  let pendingTimer = null;
  let pendingDigits = null;
  const settlePending = () => {
    clearTimeout(pendingTimer);
    pendingTimer = null;
    pendingDigits = null;
  };
  try {
    return await new Promise((resolve, reject) => {
      keypress = (text, key) => {
        if (key?.ctrl && key.name === 'c') {
          if (view.interrupt) view.interrupt();
          else reject(new Interrupt());
          return;
        }
        if (view.options.length === 0) return;
        const count = view.options.length;
        if (/^[0-9]$/.test(text ?? '')) {
          const number = Number(`${pendingDigits ?? ''}${text}`);
          settlePending();
          if (number < 1 || number > count) return;
          view.selected = number - 1;
          if (number * 10 <= count) {
            pendingDigits = String(number);
            pendingTimer = setTimeout(settlePending, 700);
          }
          renderScreen(view);
          return;
        }
        settlePending();
        if (key?.name === 'escape' || key?.name === 'left' || key?.name === 'backspace'
          || text === '\x7f' || (key?.ctrl && key.name === 'd') || text === 'q' || text === 'Q') {
          resolve(BACK);
          return;
        }
        if (key?.name === 'return' || key?.name === 'enter') {
          resolve(view.options[view.selected ?? 0].value);
          return;
        }
        if (key?.name === 'up' || text === 'k' || text === 'K') view.selected = ((view.selected ?? 0) + count - 1) % count;
        else if (key?.name === 'down' || text === 'j' || text === 'J') view.selected = ((view.selected ?? 0) + 1) % count;
        else if (key?.name === 'home') view.selected = 0;
        else if (key?.name === 'end') view.selected = count - 1;
        else if (key?.name === 'pageup') view.offset = Math.max(0, (view.offset ?? 0) - 5);
        else if (key?.name === 'pagedown') view.offset = (view.offset ?? 0) + 5;
        else return;
        renderScreen(view);
      };
      resize = () => renderScreen(view);
      abort = () => resolve(BACK);
      ended = () => resolve(BACK);
      input.on('keypress', keypress);
      input.once('end', ended);
      process.stdout.on('resize', resize);
      signal?.addEventListener('abort', abort, { once: true });
      input.setRawMode(true);
      terminal.raw = true;
      input.resume();
      if (ansi()) { term('\x1b[?25l'); terminal.cursorHidden = true; }
      if (renderInitial) renderScreen(view);
    });
  } finally {
    settlePending();
    input.off('keypress', keypress);
    input.off('end', ended);
    process.stdout.off('resize', resize);
    signal?.removeEventListener('abort', abort);
    restoreTerminal();
  }
}

// Keep reading while work runs: keys pressed during a slow step must not
// become an acknowledgement of its result. Prompts run outside this boundary.
async function runProgress(view, label, work) {
  const running = {
    title: view.title, root: view.root === true, identity: view.identity, status: `Running ${glyph.dot} ${label}`, body: '', options: [],
    interrupt: () => process.emit('SIGINT'),
  };
  const finished = new AbortController();
  const operation = new AbortController();
  activeWork = operation;
  let visible = false, redraw = null, inputError = null, interrupts = 0;
  const draw = () => {
    if (!visible || redraw !== null) return;
    redraw = setImmediate(() => { redraw = null; renderScreen(running); });
  };
  // Input belongs to this operation immediately; quick loads need no extra frame.
  const reveal = setTimeout(() => { visible = true; draw(); }, 150);
  const interrupt = () => {
    if (++interrupts > 1) { closeTerminal(); process.exit(130); }
    operation.abort();
    running.status = `Stopping ${glyph.dot} ${label}`;
    visible = true;
    draw();
  };
  for (const signal of ['SIGINT', 'SIGTERM', 'SIGHUP']) process.on(signal, interrupt);
  const input = selectScreen(running, finished.signal, false).catch(error => { inputError = error; operation.abort(); });
  screenOutput = text => {
    running.body += text;
    running.offset = Infinity;
    draw();
  };
  try {
    const value = await workContext.run(operation, work);
    if (inputError !== null) throw inputError;
    if (operation.signal.aborted) throw new Interrupt();
    return value;
  } catch (error) {
    if (operation.signal.aborted) throw new Interrupt();
    throw error;
  } finally {
    clearTimeout(reveal);
    clearImmediate(redraw);
    screenOutput = null;
    if (running.body !== '') { view.body = running.body.trim(); view.offset = Infinity; }
    finished.abort();
    await input;
    activeWork = null;
    for (const signal of ['SIGINT', 'SIGTERM', 'SIGHUP']) process.off(signal, interrupt);
  }
}
function showResult(view, status, body = view.body, failed = false) {
  Object.assign(view, { route: 'result', status, body, failed, options: [backOption], selected: 0, offset: Infinity, ready: true });
}
async function runAction(label, work, prompts = false) {
  if (!interactive() || screenOutput !== null) return work(null);
  const view = { title: `genesis ${glyph.step} ${label}` };
  const alternate = ansi() && !terminal.alternateScreen;
  if (alternate) { terminal.alternateScreen = true; term('\x1b[?1049h'); }
  let result, failure;
  const interrupt = () => { if (activeWork === null) { closeTerminal(); process.exit(130); } };
  for (const signal of ['SIGINT', 'SIGTERM', 'SIGHUP']) process.on(signal, interrupt);
  try {
    try {
      result = await (prompts ? work(view) : runProgress(view, label, () => work(view)));
      if (result === false) return false;
      showResult(view, `Complete ${glyph.dot} ${label}`);
    } catch (error) {
      if (error instanceof Interrupt) {
        if (view.body) showResult(view, `Interrupted ${glyph.dot} ${label}`);
        throw error;
      }
      failure = error;
      showResult(view, `Failed ${glyph.dot} ${label}`, [error.message || String(error), view.body].filter(Boolean).join('\n\n'), true);
    }
    await selectScreen(view);
  } finally {
    for (const signal of ['SIGINT', 'SIGTERM', 'SIGHUP']) process.off(signal, interrupt);
    if (alternate && terminal !== null) { term('\x1b[?1049l'); terminal.alternateScreen = false; }
    if (view.route === 'result') {
      out(view.status);
      if (view.body) out(view.body);
    }
  }
  if (failure) throw new CliError('', failure instanceof CliError ? failure.exitCode : 1);
  return result;
}
// Unattended children get their own group so Ctrl-C also reaches subprocesses
// (curl, sleep, client probes), not only the shell waiting for them.
function spawnWork(command, args, options) {
  const signal = workContext.getStore()?.signal;
  if (signal?.aborted) throw new Interrupt();
  const child = spawn(command, args, { ...options, detached: signal !== undefined });
  if (signal) {
    const cancel = () => {
      if (!child.pid) return;
      try { process.kill(-child.pid, 'SIGINT'); } catch (error) { if (error.code !== 'ESRCH') throw error; }
    };
    signal.addEventListener('abort', cancel, { once: true });
    child.once('close', () => signal.removeEventListener('abort', cancel));
  }
  return child;
}
// Aligned columns, two spaces apart; `right` marks right-aligned columns.
export function table(header, rows, right = new Set()) {
  const widths = header.map((cell, column) => Math.max(cell.length, ...rows.map(row => String(row[column]).length)));
  const line = (row, dim) => row.map((cell, column) => {
    const text = String(cell);
    const padded = right.has(column) ? text.padStart(widths[column]) : text.padEnd(widths[column]);
    return dim ? paint('2', padded) : padded;
  }).join('  ').replace(/\s+$/, '');
  return [line(header, true), ...rows.map(row => line(row, false))].join('\n');
}
const amount = value => value.toLocaleString('en-US', { maximumFractionDigits: 2 });
const integer = value => Math.round(value).toLocaleString('en-US');
const percent = fraction => `${(fraction * 100).toLocaleString('en-US', { maximumFractionDigits: 1 })}%`;
export function countdown(untilMs, nowMs = Date.now()) {
  if (!Number.isFinite(untilMs)) return '—';
  const total = Math.max(0, Math.round((untilMs - nowMs) / 60_000));
  if (total === 0) return 'now';
  const days = Math.floor(total / 1440), hours = Math.floor((total % 1440) / 60), minutes = total % 60;
  if (days > 0) return `${days}d ${hours}h`;
  if (hours > 0) return `${hours}h ${minutes}m`;
  return `${minutes}m`;
}

// ── clients and scopes ──────────────────────────────────────────────────────
function clientById(id) {
  const client = CLIENTS.find(entry => entry.id === id);
  if (client === undefined) throw usage(`unknown client ${id}; use ${CLIENTS.map(entry => entry.id).join(', ')}`);
  return client;
}
function installed(binary) {
  for (const directory of (process.env.PATH ?? '').split(path.delimiter)) {
    if (directory === '') continue;
    const candidate = path.join(directory, binary);
    try { fs.accessSync(candidate, fs.constants.X_OK); if (fs.statSync(candidate).isFile()) return true; } catch { /* next entry */ }
  }
  return false;
}
const homeDir = (name, fallback) => {
  const value = process.env[name];
  return value && path.isAbsolute(value) ? value : path.join(os.homedir(), fallback);
};
const exists = file => { try { fs.lstatSync(file); return true; } catch { return false; } };
const isDirectory = file => { try { return fs.statSync(file).isDirectory(); } catch { return false; } };
// The installer's resolve_config_directory: the real path of the nearest
// existing ancestor plus the missing tail, so a scope under a linked directory
// names one physical place.
function realDirectory(directory) {
  let parent = directory;
  let suffix = '';
  while (!isDirectory(parent)) {
    suffix = `/${path.basename(parent)}${suffix}`;
    parent = path.dirname(parent);
  }
  return `${fs.realpathSync(parent)}${suffix}`;
}
// The installer's resolve_config_target: a linked config file is followed to
// its real path (at most 16 hops) and must be a regular file or absent.
function resolveConfigTarget(file) {
  if (!path.isAbsolute(file) || /[\t\r\n]/.test(file)) throw new CliError('config path must be one absolute path');
  let current = file;
  for (let hops = 0; ; hops++) {
    let stat;
    try { stat = fs.lstatSync(current); } catch (error) { if (error.code === 'ENOENT') break; throw error; }
    if (!stat.isSymbolicLink()) {
      if (!stat.isFile()) throw new CliError(`config is not a regular file: ${current}`);
      break;
    }
    if (hops >= 16) throw new CliError('config has a symlink loop');
    const target = fs.readlinkSync(current);
    current = path.isAbsolute(target) ? target : path.join(fs.realpathSync(path.dirname(current)), target);
  }
  return path.join(realDirectory(path.dirname(current)), path.basename(current));
}
// The same path rules as the installer: each client's own environment picks
// the scope; OMP answers through its own CLI. `targets` are the files whose
// presence means consent is needed before a configure replaces them.
async function resolveScope(client, profile) {
  if (client.id === 'omp') {
    const agentDir = await new Promise((resolve, reject) => {
      execFile('omp', [...(profile ? ['--profile', profile] : []), 'config', 'path'],
        { encoding: 'utf8', timeout: 20_000, signal: workContext.getStore()?.signal }, (error, stdout) => {
          const directory = stdout.trim();
          if (error || !path.isAbsolute(directory) || directory.includes('\n')) reject(new CliError('omp config path did not return one absolute path'));
          else resolve(directory);
        });
    });
    const tokenDir = path.join(agentDir, 'agent-auth');
    return { stateFile: path.join(tokenDir, 'switch.json'), targets: [path.join(agentDir, 'models.yml'), path.join(agentDir, 'config.yml'), path.join(tokenDir, 'token')] };
  }
  if (client.id === 'claude-code') {
    const directory = homeDir('CLAUDE_CONFIG_DIR', '.claude');
    return { stateFile: path.join(directory, 'agent-auth/switch.json'), targets: [path.join(directory, 'settings.json'), path.join(directory, 'agent-auth/token')] };
  }
  if (client.id === 'codex') {
    const directory = homeDir('CODEX_HOME', '.codex');
    const tokenDir = path.join(directory, 'agent-auth', profile ?? 'default');
    return {
      stateFile: path.join(tokenDir, 'switch.json'),
      targets: [path.join(directory, profile ? `${profile}.config.toml` : 'config.toml'), path.join(tokenDir, 'token'), path.join(tokenDir, 'models.json')],
    };
  }
  if (client.id === 'opencode') {
    // adapters/opencode.sh: an explicit OPENCODE_CONFIG, else the first present
    // (or linked) candidate; the key and state live beside the real config file.
    const directory = path.join(homeDir('XDG_CONFIG_HOME', '.config'), 'opencode');
    const explicit = process.env.OPENCODE_CONFIG;
    const config = resolveConfigTarget(explicit
      ? explicit
      : ['opencode.jsonc', 'opencode.json', 'config.json'].map(name => path.join(directory, name)).find(exists) ?? path.join(directory, 'opencode.json'));
    const tokenDir = path.join(path.dirname(config), 'agent-auth');
    return { stateFile: path.join(tokenDir, 'switch.json'), targets: [config, path.join(tokenDir, 'token')] };
  }
  const directory = homeDir('PI_CODING_AGENT_DIR', '.pi/agent');
  return { stateFile: path.join(directory, 'agent-auth/switch.json'), targets: [path.join(directory, 'models.json'), path.join(directory, 'settings.json'), path.join(directory, 'agent-auth/token')] };
}
// Codex keeps one private directory per profile; every switch state under it
// is a scope of its own. Other clients answer for the default scope only.
function codexProfiles() {
  const root = path.join(homeDir('CODEX_HOME', '.codex'), 'agent-auth');
  let names;
  try { names = fs.readdirSync(root); } catch { return []; }
  return names.filter(name => name !== 'default' && PROFILE.test(name) && exists(path.join(root, name, 'switch.json'))).sort();
}
const fieldAt = (state, role, keys) => {
  for (const file of Array.isArray(state.files) ? state.files : []) {
    if (file.role !== role || !Array.isArray(file.fields)) continue;
    const field = file.fields.find(entry => Array.isArray(entry.path) && entry.path.length === keys.length && entry.path.every((key, index) => key === keys[index]));
    if (field?.gateway?.present === true && typeof field.gateway.value === 'string') return field.gateway.value;
  }
  return null;
};
// The switch state the installer writes beside the key: mode, issuing gateway,
// and the gateway-owned fields (the client's default model among them).
export function readState(file, clientId) {
  const text = readPrivate(file);
  if (text === null) return null;
  let state;
  try { state = JSON.parse(text); } catch { throw new CliError(`${file} is not valid JSON`); }
  if (!record(state) || state.version !== 1 || !['enabled', 'disabled'].includes(state.mode)) throw new CliError(`${file} is not a switch state this CLI understands`);
  let model = null;
  if (clientId === 'omp') model = fieldAt(state, 'settings', ['modelRoles', 'default']);
  else if (clientId === 'pi') {
    const id = fieldAt(state, 'settings', ['defaultModel']);
    const provider = fieldAt(state, 'settings', ['defaultProvider']);
    model = id === null ? null : provider === null ? id : `${provider.replace(/^agent-auth-/, '')}/${id}`;
  } else model = fieldAt(state, 'config', ['model'])?.replace(/^agent-auth-/, '') ?? null;
  return { mode: state.mode, gateway: typeof state.gateway === 'string' ? state.gateway : null, model };
}
// connected | disabled | not configured | foreign gateway | not installed
export function scopeStatus(state, isInstalled, endpoint) {
  if (state === null) return isInstalled ? 'not configured' : 'not installed';
  if (state.gateway !== endpoint) return 'foreign gateway';
  return state.mode === 'enabled' ? 'connected' : 'disabled';
}
// One row per scope. `problem` is set when the scope could not be discovered
// (for example `omp config path` failed); such a scope is reported, never
// treated as absent.
async function statusRows(session, profile) {
  const rows = [];
  for (const client of CLIENTS) {
    const profiles = client.id === 'codex' ? [profile ?? '', ...codexProfiles().filter(name => name !== profile)] : [client.id === 'omp' ? profile ?? '' : ''];
    for (const scopeProfile of profiles) {
      const isInstalled = installed(client.binary);
      let state = null, problem = null;
      try {
        if (client.id !== 'omp' || isInstalled) state = readState((await resolveScope(client, scopeProfile || undefined)).stateFile, client.id);
      } catch (error) { problem = error.message; }
      rows.push({
        client, profile: scopeProfile, state, installed: isInstalled, problem,
        status: problem ?? scopeStatus(state, isInstalled, session?.endpoint ?? state?.gateway),
        label: scopeProfile ? `${client.label} (${scopeProfile})` : client.label,
      });
    }
  }
  return rows;
}
// The client table. Given a width, the columns are budgeted from their
// measured content: the widest ones give way first (a long model id before
// a client label), and no cell is cut before it is redacted.
export function renderStatus(rows, maxWidth = Infinity) {
  const titles = ['client', 'installed', 'state', 'model', 'gateway'];
  const values = rows.map(row => [
    row.label, row.installed ? 'yes' : 'no', row.status, row.state?.model ?? '—', row.state?.gateway ? hostOf(row.state.gateway) : '—',
  ].map(cell => redact(cell)));
  if (Number.isFinite(maxWidth)) {
    const widths = titles.map((cell, column) => Math.max(cell.length, ...values.map(row => row[column].length)));
    const gaps = 2 * (titles.length - 1);
    let excess = widths.reduce((sum, width) => sum + width, 0) + gaps - maxWidth;
    while (excess > 0) {
      const widest = widths.indexOf(Math.max(...widths));
      if (widths[widest] <= 4) break;
      widths[widest] -= 1;
      excess -= 1;
    }
    for (const row of values) for (const [column, width] of widths.entries()) row[column] = clipLine(row[column], width);
  }
  return table(titles, values);
}
const sessionIdentity = session => `${environmentLabel(session.environment)} ${glyph.dot} ${session.endpoint} ${glyph.dot} ${session.name} ${glyph.dot} ${session.role}${session.identityClass === 'external' ? ` ${glyph.dot} external` : session.identityClass === null ? ` ${glyph.dot} unclassified` : ''}`;
const header = session => out(paint('1', sessionIdentity(session)));

// ── installer ───────────────────────────────────────────────────────────────
// AGENT_AUTH_URL/AGENT_AUTH_TOKEN carry the session into the installer; the key
// never appears on a command line. Its prompts, when any, come from /dev/tty,
// which it opens itself. Its output is not the terminal's: every line goes,
// redacted, to the private setup log, and the terminal gets this CLI's own
// lines — or, with GENESIS_VERBOSE=1, the relayed output as well. A failure
// names the installer's reason and one next step; the log holds the rest.
const setupLogFile = () => path.join(configDir(), 'setup.log');
const verbose = () => process.env.GENESIS_VERBOSE === '1';
// The installer's stdout and stderr, line by line through redact(), appended
// under one header per run. Bytes are held until their newline so a key split
// across chunks is still caught; latin1 keeps every byte as one character.
function openSetupLog(client, action) {
  const file = setupLogFile();
  const directory = path.dirname(file);
  let fd = null;
  // The log is private or it is skipped: a regular file this user owns,
  // mode 0600 (an existing looser mode is tightened), never a symlink, and
  // never anything that could block the open or the writes (a FIFO).
  try {
    if (checkSessionDir(directory) === null) { fs.mkdirSync(directory, { recursive: true, mode: 0o700 }); fs.chmodSync(directory, 0o700); }
    refuseSymlink(file);
    fd = fs.openSync(file, fs.constants.O_CREAT | fs.constants.O_WRONLY | fs.constants.O_APPEND | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK, 0o600);
    const stat = fs.fstatSync(fd);
    if (!stat.isFile() || stat.uid !== process.getuid()) throw new CliError(`${file} is not a private regular file`);
    if ((stat.mode & 0o777) !== 0o600) fs.fchmodSync(fd, 0o600);
    fs.writeSync(fd, `== ${new Date().toISOString()} ${client.label} ${action}\n`);
  } catch {
    if (fd !== null) { try { fs.closeSync(fd); } catch { /* Already closed. */ } }
    fd = null;
  }
  const lines = [];
  const capture = source => {
    let held = '';
    source.setEncoding('latin1');
    const flush = text => {
      const safe = redact(Buffer.from(text, 'latin1').toString('utf8'));
      for (const line of safe.split('\n')) if (line !== '') lines.push(line);
      if (fd !== null) { try { fs.writeSync(fd, safe); } catch { /* The log is best effort. */ } }
    };
    source.on('data', chunk => {
      held += chunk;
      const cut = held.lastIndexOf('\n') + 1;
      if (cut === 0) return;
      flush(held.slice(0, cut));
      held = held.slice(cut);
    });
    source.on('close', () => { if (held !== '') { flush(`${held}\n`); held = ''; } });
  };
  return {
    capture,
    lines,
    file: fd === null ? null : file,
    close() { if (fd !== null) { try { fs.closeSync(fd); } catch { /* Already closed. */ } fd = null; } },
  };
}
// The installer's `setup failed: …` line, or its last line, as one cause.
function setupCause(lines, code, signal) {
  const failed = lines.map(line => /^setup failed: (.*)$/.exec(line)).filter(Boolean).at(-1);
  if (failed) return failed[1].trim();
  const last = lines.filter(line => line.trim() !== '').at(-1);
  return last ? last.trim() : `the setup script exited ${code ?? signal} without a reason`;
}
// One next step per cause the installer is known to print (setup/*.sh); a
// cause without a known step stands alone with the log. The model-id refusal
// is special: the CLI validated that id with the same rule, so the installed
// setup script's own validator failed to compile (macOS bash before the
// RE_DUP_MAX fix), and a newer release repairs it.
function setupNextStep(cause, client) {
  if (/^model ids are 1-256 printable ASCII characters/.test(cause)) return 'run genesis update, then retry';
  if (/^could not reach /.test(cause)) return 'check the gateway URL and your network, then retry';
  if (/^model .* is not served by this gateway/.test(cause)) return `pick a served model: genesis model ${client.id}`;
  if (/^(Node\.js|Python|curl|env) .*is required|^Python jsonschema|is required to verify/.test(cause)) return 'install the named prerequisite, then retry';
  if (/^no OMP protocol works/.test(cause)) return 'update OMP, then retry';
  return null;
}
async function runSetup(session, client, action, args, withToken) {
  const env = { ...process.env };
  delete env.AGENT_AUTH_URL;
  if (session !== null) env.AGENT_AUTH_URL = session.endpoint;
  delete env.AUTH_GATEWAY_TOKEN;
  delete env.AGENT_AUTH_KEY_CHOICE;
  delete env.AGENT_AUTH_TOKEN;
  if (withToken) env.AGENT_AUTH_TOKEN = session.token;
  note(`${client.label} ${action}`);
  const log = openSetupLog(client, action);
  const child = spawnWork('bash', [setupScript(), '--harness', client.id, '--action', action, '--unattended', ...args], { env, stdio: ['ignore', 'pipe', 'pipe'] });
  log.capture(child.stdout);
  log.capture(child.stderr);
  if (verbose()) { relay(child.stdout, process.stdout); relay(child.stderr, process.stderr); }
  const [code, signal] = await once(child, 'close');
  log.close();
  if (code === 0) return;
  if (signal === 'SIGINT' || code === 130) throw new Interrupt();
  const cause = setupCause(log.lines, code, signal);
  const next = setupNextStep(cause, client);
  const version = client.id === 'claude-code' ? await clientVersion(client) : null;
  throw new CliError([
    `${client.label} ${action} failed: ${cause}`,
    ...(version === null ? [] : [`  Installed: ${client.label} ${version}`]),
    ...(next === null ? [] : [`  Next: ${next}`]),
    ...(log.file === null ? [] : [`  Details: ${log.file}`]),
  ].join('\n'));
}
// `<binary> --version`, first line, for a failure report; null when the
// binary does not answer within a few seconds.
function clientVersion(client) {
  return new Promise(resolve => {
    let settled = false;
    const finish = value => { if (!settled) { settled = true; resolve(value); } };
    try {
      const child = execFile(client.binary, ['--version'], { timeout: 5000, killSignal: 'SIGKILL', maxBuffer: 64 * 1024 }, (error, stdout) => {
        const line = String(stdout ?? '').split('\n').find(entry => entry.trim() !== '');
        finish(error || !line ? null : redact(line.trim()).slice(0, 80));
      });
      child.on('error', () => finish(null));
    } catch { finish(null); }
  });
}
const profileArgs = profile => (profile ? ['--profile', profile] : []);
// The command that starts the client in the scope just configured: the
// profile for OMP and Codex, and the directory override when one is in
// force (the installer wrote the config where that variable points).
const SCOPE_VARIABLES = { 'claude-code': 'CLAUDE_CONFIG_DIR', codex: 'CODEX_HOME', opencode: 'OPENCODE_CONFIG', pi: 'PI_CODING_AGENT_DIR' };
const shellWord = value => (/^[A-Za-z0-9_./=:@%+,-]+$/.test(value) ? value : `'${value.replace(/'/g, "'\\''")}'`);
function runCommand(client, profile) {
  const variable = SCOPE_VARIABLES[client.id];
  const scope = variable !== undefined && process.env[variable] ? `${variable}=${shellWord(process.env[variable])} ` : '';
  return `${scope}${client.binary}${['omp', 'codex'].includes(client.id) && profile ? ` --profile ${shellWord(profile)}` : ''}`;
}
function checkProfile(client, profile) {
  if (profile === undefined) return;
  if (!PROFILE.test(profile)) throw usage('profile names are [a-z0-9][a-z0-9._-]{0,63}');
  if (!['omp', 'codex'].includes(client.id)) throw usage('--profile is only supported by OMP and Codex');
}
// Consent before --overwrite: OMP always (its scope lookup may initialize client
// state); other clients only when the scope already holds a config or key.
async function consentToOverwrite(client, profile, flags) {
  if (flags.overwrite) return true;
  let occupied = client.id === 'omp';
  if (!occupied) {
    try { const scope = await resolveScope(client, profile); occupied = [scope.stateFile, ...scope.targets].some(exists); } catch { occupied = true; }
  }
  if (!occupied) return false;
  if (!interactive()) {
    throw usage(client.id === 'omp' ? 'OMP setup needs --overwrite without a terminal (its scope lookup may initialize client state)'
      : `${client.label} is already set up here; add --overwrite to replace its gateway settings and key`);
  }
  const question = client.id === 'omp'
    ? 'Set up OMP here? Existing gateway settings and key in this scope are replaced; OMP may initialize its state'
    : `Replace the ${client.label} gateway settings and key in this scope? Unrelated settings stay intact`;
  if (await confirm(question)) return true;
  out(`Left ${client.label} alone; no user files changed.`);
  return null;
}
async function configure(session, client, flags, view = null) {
  checkProfile(client, flags.profile);
  if (flags.model !== undefined && !MODEL_ID.test(flags.model)) throw usage('model ids are 1-256 printable ASCII characters without spaces');
  if (view === null && screenOutput === null) header(session);
  const overwrite = await consentToOverwrite(client, flags.profile, flags);
  if (overwrite === null) return false;
  const apply = async () => {
    await runSetup(session, client, 'configure', [
      '--new-key', ...(overwrite ? ['--overwrite'] : []), ...(flags.model !== undefined ? ['--model', flags.model] : []), ...profileArgs(flags.profile),
    ], true);
    done('Configured', flags.profile ? `${client.label} (${flags.profile})` : client.label);
    done('Gateway', session.endpoint);
    try {
      const state = readState((await resolveScope(client, flags.profile)).stateFile, client.id);
      if (state?.model ?? flags.model) done('Model', state?.model ?? flags.model);
    } catch (error) {
      if (workContext.getStore()?.signal.aborted) throw new Interrupt();
      warn(`Client configured; could not read its saved model: ${error.message}`);
    }
    done('Key', 'staged');
    done('Run', runCommand(client, flags.profile));
    return true;
  };
  const label = `Configure ${client.label}`;
  return view === null ? runAction(label, apply) : runProgress(view, label, apply);
}
async function switchScope(session, client, action, flags) {
  checkProfile(client, flags.profile);
  return runAction(`${action} ${client.label}`, async () => {
    if (action === 'enable') {
      const state = readState((await resolveScope(client, flags.profile)).stateFile, client.id);
      if (state?.gateway && state.gateway !== (loadSession('prod')?.endpoint ?? PROD_ENDPOINT)) await requireProdDev();
    }
    await runSetup(session, client, action, profileArgs(flags.profile), false);
    done({ enable: 'Enabled', disable: 'Disabled', unset: 'Unset' }[action], flags.profile ? `${client.label} (${flags.profile})` : client.label);
  });
}

// ── served models ───────────────────────────────────────────────────────────
// /v1/models lists provider-qualified ids; clients take the raw provider id
// (request_model_id when the gateway names one), OMP its own provider/id selector.
export function servedModels(catalog, client) {
  if (!record(catalog) || !Array.isArray(catalog.data)) throw new CliError('the gateway model catalog is not in the expected shape');
  const models = [];
  for (const card of catalog.data) {
    if (!record(card) || typeof card.id !== 'string' || !client.providers.includes(card.owned_by)) continue;
    const suffix = card.id.startsWith(`${card.owned_by}/`) ? card.id.slice(card.owned_by.length + 1) : card.id;
    const id = client.id !== 'omp' && typeof card.request_model_id === 'string' ? card.request_model_id : suffix;
    if (!MODEL_ID.test(id)) continue;
    models.push({ id, provider: card.owned_by, name: typeof card.display_name === 'string' ? card.display_name : id });
  }
  if (models.length === 0) throw new CliError(`the gateway serves no models for ${client.label}`);
  return models;
}
export function renderModels(models, current) {
  return table(['model', 'provider', 'name', ''], models.map(model => [
    model.id, model.provider, model.name, current !== null && model.id === current ? 'current' : '',
  ]));
}
// The raw provider id of a saved selector: the provider prefix and an OMP
// effort suffix (anthropic/claude-haiku-4-5:low) are not part of the id.
export const rawModelId = selector => selector.slice(selector.lastIndexOf('/') + 1).split(':')[0];
const modelOptions = (models, current) => models.map(entry => ({
  value: entry.id, label: entry.id,
  hint: [PROVIDER_LABELS[entry.provider] ?? entry.provider, entry.name !== entry.id ? entry.name : '', entry.id === current ? 'current' : ''].filter(Boolean).join(` ${glyph.dot} `),
}));
const currentModelId = state => (state?.model ? rawModelId(state.model) : null);

// ── renderers ───────────────────────────────────────────────────────────────
const number = value => (typeof value === 'number' && Number.isFinite(value) ? value : null);
const USAGE_CATEGORIES = [
  ['input', 'input'], ['cache_write', 'cache write'], ['cache_read', 'cache read'],
  ['output_completion', 'completion'], ['thinking', 'thinking'], ['total', 'total'],
  ['cache_write_5m', 'cache write 5m'], ['cache_write_1h', 'cache write 1h'],
  ['orchestration_input', 'orchestration input'], ['orchestration_cache_read', 'orchestration read'], ['orchestration_output', 'orchestration out'],
];
// One aligned table: a section per provider (all providers first) with the
// token categories down and the windows across. Counts only; cost is metered
// elsewhere. A window without ledger coverage shows — and is named below.
export function renderUsage(payload) {
  const bucket = value => record(value) && record(value.tokens);
  if (!record(payload) || !record(payload.windows)
    || WINDOWS.some(key => !bucket(payload.windows[key]) || !record(payload.windows[key].providers)
      || Object.values(payload.windows[key].providers).some(value => !bucket(value)))) {
    throw new CliError('the usage payload is not in the expected shape');
  }
  const count = value => number(value) === null ? '—' : integer(value);
  // A provider absent from a covered window used no tokens in it; a category
  // the payload leaves out of an existing bucket was not measured.
  const blank = key => (number(payload.windows[key].tokens.total) === null ? null : 0);
  const cell = (bucket, key, category) => (bucket === undefined ? blank(key) : Object.hasOwn(bucket.tokens, category) ? bucket.tokens[category] : null);
  const gap = ['', '', '', '', ''];
  const section = (title, pick) => [
    [title, '', '', '', ''],
    ...USAGE_CATEGORIES.filter(([category]) => WINDOWS.some(key => Object.hasOwn(pick(key)?.tokens ?? {}, category)))
      .map(([category, label]) => [`  ${label}`, ...WINDOWS.map(key => count(cell(pick(key), key, category)))]),
  ];
  const providers = [...new Set(WINDOWS.flatMap(key => Object.keys(payload.windows[key].providers)))].sort((left, right) => left.localeCompare(right));
  const rows = [
    ...section('all providers', key => payload.windows[key]),
    ...providers.flatMap(provider => [gap, ...section(provider, key => payload.windows[key].providers[provider])]),
  ];
  const coverage = WINDOWS.map(key => {
    const status = payload.coverage?.windows?.[key]?.status;
    return status === 'unavailable' ? `${key}: unavailable` : status === 'partial' ? `${key}: partial history` : null;
  }).filter(line => line !== null);
  return table(['', ...WINDOWS], rows, new Set([1, 2, 3, 4])) + (coverage.length > 0 ? `\n\n${coverage.join(`  ${glyph.dot}  `)}` : '');
}
export function renderCapacity(payload, nowMs = Date.now()) {
  if (!record(payload) || !Array.isArray(payload.providers)) throw new CliError('the capacity payload is not in the expected shape');
  const rows = [];
  for (const provider of payload.providers) {
    if (!record(provider)) continue;
    const label = typeof provider.label === 'string' ? provider.label : String(provider.id);
    const eligible = number(provider.eligible) === null ? '—' : `${provider.eligible} / ${number(provider.accounts) ?? '—'}`;
    const reset = countdown(provider.nextResetMs, nowMs);
    const metrics = provider.unavailable === true || !Array.isArray(provider.metrics) ? [] : provider.metrics.filter(record);
    if (metrics.length === 0) { rows.push([label, 'unavailable', '—', '—', '—', eligible, reset]); continue; }
    metrics.forEach((metric, index) => {
      const known = metric.known === true && number(metric.used) !== null && number(metric.total) !== null;
      rows.push([
        index === 0 ? label : '', String(metric.label ?? metric.id),
        known ? amount(metric.used) : '—',
        number(metric.total) === null ? '—' : amount(metric.total),
        known && number(metric.overall) !== null ? percent(metric.overall) : '—',
        index === 0 ? eligible : '', index === 0 ? reset : '',
      ]);
    });
  }
  const rendered = table(['provider', 'metric', 'used', 'total', 'used %', 'eligible', 'reset'], rows, new Set([2, 3, 4]));
  if (payload.stale === true) {
    const at = number(payload.generatedAt) === null ? null : new Date(payload.generatedAt).toISOString().slice(0, 16).replace('T', ' ');
    return `${rendered}\nstale${at === null ? '' : ` ${glyph.dot} as of ${at}Z`}`;
  }
  return rendered;
}
export function renderConnections(payload, nowMs = Date.now()) {
  if (!record(payload) || !Array.isArray(payload.connections)) throw new CliError('the connections payload is not in the expected shape');
  const rows = payload.connections.filter(record).map(connection => [
    PROVIDER_LABELS[connection.provider] ?? String(connection.provider),
    connection.email ?? '—',
    [...new Set([connection.plan, connection.kind].filter(value => typeof value === 'string' && value !== ''))].join(` ${glyph.dot} `) || '—',
    connection.workerId ?? '—',
    String(connection.state ?? '—'),
    number(connection.weeklyUsedFraction) === null ? '—' : percent(connection.weeklyUsedFraction),
    number(connection.fableUsedFraction) === null ? '—' : percent(connection.fableUsedFraction),
    countdown(connection.resetsAt, nowMs),
  ]);
  return table(['provider', 'account', 'plan', 'worker', 'state', 'weekly', 'fable', 'reset'], rows, new Set([5, 6]));
}

// ── commands ────────────────────────────────────────────────────────────────
function keyRefusal(endpoint, source, status) {
  const host = hostOf(endpoint);
  const lines = status === null ? [`This is not a personal gateway key: ${KEY_SHAPE} (provider API keys, box leases and the gateway root do not work here).`]
    : [`${host} refused this key (HTTP ${status}).`,
      source === 'env' ? `  The exported AGENT_AUTH_TOKEN is not a key ${host} recognizes.` : `  ${host} does not recognize the key you pasted.`];
  lines.push(`  Mint a key for ${host} in its console (${endpoint}/admin) and paste that one.`);
  return lines.join('\n');
}
function validateMe(value) {
  if (!record(value) || typeof value.name !== 'string' || value.name === '' || !ROLES.has(value.role)
    || (value.email !== null && typeof value.email !== 'string')) {
    throw new CliError('the gateway answered /admin/api/cli/me with an unexpected shape');
  }
  return { name: value.name, role: value.role, email: value.email, identityClass: identityClassOf(value.identityClass) };
}
const isProdDev = identity => identity?.identityClass === 'internal' && ['owner', 'admin'].includes(identity.role);
// A second gateway is a developer feature: the stored prod key must still be
// accepted by prod's gateway and belong to an internal owner or admin.
async function requireProdDev(view = null) {
  const prod = loadSession('prod');
  if (prod === null) throw new CliError('Prod login required for another gateway; run genesis login --environment prod first');
  const check = async () => {
    let identity;
    try { identity = await request(prod.endpoint, prod.token, 'GET', '/admin/api/cli/me'); } catch (error) {
      if (error instanceof HttpError && [401, 403].includes(error.status)) {
        throw new CliError('Prod no longer accepts the stored key; run genesis login --environment prod again');
      }
      throw error;
    }
    validateMe(identity);
    if (!isProdDev(identity)) throw new CliError('Another gateway requires an internal Prod owner or admin');
  };
  return view === null || screenOutput !== null ? check() : runProgress(view, 'Checking Prod access', check);
}
async function reachable(endpoint) {
  try {
    await request(endpoint, null, 'GET', '/healthz', undefined, 20_000);
    return null;
  } catch (error) {
    if (error instanceof HttpError) { warn(`${endpoint}/healthz answered HTTP ${error.status}; continuing, but this may not be a gateway endpoint`); return null; }
    return error.message;
  }
}
// Log into one environment: its gateway URL (a prompt offers the stored one,
// or the canonical gateway for prod) and its own personal key. `--url` sets
// the URL unattended; prod without a URL uses its default, staging refuses.
export async function login(flags, view = null) {
  const store = loadStore();
  const environment = environmentId(flags.environment ?? store.environment);
  const label = environmentLabel(environment);
  let endpoint = flags.url === undefined ? store.sessions[environment]?.endpoint ?? ENVIRONMENTS[environment].endpoint : environmentEndpoint(flags.url);
  if (environment !== 'prod') await requireProdDev(view);
  const validateUrl = value => { try { return { value: environmentEndpoint(value) }; } catch (error) { return { error: error.message }; } };
  if (flags.url === undefined && interactive()) {
    done('Environment', label);
    endpoint = await ask(`${label} gateway URL`, validateUrl, 'Gateway', endpoint ?? null);
  } else if (endpoint === undefined) {
    throw usage(`${label} is not configured; run genesis login --environment ${environment} --url URL with its own AGENT_AUTH_TOKEN`);
  }
  let token = process.env.AGENT_AUTH_TOKEN ?? '';
  if (token !== '' && interactive() && Object.entries(store.sessions).some(([other, session]) => other !== environment && session.token === token)) token = '';
  const source = token === '' ? 'entered' : 'env';
  if (token === '') {
    if (!interactive()) throw usage(`${label} login needs AGENT_AUTH_TOKEN or a terminal to enter its key`);
    if (flags.url !== undefined) { done('Environment', label); done('Gateway', endpoint); }
    token = await secret(`${label} key`, 'Key');
  }
  let identity;
  for (let attempts = 0; ; attempts++) {
    let refusal = null;
    if (!acceptKey(token)) refusal = keyRefusal(endpoint, source, null);
    else {
      checkSessionIsolation(store, environment, endpoint, token);
      const check = async () => {
        if (environment !== 'prod') await requireProdDev();
        const problem = await reachable(endpoint);
        if (problem !== null) throw new CliError(problem);
        done('Gateway', endpoint);
        return validateMe(await request(endpoint, token, 'GET', '/admin/api/cli/me'));
      };
      try { identity = await (view === null ? check() : runProgress(view, 'Checking gateway and key', check)); break; } catch (error) {
        if (!(error instanceof HttpError) || ![401, 403].includes(error.status)) throw error;
        refusal = keyRefusal(endpoint, source, error.status);
      }
    }
    if (!interactive() || source === 'env' || attempts >= 2) throw new CliError(refusal);
    if (await selectScreen({ title: 'Key refused', body: refusal, options: [{ value: 'retry', label: 'Paste a different key' }, backOption] }) !== 'retry') {
      throw new CliError('Left the login alone; nothing was stored.');
    }
    token = await secret(`${environmentLabel(environment)} key`, 'Key');
  }
  const session = { environment, endpoint, token, ...identity };
  saveSession(session);
  if (view === null) done('Logged in', sessionIdentity(session));
  else view.body = `Logged in ${glyph.dot} ${sessionIdentity(session)}\nKey stored`;
  return session;
}
function logout(flags) {
  const environment = clearSession(flags.environment);
  done('Logged out', environmentLabel(environment));
}

// ── apply ───────────────────────────────────────────────────────────────────
// Point every discoverable scope of an installed client at the selected
// environment: each is configured with that gateway and key (a foreign scope
// is retargeted, a connected one re-staged), keeps its saved model when this
// gateway serves it, and is disabled again when it was disabled.
async function applyEnvironment(session, flags, view = null) {
  // Consent comes before scope discovery: OMP's scope lookup may initialize
  // its state, so only the installed binaries are named here.
  const clients = CLIENTS.filter(client => installed(client.binary));
  if (clients.length === 0) throw new CliError(`none of ${CLIENTS.map(client => client.label).join(', ')} is installed here`);
  const names = clients.map(client => client.label).join(', ');
  const label = environmentLabel(session.environment);
  if (view === null && screenOutput === null) header(session);
  if (!flags.overwrite) {
    if (!interactive()) throw usage(`apply needs --overwrite without a terminal; it replaces the gateway settings and keys of ${names}`);
    if (!(await confirm(`Configure ${names} for ${label} (${session.endpoint})? Their gateway settings and keys are replaced`, true))) {
      out('Left the clients alone; no user files changed.');
      return false;
    }
  }
  const work = async () => {
    const rows = (await statusRows(session)).filter(row => row.installed);
    const catalog = await api(session, 'GET', '/v1/models');
    const failed = [];
    for (const row of rows) {
      if (row.problem !== null) { warn(`${row.label} was not checked: ${row.problem}`); failed.push(row); continue; }
      const profile = profileArgs(row.profile || undefined);
      let model = [];
      try {
        const current = currentModelId(row.state);
        if (current !== null && servedModels(catalog, row.client).some(entry => entry.id === current)) model = ['--model', current];
      } catch (error) {
        if (error instanceof Interrupt) throw error;
      }
      try {
        await runSetup(session, row.client, 'configure', ['--new-key', '--overwrite', ...model, ...profile], true);
        if (row.state?.mode === 'disabled') await runSetup(session, row.client, 'disable', profile, false);
        done('Configured', `${row.label}${model.length > 0 ? ` ${glyph.dot} ${model[1]}` : ''}${row.state?.mode === 'disabled' ? ` ${glyph.dot} disabled` : ''}`);
      } catch (error) {
        if (error instanceof Interrupt) throw error;
        if (error.message) warn(error.message);
        failed.push(row);
      }
    }
    if (failed.length > 0) {
      throw new CliError(`${failed.length} of ${rows.length} clients not configured: ${failed.map(row => row.label).join(', ')}`
        + `${rows.length > failed.length ? `\n  Configured: ${rows.filter(row => !failed.includes(row)).map(row => row.label).join(', ')}` : ''}`);
    }
    done('Gateway', session.endpoint);
    done('Key', 'staged');
    return true;
  };
  return view === null ? runAction(`Apply ${label}`, work) : runProgress(view, `Apply ${label}`, work);
}

// ── setup ───────────────────────────────────────────────────────────────────
// The installer's walkthrough, prod only: log in (URL and key), select prod,
// configure the installed clients for it, then open the dashboard. Rerun any
// time; a stored login that the gateway still accepts is kept.
async function setup(flags) {
  if (flags.environment !== undefined && flags.environment !== 'prod') throw usage('setup creates prod; use genesis environment staging for a second gateway');
  if (!interactive()) throw usage('setup needs a terminal; run genesis login and genesis apply --overwrite instead');
  out(paint('1', 'Set up Prod'));
  let session = flags.url === undefined ? loadSession('prod') : null;
  if (session !== null) {
    try { validateMe(await request(session.endpoint, session.token, 'GET', '/admin/api/cli/me')); done('Logged in', sessionIdentity(session)); } catch (error) {
      if (!(error instanceof HttpError) || ![401, 403].includes(error.status)) throw error;
      warn(`${hostOf(session.endpoint)} no longer accepts the stored key`);
      session = null;
    }
  }
  if (session === null) session = await login({ environment: 'prod', url: flags.url });
  const store = loadStore();
  if (store.environment !== 'prod') {
    store.environment = 'prod';
    writeSessionText(JSON.stringify(store, null, 2) + '\n');
  }
  await applyEnvironment(session, flags);
  return dashboard({ environment: 'prod' });
}
async function status(session, flags) {
  header(session);
  out('');
  out(renderStatus(await statusRows(session, flags.profile), process.stdout.isTTY === true ? columns() : Infinity));
}
async function model(session, client, requested, flags) {
  checkProfile(client, flags.profile);
  return runAction(`${client.label} Model`, async view => {
    if (view !== null) view.identity = sessionIdentity(session);
    const load = async () => {
      const models = servedModels(await api(session, 'GET', '/v1/models'), client);
      let current = null;
      try { current = currentModelId(readState((await resolveScope(client, flags.profile)).stateFile, client.id)); } catch { current = null; }
      return { models, current };
    };
    const { models, current } = await (view === null ? load() : runProgress(view, 'Loading models', load));
    if (requested !== undefined) {
      if (!models.some(entry => entry.id === requested)) throw new CliError(`model ${requested} is not served for ${client.label}; served models: ${models.map(entry => entry.id).join(', ')}`);
      return configure(session, client, { ...flags, model: requested }, view);
    }
    if (view === null) { out(renderModels(models, current)); return true; }
    const choice = await selectScreen({
      ...view,
      options: [...modelOptions(models, current), backOption],
    });
    if (choice === BACK) return false;
    return configure(session, client, { ...flags, model: choice }, view);
  }, true);
}
async function showUsage(session, flags) {
  const payload = await api(session, 'GET', '/admin/api/cli/usage');
  if (flags.json) { out(JSON.stringify(payload, null, 2)); return; }
  out(paint('1', `usage ${glyph.dot} ${environmentLabel(session.environment)} ${glyph.dot} ${session.name}`));
  out('');
  out(renderUsage(payload));
}
async function showCapacity(session) {
  out(renderCapacity(await api(session, 'GET', '/admin/api/cli/capacity')));
}
async function showConnections(session) {
  out(renderConnections(await api(session, 'GET', '/admin/api/cli/connections')));
}
const SMOKE_PROMPT = 'Reply with exactly: pong';
const SMOKE_ROUTES = { anthropic: '/anthropic/v1/messages', 'openai-codex': '/openai-codex/v1/responses' };
const SMOKE_TERMINAL = { anthropic: 'message_stop', 'openai-codex': 'response.completed' };
function smokeSse(text) {
  return String(text).split(/\r?\n\r?\n/).flatMap(block => {
    let event = null;
    const data = [];
    for (const line of block.split(/\r?\n/)) {
      if (line.startsWith('event:')) event = line.slice(6).trim();
      else if (line.startsWith('data:')) data.push(line.slice(5).trim());
    }
    if (data.length === 0) return [];
    let value = null;
    try { value = JSON.parse(data.join('\n')); } catch { value = null; }
    return [{ event: event ?? value?.type ?? null, value }];
  });
}
// The provider's cheapest served model by list price; a card without a price
// only wins when nothing priced is served, and the first such card wins.
function smokeModel(catalog, provider) {
  let pick = null;
  let pickPrice = Infinity;
  for (const card of catalog.data) {
    if (!record(card) || card.owned_by !== provider || typeof card.id !== 'string') continue;
    const id = typeof card.request_model_id === 'string' ? card.request_model_id : rawModelId(card.id);
    if (!MODEL_ID.test(id)) continue;
    const price = record(card.cost) && Number.isFinite(card.cost.input) && Number.isFinite(card.cost.output) ? card.cost.input + card.cost.output : Infinity;
    if (pick === null || price < pickPrice) { pick = id; pickPrice = price; }
  }
  return pick;
}
// /healthz: `admission` is the gate's own record ({accepting, mode, holdId…}
// on the authority, plus `mode` on a serving replica); its absence is
// reported as unknown, never as accepting.
function smokeHealth(value) {
  if (!record(value) || value.ok !== true) throw new CliError('gateway is not ready');
  const ready = value.ready === false ? `not ready${typeof value.reason === 'string' ? ` (${value.reason})` : ''}` : 'ready';
  const workers = Number.isFinite(value.workers) ? value.workers : '—';
  const admission = !record(value.admission) ? 'unknown'
    : typeof value.admission.mode === 'string' ? value.admission.mode
      : value.admission.accepting === true ? 'accepting' : value.admission.accepting === false ? 'holding' : 'unknown';
  return `ok ${glyph.dot} ${ready} ${glyph.dot} workers ${workers} ${glyph.dot} admission ${admission}`;
}
function smokeModels(catalog) {
  if (!record(catalog) || !Array.isArray(catalog.data)) throw new CliError('the gateway model catalog is not in the expected shape');
  const served = catalog.data.filter(card => record(card) && typeof card.id === 'string');
  if (served.length === 0) throw new CliError('no models are served');
  const count = provider => served.filter(card => card.owned_by === provider).length;
  return `${served.length} served ${glyph.dot} anthropic ${count('anthropic')} ${glyph.dot} openai-codex ${count('openai-codex')}`;
}
// A refusal's reason, in either JSON form the doors send ({error: "…"} or
// {error: {message}}) or a stream's error/response.failed payload; redacted
// before it is shortened, so a cut can never leave the head of a key behind.
const smokeReason = (...values) => {
  for (const value of values) {
    const text = typeof value?.error === 'string' ? value.error
      : typeof value?.error?.message === 'string' ? value.error.message
        : typeof value?.message === 'string' ? value.message : null;
    if (text !== null) return redact(text).replace(/\s+/g, ' ').trim().slice(0, 200);
  }
  return null;
};
async function smokeCall(session, provider, model) {
  const endpoint = session.endpoint;
  const headers = { Accept: 'text/event-stream', Authorization: `Bearer ${session.token}`, 'Content-Type': 'application/json' };
  const body = provider === 'anthropic'
    ? { model, max_tokens: 8, stream: true, messages: [{ role: 'user', content: SMOKE_PROMPT }] }
    : { model, stream: true, store: false, instructions: SMOKE_PROMPT, input: [{ role: 'user', content: [{ type: 'input_text', text: SMOKE_PROMPT }] }] };
  const deadline = requestDeadline(HTTP_TIMEOUT_MS);
  const started = performance.now();
  let response;
  try {
    try {
      response = await fetch(`${endpoint}${SMOKE_ROUTES[provider]}`, {
        method: 'POST', headers, body: JSON.stringify(body), redirect: 'manual', signal: deadline.signal,
      });
    } catch (error) {
      throw new CliError(`could not reach ${hostOf(endpoint)}: ${reasonOf(error)}`);
    }
    // First text is the wall time of the first non-empty visible delta as the
    // stream arrives, not the end of the body.
    const textOf = entry => (provider === 'anthropic'
      ? (entry.event === 'content_block_delta' ? entry.value?.delta?.text : undefined)
      : (entry.event === 'response.output_text.delta' ? entry.value?.delta : undefined));
    const isText = entry => typeof textOf(entry) === 'string' && textOf(entry) !== '';
    let text = '';
    let firstAt = null;
    if (response.body !== null) {
      const decoder = new TextDecoder();
      for await (const chunk of response.body) {
        text += decoder.decode(chunk, { stream: true });
        if (firstAt === null && smokeSse(text).some(isText)) firstAt = performance.now();
      }
      text += decoder.decode();
    }
    const events = smokeSse(text);
    let errorBody = null;
    try { errorBody = JSON.parse(text || '{}'); } catch { errorBody = null; }
    const failure = events.find(entry => entry.event === 'error' || entry.event === 'response.failed')?.value;
    const reason = smokeReason(errorBody, failure, failure?.response);
    if (!response.ok) throw new CliError(`HTTP ${response.status}: ${reason ?? 'request failed'}`);
    const terminalEvent = events.at(-1)?.event;
    if (terminalEvent !== SMOKE_TERMINAL[provider]) {
      throw new CliError(`stream ended with ${terminalEvent ?? 'no event'}, not ${SMOKE_TERMINAL[provider]}${reason === null ? '' : `: ${reason}`}`);
    }
    const reply = events.map(entry => (typeof textOf(entry) === 'string' ? textOf(entry) : '')).join('');
    const lastValue = events.at(-1)?.value;
    const usage = provider === 'anthropic'
      ? {
        input: events.find(entry => entry.event === 'message_start')?.value?.message?.usage?.input_tokens ?? null,
        output: events.find(entry => entry.event === 'message_delta')?.value?.usage?.output_tokens ?? null,
      }
      : {
        input: lastValue?.response?.usage?.input_tokens ?? null,
        output: lastValue?.response?.usage?.output_tokens ?? null,
      };
    if (provider === 'openai-codex' && lastValue?.response?.status !== 'completed') throw new CliError('response.completed did not report completed');
    const total = performance.now() - started;
    const first = firstAt === null ? null : firstAt - started;
    return {
      status: response.status,
      first, total, terminal: terminalEvent, reply: redact(reply).trim().slice(0, 60),
      input: usage.input, output: usage.output,
    };
  } finally { deadline.close(); }
}
const smokeSeconds = value => value === null ? '—' : `${(value / 1000).toFixed(1)}s`;
const smokeTokens = value => Number.isFinite(value) ? String(value) : '—';
// Health, login, the catalog, then one real streamed call per provider. A
// provider the catalog does not serve is a failed check, never a missing
// one: an all-green smoke always made both calls.
async function smoke(session, flags, view = null) {
  const execute = async () => {
    const checks = [];
    const add = async (name, work, format) => {
      const started = performance.now();
      try {
        const value = await work();
        const check = { name, ok: true, ms: Math.round(performance.now() - started), detail: format(value) };
        checks.push(check);
        if (!flags.json) done(name, check.detail);
      } catch (error) {
        const detail = error instanceof CliError ? error.message : String(error?.message ?? error);
        checks.push({ name, ok: false, ms: Math.round(performance.now() - started), detail });
        if (!flags.json) warn(`${name}  ${detail}`);
      }
      return checks.at(-1);
    };
    await add('health', () => request(session.endpoint, null, 'GET', '/healthz'), smokeHealth);
    await add('login', () => api(session, 'GET', '/admin/api/cli/me'), value => {
      const identity = validateMe(value);
      return `${identity.name} ${glyph.dot} ${identity.role} ${glyph.dot} ${identity.identityClass ?? 'unclassified'}`;
    });
    let catalog = null;
    const models = await add('models', async () => {
      catalog = await api(session, 'GET', '/v1/models');
      return smokeModels(catalog);
    }, value => value);
    for (const provider of Object.keys(SMOKE_ROUTES)) {
      const model = models.ok ? smokeModel(catalog, provider) : null;
      await add(provider, () => {
        if (model === null) throw new CliError(models.ok ? 'no served model' : 'no model catalog');
        return smokeCall(session, provider, model);
      }, value =>
        `${model} ${glyph.dot} HTTP ${value.status} ${glyph.dot} first text ${smokeSeconds(value.first)} ${glyph.dot} total ${smokeSeconds(value.total)} ${glyph.dot} terminal ${value.terminal} ${glyph.dot} "${value.reply}" ${glyph.dot} ${smokeTokens(value.input)}/${smokeTokens(value.output)} tokens`);
    }
    const passed = checks.filter(check => check.ok).length;
    if (!flags.json) out(`${passed} of ${checks.length} checks passed`);
    return { environment: session.environment, endpoint: session.endpoint, ok: passed === checks.length, checks };
  };
  const report = view === null || flags.json ? await execute() : await runProgress(view, 'Smoke', execute);
  if (flags.json) out(JSON.stringify(report, null, 2));
  if (!report.ok) throw new CliError(`${report.checks.filter(check => !check.ok).length} of ${report.checks.length} checks failed`);
  return report;
}

// ── add connection ──────────────────────────────────────────────────────────
// A port of login-runtime/local-admin.mjs: the worker runs the OAuth exchange;
// this process serves one page on 127.0.0.1 that picks the provider and
// worker, starts the link, shows the authorization URL or device code and
// reflects the link as it settles; it relays the browser's callback
// (Anthropic) and reports every settled link in the terminal. It never opens
// a browser: the user opens the printed URL in one of their choice, and
// nothing starts without a click on the page.
function validateLink(value) {
  if (!record(value) || typeof value.attemptId !== 'string' || !ATTEMPT_ID.test(value.attemptId)
    || typeof value.provider !== 'string' || typeof value.workerId !== 'string' || !LINK_STATUSES.has(value.status)
    || (value.url !== null && (typeof value.url !== 'string' || !value.url.startsWith('https://')))
    || (value.userCode !== null && typeof value.userCode !== 'string')
    || (value.error !== null && typeof value.error !== 'string')) {
    throw new CliError('the gateway returned an invalid OAuth link');
  }
  return { attemptId: value.attemptId, provider: value.provider, workerId: value.workerId, status: value.status, url: value.url, userCode: value.userCode, error: value.error };
}
const linkBody = (link, extra = {}) => ({ workerId: link.workerId, attemptId: link.attemptId, provider: link.provider, ...extra });
// Every local response is uncacheable and sized; JSON passes through redact()
// like the terminal does, since a gateway error may quote the key.
function send(res, status, type, body, sent) {
  res.writeHead(status, { 'Content-Type': `${type}; charset=utf-8`, 'Cache-Control': 'no-store', 'Content-Length': Buffer.byteLength(body) });
  res.end(body, sent);
}
const sendJson = (res, status, value) => send(res, status, 'application/json', redact(JSON.stringify(value)));
// A request body of at most LOCAL_BODY_CAP bytes; a larger one is cut off.
function readBody(req) {
  return new Promise((resolve, reject) => {
    const chunks = [];
    let size = 0;
    req.on('data', chunk => {
      size += chunk.length;
      if (size > LOCAL_BODY_CAP) { reject(new CliError('body too large')); req.destroy(); return; }
      chunks.push(chunk);
    });
    req.on('end', () => resolve(Buffer.concat(chunks).toString('utf8')));
    req.on('error', reject);
  });
}
// JSON for the page's script: a < never ends the script element.
const inline = value => JSON.stringify(value).replace(/</g, '\\u003c');
function callbackPage(ok) {
  const body = `<!doctype html><meta charset="utf-8"><title>genesis</title><body>${ok ? 'Authorization received. Return to the terminal.' : 'Connection failed. Return to the terminal.'}</body>`;
  return { status: ok ? 200 : 400, body };
}
function listen(server, host, port) {
  return new Promise((resolve, reject) => {
    server.once('error', reject);
    server.listen(port, host, () => { server.off('error', reject); resolve(); });
  });
}
// Anthropic redirects the browser to http://localhost:<port>/callback; the
// worker's authorization URL names the port and a 32-hex state. The code is
// forwarded to link/input once; the servers close after that answer is sent.
// A request line the handler cannot parse gets the failure page; anything
// else that goes wrong in it is reported, never thrown at the server.
async function anthropicCallback(session, link, onLink, onError) {
  const authorize = new URL(link.url);
  const redirect = authorize.searchParams.get('redirect_uri');
  const expectedState = authorize.searchParams.get('state');
  if (redirect === null || expectedState === null || !/^[0-9a-f]{32}$/.test(expectedState)) throw new CliError('the worker returned an invalid Anthropic authorization URL');
  const callbackUrl = new URL(redirect);
  const port = Number(callbackUrl.port || 80);
  const servers = [];
  let consumed = false;
  const close = () => { for (const server of servers) { server.closeAllConnections?.(); server.close(); } servers.length = 0; };
  const handler = async (req, res) => {
    let callback = null;
    try { callback = new URL(req.url ?? '/', callbackUrl.origin); } catch { /* the failure page */ }
    const local = ['127.0.0.1', '::1', '::ffff:127.0.0.1'].includes(req.socket.remoteAddress);
    let page = callbackPage(false);
    if (callback !== null && req.method === 'GET' && local && callback.pathname === '/callback' && callback.searchParams.get('state') === expectedState
      && callback.searchParams.get('code') !== null && !consumed) {
      consumed = true;
      try { onLink(validateLink(await api(session, 'POST', '/admin/api/cli/link/input', linkBody(link, { input: callback.toString() })))); page = callbackPage(true); }
      catch (error) { onError(error.message); }
    }
    res.setHeader('Connection', 'close');
    send(res, page.status, 'text/html', page.body, () => { if (consumed) close(); });
  };
  const serve = () => http.createServer((req, res) => { handler(req, res).catch(error => onError(error.message)); });
  const ipv4 = serve();
  try { await listen(ipv4, '127.0.0.1', port); } catch (error) {
    ipv4.close();
    if (error?.code === 'EADDRINUSE' || error?.code === 'EACCES') throw new CliError(`port ${port} on 127.0.0.1 is ${error.code === 'EACCES' ? 'not permitted' : 'in use'}; the Anthropic callback needs it, so free it and try again`);
    throw error;
  }
  servers.push(ipv4);
  const ipv6 = serve();
  try { await listen(ipv6, '::1', port); servers.push(ipv6); } catch { ipv6.close(); }
  return close;
}
// The page: the signed-in identity, the current connections, the provider and
// worker picks, one link at a time with its Open provider link or device code
// (copied with one click), and the state poll every LINK_POLL_MS. Every
// /api/* request carries the per-process nonce in X-S99-Local.
function launcherPage(session, nonce, preset) {
  return redact(`<!doctype html>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>genesis</title>
<style>
  :root { color-scheme: dark; }
  body { background:#101014; color:#d6d6dc; font:14px/1.6 ui-monospace,monospace; margin:2rem auto; max-width:64rem; padding:0 1rem; }
  button,select { background:#17171d; color:#d6d6dc; border:1px solid #33465e; padding:.35rem .6rem; font:inherit; }
  a { color:#9ecfff; } .muted { color:#7a7a85; } .bad { color:#f0917f; }
  ul { list-style:none; padding:0; } li { border-top:1px solid #24242d; padding:.4rem 0; }
  #authCodeRow { margin:.5rem 0; }
  #authCode { cursor:pointer; user-select:all; overflow-wrap:anywhere; }
</style>
<div id="session" class="muted"></div>
<ul id="connections"></ul>
<select id="provider" aria-label="Provider"></select>
<select id="worker" aria-label="Worker"><option value="">automatic</option></select>
<button id="add" disabled>Add</button> <button id="cancel" disabled>Cancel</button>
<div id="destination"></div>
<div id="link"></div>
<div id="authCodeRow" hidden>
  <button id="authCode" type="button" title="Copy code" aria-label="Copy auth code"></button>
  <button id="copyCode" type="button">Copy</button>
  <span id="copyStatus" role="status"></span>
</div>
<div id="error" class="bad" role="alert"></div>
<script>
const localNonce = ${inline(nonce)};
const labels = ${inline(PROVIDER_LABELS)};
let preset = ${inline(preset)};
document.title = ${inline(`genesis · ${environmentLabel(session.environment)} · ${hostOf(session.endpoint)}`)};
document.querySelector('#session').textContent = ${inline(sessionIdentity(session))};
const $ = selector => document.querySelector(selector);
const esc = value => String(value ?? '').replace(/[&<>"]/g, char => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[char]));
async function api(path, body) {
  const init = body === undefined ? { headers: { 'X-S99-Local': localNonce } }
    : { method: 'POST', headers: { 'Content-Type': 'application/json', 'X-S99-Local': localNonce }, body: JSON.stringify(body) };
  const response = await fetch(path, init);
  const result = await response.json();
  if (!response.ok) throw new Error(result.error || response.status);
  return result;
}
let placement = [];
let provisioning = null;
let link = null;
let wantedWorker = null;
let refreshFailed = false;
const busy = () => link !== null && !['done', 'failed', 'cancelled'].includes(link.status);
function paintLink() {
  const target = $('#link');
  if (link === null) target.textContent = '';
  else {
    const open = link.url && busy() ? ' · <a href="' + esc(link.url) + '" target="_blank" rel="noopener">Open ' + esc(labels[link.provider] || link.provider) + '</a>' : '';
    const error = link.error ? ' · <span class="bad">' + esc(link.error) + '</span>' : '';
    target.innerHTML = esc(labels[link.provider] || link.provider) + ' · ' + esc(link.workerId) + ' · ' + esc(link.status) + open + error;
  }
  const code = busy() && link.userCode ? link.userCode : '';
  const codeButton = $('#authCode');
  $('#authCodeRow').hidden = !code;
  if (codeButton.textContent !== code) { codeButton.textContent = code; $('#copyStatus').textContent = ''; }
  $('#cancel').disabled = !busy();
}
async function copyAuthCode() {
  const code = link?.userCode;
  const attemptId = link?.attemptId;
  if (!code) return;
  let message = 'Copied';
  try { await navigator.clipboard.writeText(code); } catch { message = 'Copy failed'; }
  if (link?.attemptId === attemptId && link?.userCode === code) $('#copyStatus').textContent = message;
}
$('#copyCode').onclick = copyAuthCode;
$('#authCode').onclick = copyAuthCode;
function paintDestination() {
  const next = placement.find(entry => entry.provider === $('#provider').value);
  const destination = $('#destination');
  const workerSelect = $('#worker');
  const wanted = wantedWorker ?? workerSelect.value;
  wantedWorker = null;
  const offered = Array.isArray(next?.availableWorkerIds) ? next.availableWorkerIds.filter(workerId => typeof workerId === 'string') : [];
  const selected = offered.includes(wanted) ? wanted : '';
  workerSelect.innerHTML = '<option value="">' + esc(next?.workerId ? 'automatic · ' + next.workerId : 'automatic') + '</option>'
    + offered.map(workerId => '<option value="' + esc(workerId) + '">' + esc(workerId) + '</option>').join('');
  workerSelect.value = selected;
  workerSelect.disabled = !next?.available || busy();
  if (next === undefined || next.unavailable) { destination.className = 'bad'; destination.textContent = 'topology unavailable'; }
  else if (next.available) { destination.className = ''; destination.textContent = 'next: ' + (selected || next.workerId); }
  else if (['provisioning', 'admitting'].includes(provisioning?.state)) { destination.className = ''; destination.textContent = provisioning.state + ' · ' + provisioning.workerId; }
  else { destination.className = 'bad'; destination.textContent = provisioning?.error || 'no slot'; }
  $('#add').textContent = 'Add' + ($('#provider').value ? ' ' + (labels[$('#provider').value] || $('#provider').value) : '');
  $('#add').disabled = !next?.available || busy();
  paintLink();
}
function paintError(error) {
  paintDestination();
  $('#error').textContent = String(error.message || error);
}
const clearError = () => { $('#error').textContent = ''; };
async function refresh() {
  try {
    const state = await api('/api/state');
    const selector = $('#provider');
    const selectedProvider = selector.value;
    placement = Array.isArray(state.workers?.placement) ? state.workers.placement.filter(entry => typeof entry?.provider === 'string') : [];
    provisioning = state.workers?.provision ?? null;
    const options = placement.map(entry => '<option value="' + esc(entry.provider) + '">' + esc(labels[entry.provider] || entry.provider) + '</option>').join('');
    if (selector.innerHTML !== options) { selector.innerHTML = options; if (placement.some(entry => entry.provider === selectedProvider)) selector.value = selectedProvider; }
    if (preset !== null) {
      if (placement.some(entry => entry.provider === preset.provider)) selector.value = preset.provider;
      wantedWorker = preset.workerId;
      preset = null;
    }
    link = state.link;
    const rows = Array.isArray(state.connections?.connections) ? state.connections.connections.filter(row => row !== null && typeof row === 'object') : [];
    $('#connections').innerHTML = rows.map(row => '<li><b>' + esc(labels[row.provider] || row.provider) + '</b> ' + esc(row.email || row.id)
      + ' <span class="muted">· ' + esc(row.workerId) + ' · ' + esc(row.state) + '</span></li>').join('');
    paintDestination();
    if (refreshFailed) { refreshFailed = false; clearError(); }
  } catch (error) {
    refreshFailed = true;
    paintError(error);
  }
  setTimeout(refresh, ${LINK_POLL_MS});
}
$('#provider').onchange = paintDestination;
$('#add').onclick = () => {
  clearError();
  $('#add').disabled = true;
  api('/api/link/start', { provider: $('#provider').value, workerId: $('#worker').value || null }).then(result => {
    link = result.link;
    if (result.provisioning) {
      provisioning = result.provisioning;
      placement = placement.map(entry => ({ ...entry, available: false, workerId: null, availableWorkerIds: [] }));
    }
    paintDestination();
  }).catch(paintError);
};
$('#cancel').onclick = () => {
  clearError();
  $('#cancel').disabled = true;
  api('/api/link/cancel', {}).then(result => { link = result.link; paintDestination(); }).catch(paintError);
};
refresh();
</script>`);
}
async function addConnection(session, flags, view = null) {
  let port = 0;
  if (flags.port !== undefined) {
    port = /^[0-9]{1,5}$/.test(flags.port) ? Number(flags.port) : 0;
    if (port < 1 || port > 65_535) throw usage('--port takes a number from 1 to 65535; the page is only ever served on 127.0.0.1');
  }
  if (view === null && interactive()) note('Loading connection workers');
  const workersRequest = () => api(session, 'GET', '/admin/api/cli/workers');
  const topology = await (view === null ? workersRequest() : runProgress(view, 'Loading connection workers', workersRequest));
  const placement = record(topology) && Array.isArray(topology.placement) ? topology.placement.filter(record) : [];
  if (placement.length === 0) throw new CliError('worker topology is unavailable; try again shortly');
  // --provider and --worker only preselect on the page; each must name what the topology offers.
  const slots = flags.provider === undefined ? placement : placement.filter(entry => entry.provider === flags.provider);
  if (slots.length === 0) throw usage(`unknown provider ${flags.provider}; use ${placement.map(entry => entry.provider).join(', ')}`);
  const workers = [...new Set(slots.flatMap(entry => [entry.workerId, ...(Array.isArray(entry.availableWorkerIds) ? entry.availableWorkerIds : [])]).filter(id => typeof id === 'string'))];
  if (flags.worker !== undefined && !workers.includes(flags.worker)) throw usage(`unknown worker ${flags.worker}${workers.length === 0 ? '' : `; use ${workers.join(', ')}`}`);
  const nonce = crypto.randomBytes(32).toString('base64url');
  const nonceMatches = value => {
    if (typeof value !== 'string') return false;
    const supplied = Buffer.from(value);
    const expected = Buffer.from(nonce);
    return supplied.length === expected.length && crypto.timingSafeEqual(supplied, expected);
  };
  const page = launcherPage(session, nonce, { provider: flags.provider ?? null, workerId: flags.worker ?? null });
  let link = null;
  let closeCallback = null;
  let starting = null;
  let cancelling = null;
  let closing = false;
  let localUrl = '';
  let cancellationError = null;
  let connected = 0;
  const report = (text, failed = false) => {
    if (view === null) { (failed ? warn : note)(text); return; }
    if (closing) return;
    view.body = `${localUrl}\n\n${text}`;
    renderScreen(view);
  };
  const busy = () => link !== null && !LINK_TERMINAL.has(link.status);
  // Every link answer lands here. A status change is reported in the
  // terminal (a settled link as Connected or a failure, otherwise the new
  // state) and a settled link releases Anthropic's callback port.
  const settle = next => {
    const changed = link === null || next.attemptId !== link.attemptId || next.status !== link.status;
    link = next;
    if (changed && link.status === 'done') {
      connected += 1;
      const where = `${PROVIDER_LABELS[link.provider] ?? link.provider} on ${link.workerId}`;
      if (view === null) done('Connected', where);
      else report(`Connected ${glyph.dot} ${where}`);
    } else if (changed && link.status === 'failed') report(`connection failed${link.error ? `: ${link.error}` : ''}`, true);
    else if (changed) report(`${PROVIDER_LABELS[link.provider] ?? link.provider} ${glyph.dot} ${link.workerId} ${glyph.dot} ${link.status}`);
    if (LINK_TERMINAL.has(link.status) && closeCallback !== null) { closeCallback(); closeCallback = null; }
  };
  // Late polls and callbacks must not revive a cancelled or replaced attempt.
  const adopt = next => { if (!closing && link !== null && !LINK_TERMINAL.has(link.status) && next.attemptId === link.attemptId) settle(next); };
  // A link that has not settled is cancelled on the worker once. When that
  // fails it is marked cancelled here, since the worker's copy is taken over
  // by the next start on it (or ends with its own timeout) and the page must
  // not stay wedged behind it.
  const cancel = async () => {
    if (!busy()) return link;
    cancelling ??= (async () => {
      report(`Cancelling ${glyph.dot} ${PROVIDER_LABELS[link.provider] ?? link.provider}`);
      try { settle(validateLink(await api(session, 'POST', '/admin/api/cli/link/cancel', linkBody(link)))); }
      catch (error) { cancellationError = error.message; report(error.message, true); settle({ ...link, status: 'cancelled', error: error.message }); }
      finally { cancelling = null; }
    })();
    await cancelling;
    return link;
  };
  // Anthropic's callback port is bound before the URL leaves this process,
  // so a browser can never race an unbound port; when it cannot be bound the
  // link is cancelled and kept without its URL.
  const bindCallback = async () => {
    if (closing || !busy() || link.provider !== 'anthropic' || link.url === null || closeCallback !== null) return;
    try { closeCallback = await anthropicCallback(session, link, adopt, text => report(text, true)); }
    catch (error) { await cancel(); settle({ ...link, url: null, error: error.message }); throw error; }
  };
  const refresh = async () => {
    if (closing || !busy()) return;
    const current = link;
    const next = validateLink(await api(session, 'POST', '/admin/api/cli/link/status', linkBody(current)));
    if (link !== current) return;
    adopt(next);
    await bindCallback();
  };
  const start = async (provider, workerId) => {
    if (closing) throw new CliError('shutting down');
    if (starting !== null || busy()) throw new CliError('a connection is already being added');
    cancellationError = null;
    starting = (async () => {
      report(`Starting ${glyph.dot} ${PROVIDER_LABELS[provider] ?? provider}${workerId ? ` on ${workerId}` : ''}`);
      const started = await api(session, 'POST', '/admin/api/cli/link/start', { provider, workerId }, 60_000);
      if (record(started) && record(started.provisioning) && started.workerId === null) {
        report(`${started.provisioning.state} ${glyph.dot} ${started.provisioning.workerId ?? 'worker'}`);
        return { link, provisioning: started.provisioning };
      }
      settle(validateLink(started));
      await bindCallback();
      return { link };
    })();
    try { return await starting; }
    catch (error) { report(`Connection failed: ${error.message}`, true); throw error; }
    finally { starting = null; }
  };
  const server = http.createServer();
  try { await listen(server, '127.0.0.1', port); } catch (error) {
    server.close();
    if (error?.code === 'EADDRINUSE' || error?.code === 'EACCES') throw new CliError(`port ${port} on 127.0.0.1 is ${error.code === 'EACCES' ? 'not permitted' : 'in use'}; pass another --port`);
    throw error;
  }
  const local = `127.0.0.1:${server.address().port}`;
  // The Host must be this bind and, on /api/*, the nonce must match and any
  // Origin must be this page's: a page from anywhere else, or a rebound name,
  // gets 403 and nothing about the link.
  const serve = async (req, res) => {
    if (req.headers.host !== local) { sendJson(res, 403, { error: 'invalid local host' }); return; }
    // Judged on the parsed path: an absolute-form request target would
    // otherwise slip past a prefix test on the raw line.
    let url;
    try { url = new URL(req.url ?? '/', `http://${local}`); } catch { sendJson(res, 400, { error: 'invalid request target' }); return; }
    if (url.origin !== `http://${local}`) { sendJson(res, 403, { error: 'invalid local host' }); return; }
    if (url.pathname.startsWith('/api/') && (!nonceMatches(req.headers['x-s99-local']) || (req.headers.origin !== undefined && req.headers.origin !== `http://${local}`))) {
      sendJson(res, 403, { error: 'local request authentication required' });
      return;
    }
    if (closing) { res.setHeader('Connection', 'close'); sendJson(res, 503, { error: 'shutting down' }); return; }
    if (req.method === 'GET' && url.pathname === '/') { send(res, 200, 'text/html', page); return; }
    if (req.method === 'GET' && url.pathname === '/api/state') {
      const [workers, connections] = await Promise.all([api(session, 'GET', '/admin/api/cli/workers'), api(session, 'GET', '/admin/api/cli/connections'), refresh()]);
      sendJson(res, 200, { workers, connections, link });
      return;
    }
    if (req.method === 'POST' && url.pathname === '/api/link/start') {
      const body = JSON.parse(await readBody(req));
      if (!record(body) || typeof body.provider !== 'string' || (body.workerId !== null && typeof body.workerId !== 'string')) throw new CliError('invalid link request');
      const result = await start(body.provider, body.workerId);
      sendJson(res, result.provisioning ? 202 : 200, result);
      return;
    }
    if (req.method === 'POST' && url.pathname === '/api/link/cancel') { await readBody(req); sendJson(res, 200, { link: await cancel() }); return; }
    sendJson(res, 404, { error: 'not found' });
  };
  server.on('request', (req, res) => { serve(req, res).catch(error => sendJson(res, error instanceof HttpError ? error.status : 400, { error: String(error?.message ?? error) })); });
  localUrl = `open http://${local}/`;
  const navigation = new AbortController();
  let finish;
  let shutdownTask = null;
  let interrupted = false;
  const finished = new Promise(resolve => { finish = resolve; });
  // Back and signals share one cleanup. A start already in flight is joined
  // before cancelling, so leaving cannot orphan its newly returned attempt.
  const shutdown = () => {
    if (shutdownTask !== null) return shutdownTask;
    closing = true;
    server.close();
    server.closeIdleConnections?.();
    if (closeCallback !== null) { closeCallback(); closeCallback = null; }
    shutdownTask = (async () => {
      await starting?.catch(() => {});
      await cancel();
      if (closeCallback !== null) { closeCallback(); closeCallback = null; }
      server.closeAllConnections?.();
      finish();
      return cancellationError;
    })();
    return shutdownTask;
  };
  const interrupt = () => {
    if (interrupted) { closeTerminal(); process.exit(130); }
    interrupted = true;
    navigation.abort();
    void shutdown();
  };
  process.on('SIGINT', interrupt);
  process.on('SIGTERM', interrupt);
  try {
    if (view === null) { header(session); out(localUrl); await finished; }
    else {
      view.body = localUrl;
      view.options = [backOption];
      try { await selectScreen(view, navigation.signal); }
      catch (error) { if (error instanceof Interrupt) interrupted = true; else throw error; }
    }
  } finally {
    const cleanup = shutdown();
    if (view === null || interrupted) await cleanup;
    process.off('SIGINT', interrupt);
    process.off('SIGTERM', interrupt);
  }
  if (interrupted) throw new Interrupt();
  return { cleanup: shutdownTask, connected: () => connected };
}

// ── key rotation ────────────────────────────────────────────────────────────
// The server re-mints the key under the same name and revokes the old row.
// The new session is committed (on disk and, through `commit`, in memory)
// before any scope is touched. Every enumerable scope configured for this
// endpoint is then staged again with the new key and its saved model; a scope
// that was disabled is disabled again. configure and disable are judged
// apart, since a failed configure leaves the old key in place while a failed
// disable leaves the new key enabled; each such scope, each scope that could
// not be checked, and what is never enumerated (OMP profiles) is reported
// after, and any of the first two exits 1 with the new session kept.
async function rotateToken(session, flags, commit = () => {}) {
  if (!flags.yes) {
    if (!interactive()) throw usage('token rotate needs --yes without a terminal');
    if (!(await confirm(`Rotate the ${environmentLabel(session.environment)} key for ${session.name}? The current key stops working everywhere`))) { out('Left the key alone.'); return; }
  }
  return runAction('Rotate key', async () => {
    const rows = await statusRows(session);
    const scopes = rows.filter(row => row.state !== null && row.state.gateway === session.endpoint);
    const minted = await api(session, 'POST', '/admin/api/cli/token/rotate', {});
    if (!record(minted) || !acceptKey(minted.token) || typeof minted.name !== 'string') {
      throw new CliError('the gateway answered token/rotate with an unexpected shape');
    }
    const next = { ...session, token: minted.token, name: minted.name };
    saveSession(next);
    commit(next);
    done('Rotated', `${environmentLabel(next.environment)} ${glyph.dot} ${next.name}; the previous key is revoked`);
    const stage = async (row, action, args, withToken) => {
      try { await runSetup(next, row.client, action, args, withToken); return true; } catch (error) {
        if (error instanceof Interrupt) throw error;
        if (error.message) warn(error.message);
        return false;
      }
    };
    const restaged = [];
    const stale = [];
    const enabled = [];
    let interrupted = false;
    for (let index = 0; index < scopes.length; index++) {
      const row = scopes[index];
      let configured = false;
      try {
        note(`re-staging ${row.label}`);
        const profile = profileArgs(row.profile || undefined);
        const model = row.state.model ? ['--model', rawModelId(row.state.model)] : [];
        if (!(await stage(row, 'configure', ['--new-key', '--overwrite', ...model, ...profile], true))) { stale.push(row); continue; }
        configured = true;
        if (row.state.mode === 'disabled' && !(await stage(row, 'disable', profile, false))) { enabled.push(row); continue; }
        restaged.push(row.state.mode === 'disabled' ? `${row.label} ${glyph.dot} disabled` : row.label);
      } catch (error) {
        if (!(error instanceof Interrupt)) throw error;
        (configured ? enabled : stale).push(row);
        for (let remaining = index + 1; remaining < scopes.length; remaining++) stale.push(scopes[remaining]);
        interrupted = true;
        break;
      }
    }
    done('Restaged', restaged.join(', ') || 'none');
    const command = (row, action) => `genesis ${action} ${row.client.id}${row.profile ? ` --profile ${row.profile}` : ''} --environment ${session.environment}`;
    for (const row of stale) warn(`${row.label} still holds the old key — run ${command(row, 'configure')}`);
    for (const row of enabled) warn(`${row.label} holds the new key but is enabled — run ${command(row, 'disable')}`);
    const unchecked = rows.filter(row => row.problem !== null);
    for (const row of unchecked) warn(`${row.label} was not checked: ${row.problem}`);
    note(`OMP profiles other than default are not enumerated; run genesis configure omp --profile <name> --environment ${session.environment} for each`);
    if (interrupted) throw new Interrupt();
    const problems = stale.length + enabled.length + unchecked.length;
    if (problems > 0) throw new CliError(`the new key is stored; ${problems} scope${problems === 1 ? '' : 's'} above need${problems === 1 ? 's' : ''} attention`);
  });
}

// ── update ──────────────────────────────────────────────────────────────────
// Updates stay on the installed CLI's recorded publisher, independent of the
// selected gateway. Gateway endpoints never supply code. Every redirect hop
// is validated before it is requested, at most five.
// The script runs with curl | bash's stdin, its output relayed through the
// redactor, and does not relaunch the dashboard.
const trustedUrl = url => typeof url === 'string' && (url.startsWith('https://') || /^http:\/\/(localhost|127\.0\.0\.1|\[::1\])(:[0-9]+)?(\/|$)/.test(url));
const REDIRECTS = new Set([301, 302, 303, 307, 308]);
async function fetchScript(url) {
  let current = url;
  for (let hops = 0; ; hops++) {
    const deadline = requestDeadline(HTTP_TIMEOUT_MS);
    try {
      let response;
      try { response = await fetch(current, { redirect: 'manual', signal: deadline.signal }); } catch (error) { throw new CliError(`could not download ${current}: ${reasonOf(error)}`); }
      if (!REDIRECTS.has(response.status)) {
        if (!response.ok) throw new CliError(`could not download ${current}: HTTP ${response.status}`);
        const text = await response.text();
        if (!text.startsWith('#!')) throw new CliError(`${current} did not return an installer script`);
        return text;
      }
      await response.body?.cancel();
      const location = response.headers.get('location');
      let next = null;
      if (location !== null) { try { next = new URL(location, current).href; } catch { /* refused below */ } }
      if (next === null || !trustedUrl(next)) throw new CliError(`${current} redirected to ${location ?? 'nowhere'}, which is not an https location`);
      if (hops === 5) throw new CliError(`${url} redirected more than 5 times`);
      current = next;
    } finally { deadline.close(); }
  }
}
async function update() {
  return runAction('Update', async () => {
    const release = releaseInfo();
    if (release === null) throw new CliError(`no release.json beside ${path.join(here, 'genesis.mjs')} (a source checkout is not updated in place); rerun the published install line`);
    if (!trustedUrl(release.installUrl)) throw new CliError(`${path.join(here, 'release.json')} records no https install URL; rerun the published install line`);
    const installUrl = release.installUrl;
    note(`downloading ${installUrl}`);
    const script = await fetchScript(installUrl);
    note(`installing from ${installUrl}`);
    const child = spawnWork('bash', ['-s'], { env: { ...process.env, GENESIS_NO_LAUNCH: '1' }, stdio: ['pipe', 'pipe', 'pipe'] });
    relay(child.stdout, process.stdout);
    relay(child.stderr, process.stderr);
    child.stdin.end(script);
    const [code] = await once(child, 'close');
    if (code !== 0) throw new CliError(`update exited ${code}`);
    done('Updated', 'Genesis; the next launch uses the installed release');
  });
}

// ── dashboard ───────────────────────────────────────────────────────────────
async function refreshIdentity(session, view) {
  try {
    const value = await runProgress(view, 'Checking saved login', () => api(session, 'GET', '/admin/api/cli/me'));
    view.prodDev = session.environment === 'prod' && isProdDev(value);
    const identity = validateMe(value);
    if (identity.name !== session.name || identity.role !== session.role || identity.email !== session.email || identity.identityClass !== session.identityClass) {
      const next = { ...session, ...identity };
      saveSession(next);
      return next;
    }
    return session;
  } catch (error) {
    view.prodDev = false;
    if (error instanceof HttpError && error.status === 401) {
      return null;
    }
    if (error instanceof Interrupt) throw error;
    view.notice = error.message;
    return session;
  }
}
async function dashboard(flags) {
  if (!interactive()) throw usage('no terminal; run a command instead (genesis --help)');
  let environment = environmentId(flags.environment ?? loadStore().environment);
  let session = loadSession(environment);
  let prodDev = false;
  const stack = [{ route: 'dashboard', title: 'genesis', selected: 0, root: true, ready: false }];
  const pendingClosures = new Set();
  const navigation = new AbortController();
  let activeView = null;
  let interruptedView = null;
  const interrupt = () => {
    if (navigation.signal.aborted) { closeTerminal(); process.exit(130); }
    navigation.abort();
    activeWork?.abort();
  };
  process.on('SIGINT', interrupt);
  process.on('SIGTERM', interrupt);
  const push = (route, label, fields = {}) => stack.push({
    route, title: `${stack.at(-1).title} ${glyph.step} ${label}`, selected: 0, ready: false, ...fields,
  });
  // Read-only pages keep a prepared parent in memory. A mutation invalidates
  // every ancestor so that a client list never displays state from before an
  // action was acknowledged.
  const pop = (mutating = false) => {
    stack.pop();
    if (mutating) for (const parent of stack) parent.ready = false;
    // The menu returned to starts at its first action again; only its data
    // is kept.
    const parent = stack.at(-1);
    if (parent !== undefined) parent.selectionOptions = null;
  };
  // The main menu depends on who is logged in where: it is rebuilt whenever
  // that changed underneath a prepared screen (a child's Main recheck can
  // drop the session), not only after an acknowledged mutation.
  const stateKey = () => `${environment}\u0000${session?.token ?? ''}\u0000${session?.role ?? ''}\u0000${prodDev}`;
  const actions = [
    { value: 'configure', label: 'Configure' }, { value: 'model', label: 'Model' },
    { value: 'enable', label: 'Enable' }, { value: 'disable', label: 'Disable' }, { value: 'unset', label: 'Unset' },
  ];
  const authorizeSecondary = async view => {
    try { await requireProdDev(view); prodDev = true; } catch (error) {
      prodDev = false;
      if (environment !== 'prod') session = null;
      throw error;
    }
  };
  if (ansi()) { terminal.alternateScreen = true; term('\x1b[?1049h'); }
  try {
    if (environment !== 'prod') {
      try { await authorizeSecondary(stack[0]); } catch (error) {
        if (error instanceof Interrupt) throw error;
        push('result', 'Prod access');
        showResult(stack.at(-1), `Failed ${glyph.dot} Prod access`, error.message, true);
      }
    }
    if (session !== null) {
      const initial = stack[0];
      const endpoint = session.endpoint;
      session = await refreshIdentity(session, initial);
      if (environment === 'prod') prodDev = initial.prodDev;
      if (session === null) {
        push('result', 'Saved login', { endpoint });
        showResult(stack.at(-1), `Failed ${glyph.dot} Check saved login`,
          `${hostOf(endpoint)} no longer accepts the stored key; log in again`, true);
      } else if (initial.notice) {
        push('result', 'Connection error');
        showResult(stack.at(-1), `Failed ${glyph.dot} Check saved login`, initial.notice, true);
        delete initial.notice;
      }
    }
    while (stack.length > 0) {
      const view = stack.at(-1);
      view.identity = session === null
        ? `${environmentLabel(environment)} ${glyph.dot} ${view.endpoint ?? loadSession(environment)?.endpoint ?? ENVIRONMENTS[environment].endpoint ?? 'not configured'} ${glyph.dot} not logged in`
        : sessionIdentity(session);
      if (navigation.signal.aborted) throw new Interrupt();
      try {
        if (view.route === 'login') {
          renderScreen({ ...view, body: '', options: [] });
          session = await login({ environment }, view);
          view.mutating = true;
          if (environment === 'prod') {
            try { await requireProdDev(view); prodDev = true; } catch (error) {
              if (error instanceof Interrupt) throw error;
              prodDev = false;
            }
          }
          delete view.notice;
          showResult(view, `Complete ${glyph.dot} ${view.title.split(` ${glyph.step} `).at(-1)}`);
          continue;
        }
        if (view.route === 'add') {
          if (environment !== 'prod') await authorizeSecondary(view);
          const { cleanup, connected } = await addConnection(session, {}, view);
          const parent = stack.at(-2);
          // A link that settled as connected changed the inventory the parent
          // shows, whether it settled before Back or while the launcher was
          // closing behind it.
          const invalidate = () => { for (const entry of stack) entry.ready = false; };
          const closing = cleanup.then(error => {
            if (connected() > 0) invalidate();
            if (error !== null) {
              parent.notice = error;
              if (activeView === parent) renderScreen(parent);
            }
          }).finally(() => pendingClosures.delete(closing));
          pendingClosures.add(closing);
          pop(connected() > 0);
          continue;
        }
        if (view.route === 'smoke') {
          // Staging is only reached with live Prod developer access: the
          // recheck happens here, before any request, like every other
          // secondary-gateway read.
          if (environment !== 'prod') await authorizeSecondary(view);
          view.body = '';
          await smoke(session, {}, view);
          showResult(view, `Complete ${glyph.dot} Smoke`);
          continue;
        }
        if (view.route === 'dashboard' && view.ready && view.stateKey !== stateKey()) view.ready = false;
        if (!view.ready) {
          const prepare = async () => {
            if (environment !== 'prod' && ['model', 'usage', 'capacity', 'connections'].includes(view.route)) await authorizeSecondary(view);
            if (view.route === 'dashboard') {
              // refreshIdentity() is the sole /me read for this dashboard.
              // In particular, do not turn a prepared main menu into a
              // second network request just to decide whether Environment fits.
              const rows = session === null ? null : await statusRows(session);
              view.statusRows = rows;
              view.body = rows === null ? '' : renderStatus(rows);
              view.options = session === null
                ? [
                  ...(prodDev ? [{ value: 'environment', label: 'Environment', hint: environmentLabel(environment) }] : []),
                  ...(environment !== 'prod' && !prodDev ? [{ value: 'prod', label: 'Prod' }] : [{ value: 'login', label: 'Log in' }]),
                  { value: 'clients', label: 'Clients' }, { value: 'update', label: 'Update' }, { value: BACK, label: 'Quit' },
                ]
                : [
                  ...(prodDev ? [{ value: 'environment', label: 'Environment', hint: environmentLabel(environment) }] : []),
                  { value: 'apply', label: 'Apply', hint: `configure installed clients for ${environmentLabel(environment)}` },
                  { value: 'clients', label: 'Clients' }, { value: 'usage', label: 'Usage' },
                  ...(['owner', 'admin'].includes(session.role) ? [{ value: 'capacity', label: 'Capacity' }, { value: 'connections', label: 'Connections' }] : []),
                  { value: 'smoke', label: 'Smoke', hint: ['health', 'login', 'models', 'one real call per provider'].join(` ${glyph.dot} `) },
                  { value: 'key', label: 'Key', hint: ['rotate', 'change gateway URL or key'].join(` ${glyph.dot} `) },
                  { value: 'logout', label: 'Log out' }, { value: 'update', label: 'Update' }, { value: BACK, label: 'Quit' },
                ];
            } else if (view.route === 'environment') {
              await authorizeSecondary(view);
              view.options = [...Object.entries(ENVIRONMENTS).map(([value, entry]) => ({
                value, label: entry.label, hint: value === environment ? 'current' : undefined,
              })), backOption];
            } else if (view.route === 'key') {
              view.options = [
                ...(session.role === 'owner' ? [{ value: 'rotate', label: 'Rotate my key' }] : []),
                { value: 'login', label: 'Change key' }, backOption,
              ];
            } else if (view.route === 'clients') {
              view.options = [...(await statusRows(session)).map(row => ({
                value: row, label: row.label,
                hint: `${row.status}${row.state?.model ? ` ${glyph.dot} ${row.state.model}` : ''}`,
              })), backOption];
            } else if (view.route === 'actions') {
              view.options = [...(session === null ? actions.filter(action => action.value === 'disable') : actions), backOption];
              const row = (await statusRows(session, view.row.profile || undefined)).find(entry => entry.client.id === view.row.client.id && entry.profile === view.row.profile);
              if (row !== undefined) view.row = row;
              view.statusRows = [view.row];
              view.body = renderStatus(view.statusRows);
            } else if (view.route === 'model') {
              const models = servedModels(await api(session, 'GET', '/v1/models'), view.row.client);
              const current = currentModelId(readState((await resolveScope(view.row.client, view.row.profile || undefined)).stateFile, view.row.client.id));
              view.options = [...modelOptions(models, current), backOption];
            } else if (view.route === 'usage') {
              view.body = renderUsage(await api(session, 'GET', '/admin/api/cli/usage'));
              view.options = [backOption];
            } else if (view.route === 'capacity') {
              view.body = renderCapacity(await api(session, 'GET', '/admin/api/cli/capacity'));
              view.options = [backOption];
            } else if (view.route === 'connections') {
              view.body = renderConnections(await api(session, 'GET', '/admin/api/cli/connections'));
              view.options = [...(session.role === 'owner' ? [{ value: 'add', label: 'Add connection' }] : []), backOption];
            } else if (view.route === 'smoke') {
              view.options = [];
            } else if (view.route === 'confirm') {
              view.options = [{ value: 'apply', label: view.actionLabel }, backOption];
            }
          };
          if (['dashboard', 'clients', 'actions', 'model', 'usage', 'capacity', 'connections'].includes(view.route)) {
            await runProgress(view, `Loading ${view.title.split(` ${glyph.step} `).at(-1)}`, prepare);
          } else await prepare();
          view.ready = true;
          view.stateKey = stateKey();
        }
        activeView = view;
        let choice;
        try { choice = await selectScreen(view, navigation.signal); } finally { activeView = null; }
        if (navigation.signal.aborted) throw new Interrupt();
        if (choice === BACK) { pop(view.mutating === true); continue; }
        if (view.route === 'dashboard') {
          const label = view.options.find(option => option.value === choice).label;
          if (choice === 'prod') {
            session = await selectEnvironment('prod');
            environment = 'prod';
            view.ready = false;
            if (session !== null) {
              session = await refreshIdentity(session, view);
              prodDev = view.prodDev;
            }
            continue;
          }
          if (['apply', 'logout', 'update'].includes(choice)) push('confirm', label, { action: choice, actionLabel: label, mutating: true });
          else if (choice === 'key' || choice === 'smoke') push(choice, label);
          else push(choice, label, { mutating: choice === 'login' });
        } else if (view.route === 'environment') {
          const next = await selectEnvironment(choice, view);
          environment = choice;
          session = next;
          view.identity = session === null ? `${environmentLabel(environment)} ${glyph.dot} not logged in` : sessionIdentity(session);
          view.mutating = true;
          showResult(view, `Complete ${glyph.dot} Environment selected`,
            `${environmentLabel(environment)}\nGateway ${session?.endpoint ?? ENVIRONMENTS[environment].endpoint}\n${session === null ? 'Not logged in' : `Logged in as ${session.name}`}\nClient configurations unchanged`);
        } else if (view.route === 'key') {
          if (choice === 'rotate') push('confirm', 'Rotate my key', { action: 'rotate', actionLabel: 'Rotate my key', mutating: true });
          else if (choice === 'login') push('login', 'Change key', { mutating: true });
        } else if (view.route === 'clients') {
          push('actions', choice.label, { row: choice });
        } else if (view.route === 'actions') {
          const label = actions.find(action => action.value === choice).label;
          if (choice === 'model') push('model', label, { row: view.row });
          else push('confirm', label, { row: view.row, action: choice, actionLabel: label, mutating: true });
        } else if (view.route === 'model') {
          push('confirm', choice, { row: view.row, action: 'configure', actionLabel: 'Configure', model: choice, mutating: true });
        } else if (view.route === 'connections') {
          push('add', 'Add connection');
        } else if (view.route === 'confirm') {
          view.body = '';
          await runProgress(view, `${view.actionLabel}${view.row ? ` ${view.row.label}` : ''}`, async () => {
            if (environment !== 'prod' && !['update', 'disable', 'logout'].includes(view.action)) await authorizeSecondary();
            if (view.action === 'rotate') await Promise.all(pendingClosures);
            const flags = { profile: view.row?.profile || undefined, model: view.model, overwrite: true };
            if (view.action === 'configure') await configure(session, view.row.client, flags);
            else if (view.action === 'disable') await switchScope(null, view.row.client, 'disable', flags);
            else if (['enable', 'unset'].includes(view.action)) await switchScope(session, view.row.client, view.action, flags);
            else if (view.action === 'rotate') await rotateToken(session, { yes: true }, next => { session = next; });
            else if (view.action === 'apply') await applyEnvironment(session, flags);
            else if (view.action === 'logout') { logout({ environment }); session = null; if (environment === 'prod') prodDev = false; }
            else if (view.action === 'update') await update();
          });
          showResult(view, `Complete ${glyph.dot} ${view.actionLabel}${view.row ? ` ${view.row.label}` : ''}`);
        }
      } catch (error) {
        if (error instanceof Interrupt) {
          if (view.body) {
            showResult(view, `Interrupted ${glyph.dot} ${view.actionLabel ? `${view.actionLabel}${view.row ? ` ${view.row.label}` : ''}` : view.title.split(` ${glyph.step} `).at(-1)}`);
            interruptedView = view;
          }
          throw error;
        }
        const resultLabel = view.actionLabel ? `${view.actionLabel}${view.row ? ` ${view.row.label}` : ''}` : view.title.split(` ${glyph.step} `).at(-1);
        showResult(view, `Failed ${glyph.dot} ${resultLabel}`,
          [error.message || String(error), view.body].filter(Boolean).join('\n\n'), true);
      }
    }
  } finally {
    activeView = null;
    await Promise.all(pendingClosures);
    process.off('SIGINT', interrupt);
    process.off('SIGTERM', interrupt);
    closeTerminal();
    if (interruptedView !== null) { out(interruptedView.status); out(interruptedView.body); }
  }
}

// ── arguments ───────────────────────────────────────────────────────────────
const HELP = `Usage: genesis [command] [options]

  genesis                                   dashboard
  setup [--url URL]                         log into prod (URL and key), then configure installed clients
  environment [prod | staging]
  login [--url URL]                         sign in (AGENT_AUTH_TOKEN or a hidden prompt)
  logout
  apply [--overwrite]                       configure every installed client for the selected environment
  status [--profile P]
  configure <client> [--model ID] [--profile P] [--overwrite]
  disable <client> [--profile P]            local; no login required
  enable | unset <client> [--profile P]
  model <client> [ID] [--profile P]         list or pick the client's default model
  usage [--json]                            your recorded usage
  capacity                                  owner/admin
  connections [list | add]                  owner/admin; add: owner, serves a local page [--provider P] [--worker ID] [--port N]
  smoke [--json] [--environment E]          gateway health, login, models and one real call per provider
  token rotate [--yes]                      owner
  update | --update
  --version | --help

Environment override: --environment prod | staging (does not change the saved selection)
Clients: ${CLIENTS.map(client => client.id).join(', ')}
Exit codes: 0 ok, 1 failure, 2 usage`;
const VALUE_FLAGS = new Set(['environment', 'url', 'model', 'profile', 'provider', 'worker', 'port']);
const SWITCH_FLAGS = new Set(['overwrite', 'yes', 'version', 'help', 'update', 'json']);
export function parseArgs(argv) {
  const positionals = [];
  const flags = {};
  for (let index = 0; index < argv.length; index++) {
    const argument = argv[index];
    if (argument === '-h') { flags.help = true; continue; }
    if (!argument.startsWith('--')) { positionals.push(argument); continue; }
    const equals = argument.indexOf('=');
    const name = argument.slice(2, equals === -1 ? undefined : equals);
    if (VALUE_FLAGS.has(name)) {
      const value = equals === -1 ? argv[++index] : argument.slice(equals + 1);
      if (value === undefined || value === '') throw usage(`--${name} needs a value`);
      flags[name] = value;
    } else if (SWITCH_FLAGS.has(name) && equals === -1) flags[name] = true;
    else throw usage(`unknown option ${argument}; see genesis --help`);
  }
  return { positionals, flags };
}
async function main(argv) {
  primeSecrets();
  const { positionals, flags } = parseArgs(argv);
  const [command, ...rest] = positionals;
  if (flags.environment !== undefined) environmentId(flags.environment);
  if (flags.help || command === 'help') { out(HELP); return; }
  if (flags.version) { out(`genesis ${releaseInfo()?.commit ?? 'source'}`); return; }
  if (flags.url !== undefined && !['login', 'setup'].includes(command)) throw usage('--url is only accepted by login and setup; it never retargets a stored key');
  if (flags.json && !['usage', 'smoke'].includes(command)) throw usage('--json is only accepted by usage and smoke');
  if (flags.update || command === 'update') { await update(); return; }
  const expect = count => { if (rest.length !== count) throw usage(`${command} takes ${count === 0 ? 'no arguments' : `${count} argument${count === 1 ? '' : 's'}`}; see genesis --help`); };
  switch (command) {
    case undefined: await dashboard(flags); return;
    case 'setup': expect(0); await setup(flags); return;
    case 'environment': {
      const apply = async view => {
        if (rest.length > 1) throw usage('environment takes prod or staging');
        if (rest.length === 1) {
          if (flags.environment !== undefined) throw usage('use environment prod|staging without --environment to save the selection');
          await selectEnvironment(rest[0], view);
        }
        const store = loadStore();
        const environment = flags.environment ?? store.environment;
        if (rest.length === 0 && environment !== 'prod') await requireProdDev(view);
        out(`${environmentLabel(environment)} ${glyph.dot} ${store.sessions[environment]?.endpoint ?? ENVIRONMENTS[environment].endpoint ?? 'not configured'}`);
      };
      if (rest.length === 0) await apply(null);
      else await runAction('Environment', apply, true);
      return;
    }
    case 'login': expect(0); await runAction('Log in', view => login(flags, view), true); return;
    case 'logout': expect(0); await runAction('Log out', () => logout(flags)); return;
    case 'apply': expect(0); await applyEnvironment(await requireSession(flags), flags); return;
    case 'status': expect(0); await status(await requireSession(flags), flags); return;
    case 'configure': expect(1); await configure(await requireSession(flags), clientById(rest[0]), flags); return;
    case 'disable': expect(1); await switchScope(null, clientById(rest[0]), command, flags); return;
    case 'enable': case 'unset': expect(1); await switchScope(await requireSession(flags), clientById(rest[0]), command, flags); return;
    case 'model':
      if (rest.length < 1 || rest.length > 2) throw usage('model takes a client and an optional model id; see genesis --help');
      await model(await requireSession(flags), clientById(rest[0]), rest[1], flags);
      return;
    case 'usage': expect(0); await showUsage(await requireSession(flags), flags); return;
    case 'capacity': expect(0); await showCapacity(await requireSession(flags)); return;
    case 'connections':
      if (rest.length === 0 || (rest.length === 1 && rest[0] === 'list')) await showConnections(await requireSession(flags));
      else if (rest[0] === 'add' && rest.length === 1) await addConnection(await requireSession(flags), flags);
      else throw usage('connections takes list or add; see genesis --help');
      return;
    case 'smoke': {
      expect(0);
      const session = await requireSession(flags);
      if (interactive() && !flags.json) await runAction('Smoke', view => smoke(session, flags, view));
      else await smoke(session, flags);
      return;
    }
    case 'token':
      if (rest.length !== 1 || rest[0] !== 'rotate') throw usage('token takes rotate; see genesis --help');
      await rotateToken(await requireSession(flags), flags);
      return;
    default: throw usage(`unknown command ${command}; see genesis --help`);
  }
}
function run() {
  main(process.argv.slice(2)).then(() => {
    closeTerminal();
    process.exitCode = 0;
  }, error => {
    closeTerminal();
    if (error instanceof CliError) {
      if (error.message !== '') process.stderr.write(redact(`${error.exitCode === 130 ? '' : 'genesis: '}${error.message}\n`));
      process.exitCode = error.exitCode;
      return;
    }
    process.stderr.write(redact(`genesis: ${error?.stack ?? error}\n`));
    process.exitCode = 1;
  });
}
function isEntry() {
  try { return process.argv[1] !== undefined && pathToFileURL(fs.realpathSync(process.argv[1])).href === import.meta.url; } catch { return false; }
}
if (isEntry()) run();
