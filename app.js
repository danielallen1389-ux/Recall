// Recall by Hand: draw a weighted set of facts or poems to write out by hand.
import { firebaseConfig } from './firebase-config.js';
import { initializeApp, getApps } from 'https://www.gstatic.com/firebasejs/12.19.0/firebase-app.js';
import {
  getAuth, onAuthStateChanged, signInWithEmailAndPassword, createUserWithEmailAndPassword,
  signOut, sendPasswordResetEmail, setPersistence, inMemoryPersistence
} from 'https://www.gstatic.com/firebasejs/12.19.0/firebase-auth.js';
import {
  initializeFirestore, persistentLocalCache, persistentMultipleTabManager,
  doc, collection, query, where, onSnapshot, setDoc, updateDoc, deleteDoc, deleteField, serverTimestamp, writeBatch, increment
} from 'https://www.gstatic.com/firebasejs/12.19.0/firebase-firestore.js';

const DAY = 864e5;
const NEW_DAYS = 30;            // never-written items count as at least this many days overdue
const MISS_DAYS = 14;           // items missed last time count as at least this many days overdue
const MASTERED_N = 3;           // right this many times, and right last time
const MAX_DECK_BYTES = 900000;  // Firestore documents top out at 1 MiB
const MAX_LIST = 300;
const MAX_FIELD = 2000;
const MAX_POEM = 20000;
const DEFAULT_ALLOW = { facts: 0, poems: 5 };
const ALLOW_CHOICES = [0, 5, 10, 15, 20, 25, 30, 40, 50];
const $ = (id) => document.getElementById(id);
const enc = new TextEncoder();

let app, auth, db;

// ---------------------------------------------------------------- state
const freshStudy = () => ({ kind: 'facts', sel: { facts: new Set(), poems: new Set() }, count: { facts: 10, poems: 1 }, mode: 'paper', allow: 'deck' });
const freshDv = () => ({ open: null, q: '', editing: null, renaming: false, confirmDeck: false, creating: false, expanded: new Set(), selecting: false, picked: new Set() });
const S = {
  phase: 'loading',             // loading | config | setup | signin | inactive | app
  metaLoaded: false, authLoaded: false,
  adminUid: null, adminName: '',
  fbUser: null, me: null, meLoaded: false, myRequest: null,
  isAdmin: false, listenersFor: null, settingUp: false, authShown: null,
  decks: new Map(), deckParts: {}, decksLoaded: false, pendingDecks: new Map(),
  progress: {}, days: {}, people: new Map(), peopleLoaded: false, requests: new Map(),
  profiles: new Map(), profilesLoaded: false, stats: new Map(), friendsLoaded: false, friendsListening: false,
  myStats: null, myStatsLoaded: false, progressLoaded: false, friendsSort: 'week',
  theme: { id: 'classic' }, themeSaved: null, themePreview: false,
  view: 'study',
  study: freshStudy(),
  session: null,
  dv: freshDv(),
  add: { kind: 'facts', deckId: null, chosen: false },
  pp: { renaming: null },
};
let userUnsubs = [];
let dataUnsubs = null;
let migrated = false;

// ---------------------------------------------------------------- helpers
function h(tag, props, ...kids) {
  const el = document.createElement(tag);
  if (props) for (const [k, v] of Object.entries(props)) {
    if (v == null || v === false) continue;
    if (k === 'class') el.className = v;
    else if (k === 'text') el.textContent = v;
    else if (k === 'style') el.style.cssText = v;
    else if (k === 'value') el.value = v;
    else if (k === 'checked') el.checked = !!v;
    else if (k.startsWith('on') && typeof v === 'function') el.addEventListener(k.slice(2), v);
    else if (v === true) el.setAttribute(k, '');
    else el.setAttribute(k, String(v));
  }
  for (const c of kids.flat()) if (c != null && c !== false) el.append(c.nodeType ? c : String(c));
  return el;
}
function put(el, ...kids) { el.replaceChildren(...kids.flat().filter(k => k != null && k !== false)); return el; }
const clampInt = (v, lo, hi, d) => { const n = Math.round(Number(v)); return Number.isFinite(n) ? Math.min(hi, Math.max(lo, n)) : d; };
const rid = (p) => p + Date.now().toString(36) + Math.random().toString(36).slice(2, 8);
const plural = (n, one, many) => `${Number(n).toLocaleString()} ${n === 1 ? one : (many || one + 's')}`;
const norm = (s) => String(s || '').trim().toLowerCase().replace(/\s+/g, ' ');
const myUid = () => (S.fbUser ? S.fbUser.uid : null);
const myName = () => (S.me && S.me.name) || (S.isAdmin && S.adminName) || 'Me';
const bytes = (o) => enc.encode(JSON.stringify(o)).length;
const pct = (x) => `${Math.round(x)}%`;

function ago(t, now) {
  if (!t) return 'never';
  const s = (now - t) / 1000;
  if (s < 3600) return 'just now';
  if (s < 86400) return Math.floor(s / 3600) + ' h ago';
  const d = Math.floor(s / 86400);
  if (d === 1) return 'yesterday';
  if (d < 14) return d + ' days ago';
  if (d < 60) return Math.round(d / 7) + ' wk ago';
  if (d < 730) return Math.round(d / 30.4) + ' mo ago';
  return (d / 365).toFixed(1) + ' yr ago';
}
function dayKey(date) {
  const d = date || new Date();
  return d.getFullYear() + '-' + String(d.getMonth() + 1).padStart(2, '0') + '-' + String(d.getDate()).padStart(2, '0');
}
function cleanPoem(text) {
  return String(text || '').replace(/\r\n?/g, '\n').split('\n').map(l => l.replace(/\s+$/, '')).join('\n').replace(/\n{3,}/g, '\n\n').trim();
}
const poemLines = (t) => String(t || '').split('\n').filter(l => l.trim()).length;
const poemFirstLine = (t) => (String(t || '').split('\n').find(l => l.trim()) || '').trim();
function poemFirstWords(t) {
  return String(t || '').split('\n').map(l => { const w = l.trim().split(/\s+/)[0]; return w ? w + ' …' : ''; }).join('\n');
}

let toastTimer = 0;
function toast(msg, action) {
  const t = $('toast');
  put(t, h('span', { text: msg }), action ? h('button', { type: 'button', onclick: () => { t.hidden = true; action.run(); } }, action.label) : null);
  t.hidden = false;
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => { t.hidden = true; }, action ? 7000 : 4500);
}
function authError(e) {
  const c = (e && e.code) || '';
  if (c.includes('invalid-credential') || c.includes('wrong-password') || c.includes('user-not-found')) return "That email and password don't match.";
  if (c.includes('too-many-requests')) return 'Too many tries. Wait a few minutes, or reset your password.';
  if (c.includes('email-already-in-use')) return 'There is already a sign-in for that email.';
  if (c.includes('weak-password')) return 'Use a password with at least 8 characters.';
  if (c.includes('invalid-email')) return "That email address doesn't look right.";
  if (c.includes('network-request-failed')) return "Can't reach the server. Check your connection and try again.";
  if (c.includes('operation-not-allowed')) return 'Email sign-in is turned off in Firebase. Turn on Email/Password under Authentication → Sign-in method.';
  return (e && e.message) || 'Something went wrong. Try again.';
}
function dataError(e) {
  const c = (e && e.code) || '';
  if (c.includes('permission-denied')) return "You don't have permission to change that.";
  if (c.includes('resource-exhausted')) return "Today's free database allowance is used up. It resets tomorrow.";
  if (c.includes('unavailable')) return "Can't reach the server. Your change will save when you're back online.";
  if (c.includes('invalid-argument')) return 'That deck is too big to save. Put new items in a new deck.';
  return "Couldn't save that. Try again.";
}
async function save(p, okMsg, action) {
  try { await p; if (okMsg) toast(okMsg, action); return true; }
  catch (e) { console.error(e); toast(dataError(e)); return false; }
}
async function copyText(text, fallbackEl, okMsg) {
  try {
    await navigator.clipboard.writeText(text);
    if (fallbackEl) fallbackEl.hidden = true;
    toast(okMsg);
  } catch (e) {
    if (fallbackEl) { fallbackEl.value = text; fallbackEl.hidden = false; fallbackEl.focus(); fallbackEl.select(); }
    toast('Copying was blocked, so the text is selected below. Copy it with your keyboard.');
  }
}
function seg(id, options, current, onPick) {
  return h('div', { class: 'seg', id, role: 'group' }, ...options.map(([k, label]) =>
    h('button', { type: 'button', 'data-k': k, 'aria-pressed': k === current ? 'true' : 'false', onclick: () => onPick(k) }, label)));
}
function setSeg(id, value) {
  const el = $(id); if (!el) return;
  for (const b of el.querySelectorAll('button')) b.setAttribute('aria-pressed', b.dataset.k === value ? 'true' : 'false');
}
function withFocus(container, fn) {
  const a = document.activeElement;
  const key = a && container.contains(a) ? a.dataset.key : null;
  fn();
  if (key) { const el = container.querySelector(`[data-key="${CSS.escape(key)}"]`); if (el) el.focus(); }
}
function field(label, input) { return h('div', { class: 'field' }, h('label', { class: 'label', for: input.id, text: label }), input); }
function check(id, label, checked, onChange, disabled) {
  const cb = h('input', { type: 'checkbox', id, checked, disabled, 'data-key': id });
  if (onChange) cb.addEventListener('change', () => onChange(cb.checked));
  return h('label', { class: 'check', for: id }, cb, h('span', { text: label }));
}
function allowSelect(id, value, onChange, withDeckOption) {
  const sel = h('select', { id, 'data-key': id });
  if (withDeckOption) sel.append(h('option', { value: 'deck', text: "Each deck's standard" }));
  for (const n of ALLOW_CHOICES) sel.append(h('option', { value: String(n), text: n === 0 ? '0% (exact)' : `${n}%` }));
  sel.value = String(value);
  sel.addEventListener('change', () => onChange(sel.value === 'deck' ? 'deck' : Number(sel.value)));
  return sel;
}

// ---------------------------------------------------------------- themes
// Each theme takes its main color from an iPhone finish and pairs it with complementary accents.
// Only a few colors are picked by hand; the rest are derived and checked for readable contrast.
const CLASSIC_PREVIEW = { mode: 'light', bg: '#EDF1F6', card: '#FFFFFF', accent: '#2944C4', pen: '#2340B8', margin: '#D8524A', hl: '#FFE45E' };
const THEME_GROUPS = [
  ['iPhone 18 Pro', [
    ['burgundy', 'Burgundy', '#5E1A28', { mode: 'dark', bg: '#1A0E12', accent: '#E8798F', pen: '#F4B9C6', margin: '#E3B65C', hl: '#E3B65C' }],
    ['glacier', 'Glacier', '#C9DCE6', { mode: 'light', bg: '#E9F1F5', accent: '#2C6E8F', pen: '#1D5B7A', margin: '#D8634D', hl: '#FFE3A6' }],
    ['silver', 'Silver', '#E2E3E4', { mode: 'light', bg: '#EDEEF0', accent: '#3A4A63', pen: '#2D4C82', margin: '#D4544A', hl: '#FFE45E' }, 'Also on iPhone 17 Pro'],
    ['black', 'Black', '#232426', { mode: 'dark', bg: '#101113', accent: '#9FB4FF', pen: '#C7D4FF', margin: '#FF7A6B', hl: '#E9CF4E' }, 'Also on iPhone 17 and 16'],
  ]],
  ['iPhone 17 Pro', [
    ['cosmic-orange', 'Cosmic Orange', '#F77E2D', { mode: 'light', bg: '#FFF1E6', accent: '#C4520E', pen: '#2350B5', margin: '#2F5BD3', hl: '#FFD3A8' }],
    ['deep-blue', 'Deep Blue', '#32374A', { mode: 'dark', bg: '#11162A', accent: '#F29A4A', pen: '#AFC4FF', margin: '#F29A4A', hl: '#F2C14A' }],
  ]],
  ['iPhone Air', [
    ['sky-blue', 'Sky Blue', '#DCEAF4', { mode: 'light', bg: '#EDF5FB', accent: '#2C74B0', pen: '#1C5A92', margin: '#E46A58', hl: '#FFF0A0' }],
    ['light-gold', 'Light Gold', '#EFE2C6', { mode: 'light', bg: '#FAF4E4', accent: '#8E6210', pen: '#33489C', margin: '#C0533B', hl: '#F4D684' }],
    ['cloud-white', 'Cloud White', '#F2F2EE', { mode: 'light', bg: '#F5F5F2', accent: '#3E63DD', pen: '#2B49B8', margin: '#E05A4F', hl: '#FFE58A' }],
    ['space-black', 'Space Black', '#2B2C30', { mode: 'dark', bg: '#0D0E11', accent: '#7DD3FC', pen: '#C2DCFF', margin: '#FF6B6B', hl: '#F5D565' }],
  ]],
  ['iPhone 17', [
    ['lavender', 'Lavender', '#DCCBEB', { mode: 'light', bg: '#F4EFFA', accent: '#7046A8', pen: '#55348F', margin: '#C9577F', hl: '#E4F2A2' }],
    ['mist-blue', 'Mist Blue', '#9DB4D6', { mode: 'light', bg: '#ECF1F8', accent: '#3A5C97', pen: '#284B88', margin: '#DB6E52', hl: '#FFE1A0' }],
    ['sage', 'Sage', '#A9B78C', { mode: 'light', bg: '#F0F3E8', accent: '#4A6A2A', pen: '#2C4F33', margin: '#B4546C', hl: '#F5E49C' }],
    ['white', 'White', '#F6F6F6', { mode: 'light', bg: '#FAFAFA', card: '#FFFFFF', accent: '#2563EB', pen: '#1D4ED8', margin: '#E5413B', hl: '#FDE68A' }, 'Also on iPhone 16'],
  ]],
  ['iPhone 16 Pro', [
    ['desert-titanium', 'Desert Titanium', '#BFA38C', { mode: 'light', bg: '#F5EEE6', accent: '#87553A', pen: '#2D4A6E', margin: '#B44E36', hl: '#F2D6A2' }],
    ['natural-titanium', 'Natural Titanium', '#BDB7AD', { mode: 'light', bg: '#EFEDE8', accent: '#4D5C6B', pen: '#2F4760', margin: '#BF4F2E', hl: '#F0DE9A' }],
    ['white-titanium', 'White Titanium', '#EEEDE8', { mode: 'light', bg: '#F4F3EF', accent: '#7A6544', pen: '#2B4762', margin: '#C2553E', hl: '#F3E1A6' }],
    ['black-titanium', 'Black Titanium', '#3A3A3B', { mode: 'dark', bg: '#131313', accent: '#CDBA9C', pen: '#D6E1EC', margin: '#E07A5F', hl: '#CDBA9C' }],
  ]],
  ['iPhone 16', [
    ['ultramarine', 'Ultramarine', '#8F9FF2', { mode: 'light', bg: '#EEF0FD', accent: '#4352D6', pen: '#2F3DB8', margin: '#D9701F', hl: '#FFD8A6' }],
    ['teal', 'Teal', '#A6D3CF', { mode: 'light', bg: '#E9F5F3', accent: '#1C7670', pen: '#145954', margin: '#D2664A', hl: '#FFD9C7' }],
    ['pink', 'Pink', '#F2B3D6', { mode: 'light', bg: '#FDF0F6', accent: '#B83C78', pen: '#7A2C5B', margin: '#2F8A5B', hl: '#CDEFD8' }],
  ]],
];
const PRESETS = new Map();
for (const [, list] of THEME_GROUPS) for (const [id, name, finish, spec] of list) PRESETS.set(id, { name, finish, spec });
const THEME_KEYS = ['--paper', '--card', '--ink', '--ink-soft', '--line', '--rule', '--margin', '--accent', '--accent-soft', '--accent-ink',
  '--pen', '--hl', '--hl-ink', '--ok', '--ok-soft', '--danger', '--danger-soft', '--shadow', 'color-scheme'];

function hexRgb(hex) {
  let x = String(hex || '').replace('#', '');
  if (x.length === 3) x = x.split('').map(c => c + c).join('');
  const n = parseInt(x, 16);
  return Number.isFinite(n) ? [(n >> 16) & 255, (n >> 8) & 255, n & 255] : [0, 0, 0];
}
const rgbHex = (rgb) => '#' + rgb.map(v => Math.round(Math.max(0, Math.min(255, v))).toString(16).padStart(2, '0')).join('').toUpperCase();
const mix = (a, b, t) => { const A = hexRgb(a), B = hexRgb(b); return rgbHex(A.map((v, i) => v + (B[i] - v) * t)); };
function lum(hex) {
  const c = hexRgb(hex).map(v => { v /= 255; return v <= 0.03928 ? v / 12.92 : Math.pow((v + 0.055) / 1.055, 2.4); });
  return 0.2126 * c[0] + 0.7152 * c[1] + 0.0722 * c[2];
}
const contrastRatio = (a, b) => { const x = lum(a), y = lum(b); return (Math.max(x, y) + 0.05) / (Math.min(x, y) + 0.05); };
// Nudge a color toward black (light themes) or white (dark themes) until it reads clearly on every background given.
function ensureContrast(fg, bgs, ratio, dark) {
  let c = fg;
  for (let i = 0; i < 30 && bgs.some(b => contrastRatio(c, b) < ratio); i++) c = mix(c, dark ? '#FFFFFF' : '#000000', 0.07);
  return c;
}
function hexHsl(hex) {
  const [r, g, b] = hexRgb(hex).map(v => v / 255);
  const max = Math.max(r, g, b), min = Math.min(r, g, b), l = (max + min) / 2;
  if (max === min) return [0, 0, l * 100];
  const d = max - min, s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
  let hh = max === r ? (g - b) / d + (g < b ? 6 : 0) : max === g ? (b - r) / d + 2 : (r - g) / d + 4;
  return [hh * 60, s * 100, l * 100];
}
function hslHex(hh, s, l) {
  hh = ((hh % 360) + 360) % 360; s /= 100; l /= 100;
  const k = (n) => (n + hh / 30) % 12, a = s * Math.min(l, 1 - l);
  const f = (n) => l - a * Math.max(-1, Math.min(k(n) - 3, Math.min(9 - k(n), 1)));
  return rgbHex([f(0) * 255, f(8) * 255, f(4) * 255]);
}
const isDarkColor = (hex) => lum(hex) < 0.2;
function deriveTheme(spec) {
  const dark = spec.mode ? spec.mode === 'dark' : isDarkColor(spec.bg);
  const bg = spec.bg;
  const card = spec.card || (dark ? mix(bg, '#FFFFFF', 0.07) : mix(bg, '#FFFFFF', 0.72));
  const surf = [bg, card];
  const ink = ensureContrast(dark ? mix('#F1F3F7', spec.accent, 0.08) : mix('#15171D', spec.accent, 0.1), surf, 12, dark);
  const inkSoft = ensureContrast(mix(ink, bg, 0.42), surf, 4.6, dark);
  const accentSoft = mix(bg, spec.accent, dark ? 0.2 : 0.13);
  const accent = ensureContrast(spec.accent, [bg, card, accentSoft], 4.5, dark);
  const accentInk = contrastRatio(accent, '#FFFFFF') >= contrastRatio(accent, '#111111') ? '#FFFFFF' : '#111111';
  const pen = ensureContrast(spec.pen || accent, [card], 4.6, dark);
  const margin = ensureContrast(spec.margin || (dark ? '#E2716A' : '#D8524A'), [card], 4.2, dark);
  const hl = spec.hl || (dark ? '#E9CF4E' : '#FFE45E');
  const hlInk = contrastRatio(hl, '#111111') >= contrastRatio(hl, '#FFFFFF') ? '#1E1A0A' : '#FFFFFF';
  const okBase = dark ? '#6FD3A0' : '#1F7A4D', dangerBase = dark ? '#F08A80' : '#B23A30';
  const okSoft = mix(bg, okBase, dark ? 0.18 : 0.14), dangerSoft = mix(bg, dangerBase, dark ? 0.18 : 0.12);
  return {
    '--paper': bg, '--card': card, '--ink': ink, '--ink-soft': inkSoft,
    '--line': mix(bg, ink, dark ? 0.16 : 0.13), '--rule': mix(card, spec.accent, dark ? 0.2 : 0.16),
    '--margin': margin, '--accent': accent, '--accent-soft': accentSoft, '--accent-ink': accentInk,
    '--pen': pen, '--hl': hl, '--hl-ink': hlInk,
    '--ok': ensureContrast(okBase, [card, okSoft], 4.5, dark), '--ok-soft': okSoft,
    '--danger': ensureContrast(dangerBase, [card, dangerSoft], 4.5, dark), '--danger-soft': dangerSoft,
    '--shadow': dark ? '0 1px 0 rgba(0,0,0,.3), 0 12px 30px -14px rgba(0,0,0,.75)' : '0 1px 0 rgba(22,32,58,.05), 0 10px 26px -14px rgba(22,32,58,.32)',
    'color-scheme': dark ? 'dark' : 'light',
  };
}
// Picks an accent, answer ink and margin color that go with a background.
function suggestColors(bg) {
  const dark = isDarkColor(bg);
  const [hh, s] = hexHsl(bg);
  const neutral = s < 12;
  const base = neutral ? 225 : hh + 180;
  return {
    bg,
    accent: hslHex(base, neutral ? 70 : 62, dark ? 70 : 38),
    pen: hslHex(base + 18, 58, dark ? 80 : 30),
    margin: hslHex(neutral ? 6 : hh + 40, 68, dark ? 66 : 48),
  };
}
function themeSpec(theme) {
  if (!theme || !theme.id || theme.id === 'classic') return null;
  if (theme.id === 'custom') return theme.custom && theme.custom.bg && theme.custom.accent ? theme.custom : null;
  const p = PRESETS.get(theme.id);
  return p ? p.spec : null;
}
function applyTheme(theme) {
  const root = document.documentElement;
  for (const k of THEME_KEYS) root.style.removeProperty(k);
  const spec = themeSpec(theme);
  if (spec) for (const [k, v] of Object.entries(deriveTheme(spec))) root.style.setProperty(k, v);
  const paper = getComputedStyle(document.body || root).backgroundColor;
  const meta = document.querySelector('meta[name="theme-color"]');
  if (meta && paper) meta.setAttribute('content', paper);
  S.theme = spec ? theme : { id: 'classic' };
}
function cacheTheme(theme) { try { localStorage.setItem('rbh.theme', JSON.stringify(theme)); } catch (e) { /* ignore */ } }
async function saveTheme(theme) {
  S.themeSaved = theme; S.themePreview = false;
  applyTheme(theme); cacheTheme(theme);
  if (myUid()) await save(updateDoc(doc(db, 'users', myUid()), { theme }), 'Theme saved.');
}

// ---------------------------------------------------------------- answer checking
function normText(s) {
  return String(s || '').normalize('NFKD').replace(/[̀-ͯ]/g, '').toLowerCase()
    .replace(/[^\p{L}\p{N}\s]/gu, '').replace(/\s+/g, ' ').trim();
}
function tokens(text) {
  const out = [];
  const re = /(\s+)|(\S+)/g; let m;
  while ((m = re.exec(String(text || '')))) {
    if (m[1]) out.push({ raw: m[1], space: true });
    else { const n = normText(m[2]); out.push({ raw: m[2], norm: n, word: n.length > 0 }); }
  }
  return out;
}
// 2 = same word, 1 = small typo, 0 = different word
function wordScore(a, b) {
  if (a === b) return 2;
  const L = Math.max(a.length, b.length);
  if (L < 4 || Math.abs(a.length - b.length) > 2) return 0;
  return charDist(a, b) <= Math.max(1, Math.floor(L / 5)) ? 1 : 0;
}
// Pairs up as many of your words with the answer's words as possible, in reading order (earliest pairing wins ties).
function alignWords(a, b) {
  const n = a.length, m = b.length;
  if ((n + 1) * (m + 1) > 4e6) return null;
  const W = m + 1;
  const s = new Uint16Array((n + 1) * W);
  for (let i = n - 1; i >= 0; i--) for (let j = m - 1; j >= 0; j--) {
    const down = s[(i + 1) * W + j], right = s[i * W + j + 1];
    let best = down > right ? down : right;
    const w = wordScore(a[i], b[j]);
    if (w) { const diag = s[(i + 1) * W + j + 1] + w; if (diag > best) best = diag; }
    s[i * W + j] = best;
  }
  const aSt = new Array(n).fill('miss'), bSt = new Array(m).fill('extra');
  let i = 0, j = 0;
  while (i < n && j < m) {
    const w = wordScore(a[i], b[j]);
    if (w && s[i * W + j] === s[(i + 1) * W + j + 1] + w) { aSt[i] = bSt[j] = w === 2 ? 'ok' : 'typo'; i++; j++; }
    else if (s[(i + 1) * W + j] >= s[i * W + j + 1]) i++;
    else j++;
  }
  return { aSt, bSt };
}
function charDist(a, b) {
  if (a === b) return 0;
  let prev = Array.from({ length: b.length + 1 }, (_, j) => j);
  for (let i = 1; i <= a.length; i++) {
    const cur = [i];
    for (let j = 1; j <= b.length; j++) cur[j] = Math.min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (a[i - 1] === b[j - 1] ? 0 : 1));
    prev = cur;
  }
  return prev[b.length];
}
// How far off a typed answer is (0–100), which words to mark, and the missing phrases.
// Short fact answers (1–2 words) are compared letter by letter; everything else word by word.
function grade(expected, typed, kind) {
  const et = tokens(expected), tt = tokens(typed);
  const ew = et.filter(t => t.word), tw = tt.filter(t => t.word);
  let r = alignWords(ew.map(t => t.norm), tw.map(t => t.norm));
  if (!r) r = {
    aSt: ew.map((t, k) => (tw[k] && tw[k].norm === t.norm ? 'ok' : 'miss')),
    bSt: tw.map((t, k) => (ew[k] && ew[k].norm === t.norm ? 'ok' : 'extra')),
  };
  ew.forEach((t, k) => { t.st = r.aSt[k]; });
  tw.forEach((t, k) => { t.st = r.bSt[k]; });
  const missing = r.aSt.filter(x => x === 'miss').length;
  const extra = r.bSt.filter(x => x === 'extra').length;
  const typos = r.aSt.filter(x => x === 'typo').length;
  let off;
  if (kind === 'facts' && ew.length <= 2) {
    const a = normText(expected), b = normText(typed);
    off = (charDist(a, b) / Math.max(1, a.length)) * 100;
  } else off = ((Math.max(missing, extra) + typos * 0.5) / Math.max(1, ew.length)) * 100;
  const gaps = []; let cur = [];
  for (const t of et) {
    if (t.space || !t.word) continue;
    if (t.st === 'miss') cur.push(t.raw);
    else if (cur.length) { gaps.push(cur.join(' ')); cur = []; }
  }
  if (cur.length) gaps.push(cur.join(' '));
  const clean = (g) => g.replace(/^[^\p{L}\p{N}]+|[^\p{L}\p{N}]+$/gu, '');
  return { off: Math.min(100, off), et, tt, gaps: gaps.map(clean).filter(Boolean) };
}
function renderTokens(list, side) {
  return list.map(t => {
    if (t.space) return document.createTextNode(t.raw);
    const cls = !t.word ? null : t.st === 'typo' ? 'w-typo' : (side === 'exp' ? (t.st === 'miss' ? 'w-miss' : null) : (t.st === 'extra' ? 'w-extra' : null));
    return h('span', { class: cls, text: t.raw });
  });
}

// ---------------------------------------------------------------- prefs (per person, per device)
function loadPrefs() {
  try {
    const p = JSON.parse(localStorage.getItem('rbh.prefs.' + myUid()) || '{}');
    if (p.kind === 'facts' || p.kind === 'poems') S.study.kind = p.kind;
    if (p.count) { S.study.count.facts = clampInt(p.count.facts, 1, 200, 10); S.study.count.poems = clampInt(p.count.poems, 1, 50, 1); }
    if (p.sel) for (const k of ['facts', 'poems']) if (Array.isArray(p.sel[k])) S.study.sel[k] = new Set(p.sel[k].filter(x => typeof x === 'string'));
    if (p.mode === 'paper' || p.mode === 'type') S.study.mode = p.mode;
    if (p.allow === 'deck' || ALLOW_CHOICES.includes(p.allow)) S.study.allow = p.allow;
  } catch (e) { /* storage unavailable */ }
}
function savePrefs() {
  try {
    localStorage.setItem('rbh.prefs.' + myUid(), JSON.stringify({
      kind: S.study.kind, count: S.study.count, mode: S.study.mode, allow: S.study.allow,
      sel: { facts: [...S.study.sel.facts], poems: [...S.study.sel.poems] },
    }));
  } catch (e) { /* ignore */ }
}

// ---------------------------------------------------------------- decks, items, progress
function normDeck(id, v) {
  const kind = v.kind === 'poems' ? 'poems' : 'facts';
  const legacyUniversal = v.scope === 'universal';
  return {
    id, kind, legacyUniversal,
    name: String(v.name || 'Untitled deck'),
    visibility: legacyUniversal || v.visibility === 'shared' ? 'shared' : 'private',
    friendsCanEdit: v.friendsCanEdit === true,
    allowPct: typeof v.allowPct === 'number' ? v.allowPct : DEFAULT_ALLOW[kind],
    ownerId: String(v.ownerId || ''),
    ownerName: String(v.ownerName || ''),
    items: (v.items && typeof v.items === 'object') ? v.items : {},
  };
}
function itemsOf(d) {
  return Object.entries(d.items).filter(([, it]) => it && typeof it === 'object' &&
    (d.kind === 'poems' ? (typeof it.title === 'string' && typeof it.text === 'string') : (typeof it.p === 'string' && typeof it.a === 'string')));
}
function category(d) {
  if (d.ownerId === myUid()) return 'mine';
  if (d.visibility === 'shared') return 'shared';
  return 'other';
}
const canManage = (d) => S.isAdmin || d.ownerId === myUid();
const canEditItems = (d) => canManage(d) || (d.visibility === 'shared' && d.friendsCanEdit);
function ownerLabel(d) {
  if (d.ownerId === myUid()) return 'you';
  const pr = S.profiles.get(d.ownerId);
  const p = S.people.get(d.ownerId);
  return (pr && pr.name) || (p && p.name) || d.ownerName || 'someone';
}
function sortDecks(list) { return list.sort((a, b) => a.name.localeCompare(b.name, undefined, { sensitivity: 'base' })); }
function studyDecks(kind) { return sortDecks([...S.decks.values()].filter(d => d.kind === kind && category(d) !== 'other')); }
function pool(kind, sel) {
  const out = [];
  for (const d of studyDecks(kind)) {
    if (sel && sel.size && !sel.has(d.id)) continue;
    for (const [iid, it] of itemsOf(d)) out.push({ deckId: d.id, itemId: iid, deck: d, it });
  }
  return out;
}
const progKey = (deckId, itemId) => deckId + '_' + itemId;
const progOf = (deckId, itemId) => S.progress[progKey(deckId, itemId)] || null;
const lastMissed = (pr) => !!pr && pr.r === 0;
function isDue(pr, now) {
  if (!pr || !Number(pr.t)) return true;
  if (lastMissed(pr)) return true;
  const n = Number(pr.n) || 0;
  const gap = Math.min(60, Math.pow(2, Math.max(0, n - 1)));
  return (now - Number(pr.t)) / DAY >= gap;
}
const isMastered = (pr) => !!pr && !lastMissed(pr) && (Number(pr.n) || 0) >= MASTERED_N;
function weightOf(it, pr, now) {
  const n = pr ? Math.max(0, Number(pr.n) || 0) : 0;
  const t = pr ? Number(pr.t) || 0 : 0;
  let days;
  if (!t) days = Math.max(NEW_DAYS, (now - (Number(it.c) || now)) / DAY);
  else {
    days = Math.max(0, (now - t) / DAY);
    if (lastMissed(pr)) days = Math.max(days, MISS_DAYS);
  }
  return (days + 1) / (n + 1);
}
function statusOf(pr, now) {
  if (!pr || !Number(pr.t)) return ['new', 'new'];
  if (lastMissed(pr)) return ['missed', 'missed last time'];
  if (isMastered(pr)) return ['mastered', 'mastered'];
  if (isDue(pr, now)) return ['due', 'due'];
  return null;
}
function deckStats(d, now) {
  const its = itemsOf(d);
  let due = 0, mastered = 0;
  for (const [iid] of its) { const pr = progOf(d.id, iid); if (isDue(pr, now)) due++; if (isMastered(pr)) mastered++; }
  return { total: its.length, due, mastered, masteredPct: its.length ? (mastered / its.length) * 100 : 0 };
}
// Weighted sampling without replacement (Efraimidis–Spirakis)
function draw(items, k) {
  const now = Date.now();
  return items
    .map(x => ({ x, key: Math.log(1 - Math.random()) / weightOf(x.it, progOf(x.deckId, x.itemId), now) }))
    .sort((a, b) => b.key - a.key).slice(0, k).map(o => o.x);
}
function shuffle(a) {
  for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; }
  return a;
}
function streakInfo() {
  const days = (S.myStats && S.myStats.days) || S.days || {};
  const d = new Date(); d.setHours(12, 0, 0, 0);
  const today = typeof days[dayKey(d)] === 'number' ? days[dayKey(d)] : Number(days[dayKey(d)] && days[dayKey(d)].n) || 0;
  if (!today) d.setDate(d.getDate() - 1);
  let count = 0;
  const cnt = (v) => (typeof v === 'number' ? v : Number(v && v.n) || 0);
  while (cnt(days[dayKey(d)]) > 0) { count++; d.setDate(d.getDate() - 1); }
  return { count, today };
}

async function createDeck({ name, kind, visibility, friendsCanEdit, allowPct, items }) {
  const ref = doc(collection(db, 'decks'));
  const data = {
    name: name.slice(0, 80), kind,
    visibility: visibility === 'shared' ? 'shared' : 'private',
    friendsCanEdit: visibility === 'shared' && !!friendsCanEdit,
    allowPct: typeof allowPct === 'number' ? allowPct : DEFAULT_ALLOW[kind],
    ownerId: myUid(), ownerName: myName().slice(0, 60),
    items: items || {},
  };
  await setDoc(ref, { ...data, createdAt: serverTimestamp(), updatedAt: serverTimestamp() });
  if (!S.decks.has(ref.id)) {   // show it right away, even before the live listener catches up
    const d = normDeck(ref.id, data);
    S.pendingDecks.set(ref.id, d);
    S.decks.set(ref.id, d);
  }
  return ref.id;
}
function itemsPatch(items, extra) {
  const patch = { updatedAt: serverTimestamp(), ...(extra || {}) };
  for (const [id, it] of Object.entries(items)) patch['items.' + id] = it;
  return patch;
}
const addItems = (deckId, items) => updateDoc(doc(db, 'decks', deckId), itemsPatch(items));
function removeItems(deckId, ids) {
  const patch = { updatedAt: serverTimestamp() };
  for (const id of ids) patch['items.' + id] = deleteField();
  return updateDoc(doc(db, 'decks', deckId), patch);
}

// Older versions had "universal" decks. Turn them into shared decks once, from the admin's side.
async function migrateLegacy() {
  if (!S.isAdmin || migrated || !S.decksLoaded || !S.peopleLoaded) return;
  migrated = true;
  const legacy = [...S.decks.values()].filter(d => d.legacyUniversal);
  if (!legacy.length) return;
  const editors = [...S.people.entries()].some(([uid, p]) => uid !== S.adminUid && p.active === true && p.canEditUniversal === true);
  for (const d of legacy) {
    await save(updateDoc(doc(db, 'decks', d.id), { scope: deleteField(), visibility: 'shared', friendsCanEdit: editors, updatedAt: serverTimestamp() }));
  }
}

// ---------------------------------------------------------------- boot and routing
function configMissing() {
  return !firebaseConfig || !firebaseConfig.apiKey || /PASTE/i.test(String(firebaseConfig.apiKey) + String(firebaseConfig.projectId));
}
function boot() {
  if (configMissing()) { S.phase = 'config'; render(); return; }
  app = initializeApp(firebaseConfig);
  auth = getAuth(app);
  try {
    db = initializeFirestore(app, { localCache: persistentLocalCache({ tabManager: persistentMultipleTabManager() }) });
  } catch (e) {
    db = initializeFirestore(app, {});
  }
  onSnapshot(doc(db, 'meta', 'admin'), (snap) => {
    if (!snap.exists() && snap.metadata.fromCache) return;   // wait for the server before deciding setup is needed
    const d = snap.exists() ? snap.data() : null;
    S.adminUid = d ? d.uid : null;
    S.adminName = d ? String(d.name || '') : '';
    S.metaLoaded = true;
    route();
  }, (e) => {
    console.error(e);
    S.metaLoaded = true; S.metaError = e;
    route();
  });
  onAuthStateChanged(auth, (u) => {
    S.fbUser = u; S.authLoaded = true;
    if (!u) teardown();
    route();
  });
}
function route() {
  if (S.phase === 'config') return render();
  if (!S.metaLoaded || !S.authLoaded) { S.phase = 'loading'; return render(); }
  if (S.metaError && !S.adminUid) { S.phase = 'config'; return render(); }
  if (!S.adminUid) { if (S.settingUp) return; S.phase = 'setup'; return render(); }
  const u = S.fbUser;
  if (!u) { S.phase = 'signin'; return render(); }
  const isAdmin = u.uid === S.adminUid;
  const key = u.uid + ':' + isAdmin;
  if (S.listenersFor !== key) {
    teardown();
    S.isAdmin = isAdmin; S.listenersFor = key;
    loadPrefs();
    startUser(u.uid);
  }
  if (!isAdmin && !S.meLoaded) { S.phase = 'loading'; return render(); }
  if (!isAdmin && !(S.me && S.me.active === true)) { S.phase = 'inactive'; return render(); }
  ensureData();
  S.phase = 'app';
  render();
}
function startUser(uid) {
  userUnsubs.push(onSnapshot(doc(db, 'users', uid), (s) => {
    if (!s.exists() && s.metadata.fromCache) return;
    S.me = s.exists() ? s.data() : null;
    S.meLoaded = true;
    const th = S.me && S.me.theme;
    if (th && th.id && stableStr(th) !== stableStr(S.themeSaved || {}) && !S.themePreview) { S.themeSaved = th; applyTheme(th); cacheTheme(th); }
    route();
  }, (e) => { console.error(e); S.me = null; S.meLoaded = true; route(); }));
  userUnsubs.push(onSnapshot(doc(db, 'requests', uid), (s) => {
    S.myRequest = s.exists() ? s.data() : null;
    if (S.phase === 'inactive') render();
  }, () => {}));
}
function ensureData() {
  const allowed = S.isAdmin || !!(S.me && S.me.active === true);
  if (allowed && !dataUnsubs) startData();
  if (!allowed && dataUnsubs) stopData();
}
function startData() {
  const uid = myUid();
  dataUnsubs = [];
  S.deckParts = {}; S.decksLoaded = false;
  const expected = S.isAdmin ? 1 : 2;
  const onErr = (e) => console.error(e);
  const part = (name) => (snap) => {
    const m = new Map();
    snap.forEach(d => m.set(d.id, normDeck(d.id, d.data())));
    S.deckParts[name] = m;
    const merged = new Map();
    for (const p of Object.values(S.deckParts)) for (const [k, v] of p) merged.set(k, v);
    for (const [k, v] of S.pendingDecks) { if (merged.has(k)) S.pendingDecks.delete(k); else merged.set(k, v); }
    S.decks = merged;
    S.decksLoaded = Object.keys(S.deckParts).length >= expected;
    refresh();
  };
  const decks = collection(db, 'decks');
  if (S.isAdmin) dataUnsubs.push(onSnapshot(decks, part('all'), onErr));
  else {
    dataUnsubs.push(onSnapshot(query(decks, where('ownerId', '==', uid)), part('mine'), onErr));
    dataUnsubs.push(onSnapshot(query(decks, where('visibility', '==', 'shared')), part('shared'), onErr));
  }
  dataUnsubs.push(onSnapshot(doc(db, 'progress', uid), (s) => {
    const d = s.exists() ? s.data() : {};
    S.progress = d.p || {};
    S.days = d.days || {};
    S.progressLoaded = true;
    refresh();
  }, onErr));
  dataUnsubs.push(onSnapshot(doc(db, 'stats', uid), (s) => {
    S.myStats = s.exists() ? s.data() : null;
    S.myStatsLoaded = true;
    refresh();
  }, (e) => { console.error(e); S.myStatsLoaded = true; }));
  dataUnsubs.push(onSnapshot(collection(db, 'profiles'), (snap) => {
    const m = new Map(); snap.forEach(d => m.set(d.id, d.data()));
    S.profiles = m; S.profilesLoaded = true; refresh();
  }, onErr));
  if (S.isAdmin) {
    dataUnsubs.push(onSnapshot(collection(db, 'users'), (snap) => {
      const m = new Map(); snap.forEach(d => m.set(d.id, d.data())); S.people = m; S.peopleLoaded = true; refresh();
    }, onErr));
    dataUnsubs.push(onSnapshot(collection(db, 'requests'), (snap) => {
      const m = new Map(); snap.forEach(d => m.set(d.id, d.data())); S.requests = m; refresh();
    }, onErr));
  }
}
function stopData() {
  if (dataUnsubs) dataUnsubs.forEach(u => u());
  dataUnsubs = null;
  S.decks = new Map(); S.deckParts = {}; S.decksLoaded = false; S.pendingDecks = new Map();
  S.progress = {}; S.days = {}; S.people = new Map(); S.peopleLoaded = false; S.requests = new Map();
  S.profiles = new Map(); S.profilesLoaded = false; S.stats = new Map(); S.friendsLoaded = false; S.friendsListening = false;
  S.myStats = null; S.myStatsLoaded = false; S.progressLoaded = false;
  clearTimeout(statsTimer); statsTimer = 0; statsSyncedOnce = false; S.legacyDaysCopied = false;
}
function teardown() {
  userUnsubs.forEach(u => u()); userUnsubs = [];
  stopData();
  S.listenersFor = null; S.me = null; S.meLoaded = false; S.myRequest = null; S.isAdmin = false;
  S.session = null; S.view = 'study'; S.authShown = null;
  S.dv = freshDv();
  S.add = { kind: 'facts', deckId: null, chosen: false };
  S.pp = { renaming: null };
  S.study = freshStudy();
  migrated = false;
  mounted.study = mounted.add = mounted.people = mounted.account = false;
}
let statsSyncedOnce = false;
function refresh() {
  if (S.phase !== 'app') return;
  migrateLegacy();
  syncProfiles();
  if (S.decksLoaded && S.progressLoaded && S.myStatsLoaded) { scheduleStatsSync(statsSyncedOnce ? 4000 : 300); statsSyncedOnce = true; }
  renderApp();
}

// ---------------------------------------------------------------- top-level render
function render() {
  const authPhase = ['config', 'setup', 'signin', 'inactive'].includes(S.phase);
  $('screen-loading').hidden = S.phase !== 'loading';
  $('screen-auth').hidden = !authPhase;
  $('screen-main').hidden = S.phase !== 'app';
  if (S.phase === 'config') renderConfig();
  else if (S.phase === 'setup') renderSetupAdmin();
  else if (S.phase === 'signin') renderSignin();
  else if (S.phase === 'inactive') renderInactive();
  else if (S.phase === 'app') renderApp();
}

// ---------------------------------------------------------------- auth screens
function authForm(onsubmit, ...kids) {
  return h('form', { class: 'stack-sm', novalidate: true, onsubmit: (e) => { e.preventDefault(); onsubmit(); } }, ...kids);
}
function renderConfig() {
  if (S.authShown === 'config') return; S.authShown = 'config';
  const msg = S.metaError
    ? "This site can't read its database. Check that Firestore is created and the security rules from firestore.rules are published, then reload."
    : 'Setup isn\'t finished. Paste your Firebase config into firebase-config.js, upload the files again, and reload this page.';
  put($('authBox'), h('h1', { text: 'Almost there' }), h('p', { text: msg }));
}
function renderSetupAdmin() {
  const variant = S.fbUser ? 'finish' : 'new';
  if (S.authShown === 'setup:' + variant) return; S.authShown = 'setup:' + variant;
  const status = h('p', { class: 'status', role: 'status' });
  const name = h('input', { type: 'text', id: 'suName', autocomplete: 'name', maxlength: '60' });
  const email = h('input', { type: 'email', id: 'suEmail', autocomplete: 'username' });
  const pw = h('input', { type: 'password', id: 'suPw', autocomplete: 'new-password' });
  const pw2 = h('input', { type: 'password', id: 'suPw2', autocomplete: 'new-password' });
  const btn = h('button', { type: 'submit', class: 'btn primary big' }, variant === 'new' ? 'Create admin account' : 'Finish setup');
  const fail = (m) => { status.className = 'status err'; status.textContent = m; btn.disabled = false; S.settingUp = false; };
  const submit = async () => {
    const n = name.value.trim();
    if (!n) return fail('Add your name.');
    btn.disabled = true; status.className = 'status'; status.textContent = 'Setting things up…';
    S.settingUp = true;
    try {
      let user = S.fbUser;
      if (!user) {
        const e = email.value.trim();
        if (!e) return fail('Add your email.');
        if (pw.value.length < 8) return fail('Use a password with at least 8 characters.');
        if (pw.value !== pw2.value) return fail("The two passwords don't match.");
        user = (await createUserWithEmailAndPassword(auth, e, pw.value)).user;
      }
      await setDoc(doc(db, 'meta', 'admin'), { uid: user.uid, name: n, createdAt: serverTimestamp() });
      await setDoc(doc(db, 'users', user.uid), { name: n, email: user.email || '', active: true, createdAt: serverTimestamp() });
      S.settingUp = false;
      route();
    } catch (e) {
      console.error(e);
      const c = (e && e.code) || '';
      fail(c.includes('permission-denied') ? 'Someone else already set up this site. Sign in instead, or check your Firestore rules.' : authError(e));
    }
  };
  const kids = variant === 'new'
    ? [field('Your name', name), field('Email', email), field('Password (8+ characters)', pw), field('Password again', pw2)]
    : [field('Your name', name)];
  put($('authBox'),
    h('h1', { text: 'Create the admin account' }),
    h('p', { text: 'This first account runs the site: it creates everyone else\'s accounts and can see every deck.' }),
    authForm(submit, ...kids, btn, status),
    S.fbUser ? h('button', { type: 'button', class: 'linkbtn quiet', onclick: () => signOut(auth) }, 'Sign out') : null
  );
}
function signinNote() {
  return S.adminName ? `Accounts are made by ${S.adminName}. Ask them if you need one.` : 'Accounts are made by the admin. Ask them if you need one.';
}
function renderSignin() {
  if (S.authShown === 'signin') { const p = $('signinNote'); if (p) p.textContent = signinNote(); return; }
  S.authShown = 'signin';
  const status = h('p', { class: 'status', role: 'status' });
  const email = h('input', { type: 'email', id: 'siEmail', autocomplete: 'username' });
  const pw = h('input', { type: 'password', id: 'siPw', autocomplete: 'current-password' });
  const btn = h('button', { type: 'submit', class: 'btn primary big' }, 'Sign in');
  const submit = async () => {
    if (!email.value.trim() || !pw.value) { status.className = 'status err'; status.textContent = 'Enter your email and password.'; return; }
    btn.disabled = true; status.className = 'status'; status.textContent = 'Signing in…';
    try { await signInWithEmailAndPassword(auth, email.value.trim(), pw.value); }
    catch (e) { status.className = 'status err'; status.textContent = authError(e); btn.disabled = false; }
  };
  const forgot = async () => {
    const e = email.value.trim();
    if (!e) { status.className = 'status err'; status.textContent = 'Type your email above first.'; email.focus(); return; }
    try { await sendPasswordResetEmail(auth, e); status.className = 'status ok'; status.textContent = 'If that email has an account, a link to set a new password is on its way. Check spam too.'; }
    catch (err) { status.className = 'status err'; status.textContent = authError(err); }
  };
  const showPw = h('button', { type: 'button', class: 'linkbtn quiet', onclick: () => { pw.type = pw.type === 'password' ? 'text' : 'password'; showPw.textContent = pw.type === 'password' ? 'Show password' : 'Hide password'; } }, 'Show password');
  put($('authBox'),
    h('h1', { text: 'Sign in' }),
    h('p', { id: 'signinNote', text: signinNote() }),
    authForm(submit, field('Email', email), field('Password', pw), h('div', null, showPw), btn, status),
    h('div', null, h('button', { type: 'button', class: 'linkbtn', onclick: forgot }, 'Forgot your password?'))
  );
}
function renderInactive() {
  const variant = S.me ? 'off' : (S.myRequest ? 'requested' : 'none');
  if (S.authShown === 'inactive:' + variant) return; S.authShown = 'inactive:' + variant;
  const who = S.adminName || 'the admin';
  const out = h('button', { type: 'button', class: 'btn ghost', onclick: () => signOut(auth) }, 'Sign out');
  if (variant === 'off') {
    put($('authBox'), h('h1', { text: 'Your account is turned off' }), h('p', { text: `Ask ${who} to turn it back on. Your decks and progress are still saved.` }), out);
    return;
  }
  if (variant === 'requested') {
    put($('authBox'), h('h1', { text: 'Request sent' }), h('p', { text: `${who} will see your request on their People page. This page opens up as soon as they approve it.` }), out);
    return;
  }
  const name = h('input', { type: 'text', id: 'rqName', maxlength: '60', autocomplete: 'name' });
  const status = h('p', { class: 'status', role: 'status' });
  const send = async () => {
    const n = name.value.trim();
    if (!n) { status.className = 'status err'; status.textContent = 'Add your name so they know who you are.'; return; }
    try { await setDoc(doc(db, 'requests', myUid()), { name: n, email: S.fbUser.email || '', at: serverTimestamp() }); }
    catch (e) { status.className = 'status err'; status.textContent = dataError(e); }
  };
  put($('authBox'),
    h('h1', { text: "You're signed in, but not added yet" }),
    h('p', { text: `Ask ${who} to let you in. Send a request and it will show up for them.` }),
    authForm(send, field('Your name', name), h('button', { type: 'submit', class: 'btn primary' }, 'Request access'), status),
    out
  );
}

// ---------------------------------------------------------------- app shell
const mounted = { study: false, add: false, people: false, account: false };

function go(view) {
  if (S.themePreview) closeCustomEditor(true);
  S.view = view;
  if (view === 'decks') S.dv = freshDv();
  if (view === 'account') mounted.account = false;
  renderApp();
  window.scrollTo({ top: 0 });
}
function renderTop() {
  $('peopleTab').hidden = !S.isAdmin;
  $('peopleTab').textContent = 'People' + (S.isAdmin && S.requests.size ? ` (${S.requests.size})` : '');
  for (const b of document.querySelectorAll('.tab')) b.setAttribute('aria-selected', b.dataset.view === S.view ? 'true' : 'false');
  const who = $('whoBtn');
  const nm = myName();
  const initials = nm.split(/\s+/).filter(Boolean).slice(0, 2).map(w => w[0].toUpperCase()).join('') || '?';
  put(who, h('span', { class: 'who-full', text: nm }), h('span', { class: 'who-short', text: initials, 'aria-hidden': 'true' }));
  who.title = S.isAdmin ? 'Your account (admin)' : 'Your account';
  if (S.view === 'account') who.setAttribute('aria-current', 'page'); else who.removeAttribute('aria-current');
}
function renderApp() {
  if (S.view === 'people' && !S.isAdmin) S.view = 'study';
  renderTop();
  for (const v of ['study', 'decks', 'add', 'friends', 'people', 'account']) $('view-' + v).hidden = S.view !== v;
  if (S.view === 'study') renderStudy();
  else if (S.view === 'decks') renderDecks();
  else if (S.view === 'add') renderAdd();
  else if (S.view === 'friends') renderFriends();
  else if (S.view === 'people') renderPeople();
  else if (S.view === 'account') renderAccount();
}

// ---------------------------------------------------------------- study: setup
const curCount = () => S.study.count[S.study.kind];
function setCount(n) {
  const k = S.study.kind;
  S.study.count[k] = clampInt(n, 1, k === 'poems' ? 50 : 200, k === 'poems' ? 1 : 10);
  savePrefs(); renderSetup();
}
function mountStudy() {
  mounted.study = true;
  const input = h('input', { type: 'number', inputmode: 'numeric', id: 'countInput', min: '1', 'aria-labelledby': 'countLabel' });
  input.addEventListener('input', () => { if (input.value !== '') setCount(input.value); });
  input.addEventListener('blur', () => { input.value = curCount(); });
  put($('study-setup'),
    h('div', { class: 'row', style: 'align-items:flex-start' },
      h('div', { style: 'flex:1 1 18rem;min-width:0' }, h('h1', { text: 'Draw a set to write out' }), h('p', { class: 'streak', id: 'streakLine' })),
      seg('studyKind', [['facts', 'Facts'], ['poems', 'Poems']], S.study.kind, (k) => { S.study.kind = k; savePrefs(); renderSetup(); })
    ),
    h('div', { id: 'studyLoading', class: 'block-note' }, h('p', { text: 'Loading your decks…' })),
    h('div', { id: 'studyEmpty', class: 'block-note', hidden: true },
      h('p', { id: 'studyEmptyText' }),
      h('button', { type: 'button', class: 'btn primary', onclick: () => { S.add.kind = S.study.kind; S.add.chosen = false; go('add'); } }, 'Add some')),
    h('div', { id: 'studyMain', class: 'stack', hidden: true },
      h('div', null, h('span', { class: 'label', text: 'Draw from' }), h('div', { class: 'chip-groups', id: 'chipGroups' })),
      h('div', null,
        h('span', { class: 'label', id: 'countLabel' }),
        h('div', { class: 'count-row' },
          h('div', { class: 'stepper', role: 'group', 'aria-labelledby': 'countLabel' },
            h('button', { type: 'button', 'aria-label': 'One fewer', onclick: () => setCount(curCount() - 1) }, '−'),
            input,
            h('button', { type: 'button', 'aria-label': 'One more', onclick: () => setCount(curCount() + 1) }, '+')),
          h('div', { class: 'presets', id: 'presets' }))),
      h('div', { class: 'opts' },
        h('div', null, h('span', { class: 'label', text: "How you'll answer" }),
          seg('answerMode', [['paper', 'On paper'], ['type', 'Type it']], S.study.mode, (k) => { S.study.mode = k; savePrefs(); renderSetup(); }),
          h('p', { class: 'help', id: 'modeHelp', style: 'margin-top:.45rem' })),
        h('div', null, h('label', { class: 'label', for: 'allowSel', text: 'Allowed mistakes' }),
          allowSelect('allowSel', S.study.allow, (v) => { S.study.allow = v; savePrefs(); renderSetup(); }, true),
          h('p', { class: 'help', id: 'allowHelp', style: 'margin-top:.45rem' }))),
      h('dl', { class: 'stats', id: 'poolStats' }),
      h('div', { id: 'likelyWrap' }, h('span', { class: 'label', text: 'Most likely to come up' }), h('ul', { class: 'likely', id: 'likely' })),
      h('div', null, h('button', { type: 'button', class: 'btn primary big', id: 'startBtn', onclick: () => startSession() }, 'Draw')),
      h('details', { class: 'how' },
        h('summary', { text: 'How picking and checking work' }),
        h('div', { class: 'formula', text: 'weight = (days since you last wrote it + 1) ÷ (times you got it right + 1)' }),
        h('p', { text: 'Each item gets a weight and the draw picks without repeats, so heavier items are more likely but nothing is guaranteed. Items you\'ve never written count as at least 30 days overdue. Items you missed last time count as at least 14 days overdue, and they come back once more at the end of the same set (that retry is practice and isn\'t recorded).' }),
        h('p', { text: 'Due: never written, missed last time, or longer ago than its spacing (1 day after the first right answer, then 2, 4, 8… up to 60 days). Mastered: right at least 3 times, including the last time.' }),
        h('p', { text: 'Allowed mistakes: typed facts are compared letter by letter, typed poems word by word; capitals, accents and punctuation are ignored. On paper, poems ask how many lines you missed. You can always overrule a result.' }))
    )
  );
}
function renderStudy() {
  if (!mounted.study) mountStudy();
  const s = S.session;
  $('study-setup').hidden = !!s;
  $('study-session').hidden = !s || s.finished;
  $('study-done').hidden = !s || !s.finished;
  if (!s) renderSetup();
  else if (s.finished) renderDone();
  else renderCard();
}
function chip(label, n, on, onclick, extra, key, by) {
  return h('button', { type: 'button', class: 'chip' + (extra ? ' ' + extra : ''), 'aria-pressed': on ? 'true' : 'false', 'data-key': key, onclick },
    h('span', { class: 'nm', text: label }), by ? h('span', { class: 'by', text: 'by ' + by }) : null, h('span', { class: 'n', text: Number(n).toLocaleString() }));
}
function renderSetup() {
  const kind = S.study.kind;
  setSeg('studyKind', kind);
  setSeg('answerMode', S.study.mode);
  const st = streakInfo();
  put($('streakLine'),
    st.count ? h('span', null, h('b', { text: String(st.count) }), ' day streak') : h('span', { text: 'Write something today to start a streak' }),
    st.today ? h('span', null, h('b', { text: String(st.today) }), ' written today') : null);
  const decks = studyDecks(kind);
  const sel = S.study.sel[kind];
  const loading = !S.decksLoaded;
  if (!loading) for (const id of [...sel]) if (!decks.some(d => d.id === id)) sel.delete(id);
  const all = pool(kind, null);
  $('studyLoading').hidden = !loading;
  $('studyEmpty').hidden = loading || all.length > 0;
  $('studyMain').hidden = loading || all.length === 0;
  $('studyEmptyText').textContent = kind === 'poems'
    ? 'No poems yet. Add one and it will be ready to draw here.'
    : 'No facts yet. Paste a batch and they will be ready to draw here.';
  if (loading || !all.length) return;

  const box = $('chipGroups');
  const toggle = (id) => { if (sel.has(id)) sel.delete(id); else sel.add(id); savePrefs(); renderSetup(); };
  withFocus(box, () => put(box,
    h('div', { class: 'chips' }, chip(kind === 'poems' ? 'All poems' : 'All facts', all.length, sel.size === 0, () => { sel.clear(); savePrefs(); renderSetup(); }, 'pool', 'all')),
    ...[['mine', 'Mine'], ['shared', 'Shared by friends']].map(([cat, label]) => {
      const ds = decks.filter(d => category(d) === cat);
      if (!ds.length) return null;
      return h('div', { class: 'chip-group' }, h('h3', { text: label }),
        h('div', { class: 'chips' }, ...ds.map(d => chip(d.name, itemsOf(d).length, sel.has(d.id), () => toggle(d.id), '', d.id, cat === 'shared' ? ownerLabel(d) : null))));
    })));

  const items = pool(kind, sel);
  const now = Date.now();
  $('countLabel').textContent = kind === 'poems' ? 'How many poems' : 'How many facts';
  const input = $('countInput');
  input.max = kind === 'poems' ? '50' : '200';
  if (document.activeElement !== input) input.value = curCount();
  const presets = kind === 'poems' ? [1, 2, 3, 5] : [5, 10, 20, 40];
  put($('presets'), ...presets.map(n => h('button', { type: 'button', class: 'preset', 'aria-pressed': n === curCount() ? 'true' : 'false', onclick: () => setCount(n) }, String(n))));

  const paperFacts = S.study.mode === 'paper' && kind === 'facts';
  $('modeHelp').textContent = S.study.mode === 'paper'
    ? (kind === 'poems' ? 'Write it out, reveal it, then count the lines you missed.' : 'Write it out, reveal it, then mark Got it or Missed it.')
    : 'Type your answer and the site checks it. You can overrule it.';
  const allowSel = $('allowSel');
  if (document.activeElement !== allowSel) allowSel.value = String(S.study.allow);
  const deckAllows = [...new Set(decks.filter(d => !sel.size || sel.has(d.id)).map(d => d.allowPct))].sort((a, b) => a - b);
  $('allowHelp').textContent = paperFacts
    ? 'On paper, facts are simply right or wrong. This applies when you type.'
    : (S.study.allow === 'deck'
      ? (deckAllows.length === 1 ? `These decks allow ${deckAllows[0]}%.` : `These decks allow ${deckAllows.map(n => n + '%').join(', ')}.`)
      : "Overrides each deck's standard for this set.");

  let due = 0, mastered = 0;
  for (const x of items) { const pr = progOf(x.deckId, x.itemId); if (isDue(pr, now)) due++; if (isMastered(pr)) mastered++; }
  put($('poolStats'),
    h('div', null, h('dt', { text: 'In this pool' }), h('dd', { text: items.length.toLocaleString() })),
    h('div', null, h('dt', { text: 'Due now' }), h('dd', { text: due.toLocaleString() })),
    h('div', null, h('dt', { text: 'Mastered' }), h('dd', { text: items.length ? pct(mastered / items.length * 100) : '0%' })));

  const ranked = items.map(x => ({ x, w: weightOf(x.it, progOf(x.deckId, x.itemId), now) })).sort((a, b) => b.w - a.w).slice(0, 3);
  const maxW = ranked.length ? ranked[0].w : 1;
  put($('likely'), ...ranked.map(r => h('li', null,
    h('span', { class: 'lp', text: kind === 'poems' ? r.x.it.title : r.x.it.p }),
    h('span', { class: 'bar', 'aria-hidden': 'true' }, h('i', { style: `width:${Math.max(6, Math.round(r.w / maxW * 100))}%` })))));
  $('likelyWrap').hidden = items.length < 2;

  const k = Math.min(curCount(), items.length);
  const noun = kind === 'poems' ? 'poem' : 'fact';
  const b = $('startBtn');
  b.disabled = !items.length;
  b.textContent = !items.length ? `No ${noun}s in these decks` : (items.length < curCount() ? `Draw all ${plural(items.length, noun)}` : `Draw ${plural(k, noun)}`);
}

// ---------------------------------------------------------------- study: session
function startSession(refs) {
  const kind = S.study.kind;
  let queue;
  if (refs) queue = refs.map(r => ({ deckId: r.deckId, itemId: r.itemId, retry: false }));
  else {
    const items = pool(kind, S.study.sel[kind]);
    if (!items.length) return;
    queue = shuffle(draw(items, Math.min(curCount(), items.length))).map(x => ({ deckId: x.deckId, itemId: x.itemId, retry: false }));
  }
  S.session = { kind, mode: S.study.mode, allow: S.study.allow, queue, i: 0, phase: 'ask', hint: 0, typed: '', linesMissed: 0, check: null, override: null, results: [], undo: [], finished: false };
  $('typeInput').value = '';
  renderStudy();
  window.scrollTo({ top: 0 });
  focusPrimary();
}
function currentItem() {
  const s = S.session;
  while (s && s.i < s.queue.length) {
    const ref = s.queue[s.i];
    const d = S.decks.get(ref.deckId);
    const it = d && d.items[ref.itemId];
    if (it && typeof it === 'object') return { ref, d, it };
    s.i++; resetCard(s);   // deleted mid-set
  }
  return null;
}
function resetCard(s) { s.phase = 'ask'; s.hint = 0; s.typed = ''; s.linesMissed = 0; s.check = null; s.override = null; }
const allowFor = (s, d) => (s.allow === 'deck' ? d.allowPct : Number(s.allow));

// The result after reveal or check: right/missed, and how far off when that applies.
function outcome(s, d, it) {
  const poem = s.kind === 'poems';
  const allow = allowFor(s, d);
  let right = null, off = null;
  if (s.mode === 'type' && s.check) { off = s.check.off; right = off <= allow + 1e-9; }
  else if (s.mode === 'paper' && poem) { const lines = Math.max(1, poemLines(it.text)); off = (s.linesMissed / lines) * 100; right = off <= allow + 1e-9; }
  if (s.override != null) right = s.override;
  return { right, off, allow };
}
function verdictText(o, overruled) {
  const base = o.right
    ? (o.off != null && o.off > 0 ? `Counts as right · ${pct(o.off)} off, ${o.allow}% allowed` : 'Right')
    : `Counts as missed · ${pct(o.off || 0)} off, ${o.allow}% allowed`;
  return base + (overruled ? ' (your call)' : '');
}

function renderCard() {
  const s = S.session;
  const cur = currentItem();
  if (!cur) { s.finished = true; renderStudy(); return; }
  const { ref, d, it } = cur;
  const poem = s.kind === 'poems';
  const now = Date.now();
  const pr = progOf(ref.deckId, ref.itemId);
  const n = pr ? Number(pr.n) || 0 : 0;
  const shown = s.phase === 'shown';
  const typed = s.mode === 'type';

  $('sessProgress').textContent = `${s.i + 1} / ${s.queue.length}`;
  $('sessBar').style.width = `${Math.round(s.i / s.queue.length * 100)}%`;
  $('undoBtn').hidden = !s.undo.length;
  $('cardDeck').textContent = d.name;
  $('cardMeta').textContent = ref.retry ? 'retry · practice only'
    : (pr && Number(pr.t) ? `${lastMissed(pr) ? 'missed last time' : `right ${n}×`} · ${ago(Number(pr.t), now)}` : 'first time');
  $('cardPrompt').textContent = poem ? it.title : it.p;
  const by = $('cardByline');
  by.hidden = !poem;
  if (poem) by.textContent = [it.author ? 'by ' + it.author : '', plural(poemLines(it.text), 'line')].filter(Boolean).join(' · ');

  const hint = $('cardHint');
  hint.hidden = shown;
  hint.textContent = typed
    ? (poem ? 'Type the whole poem from memory, then check it.' : 'Type the answer, then check it.')
    : (poem ? 'Write the whole poem from memory, then reveal it to check.' : 'Write the answer on paper, then reveal it.');
  const hl = $('cardHintLines');
  hl.hidden = !(poem && !shown && s.hint > 0);
  hl.textContent = s.hint === 1 ? poemFirstLine(it.text) : (s.hint === 2 ? poemFirstWords(it.text) : '');

  const ans = $('cardAnswer');
  const wasHidden = ans.hidden;
  ans.className = 'answer hand' + (poem ? ' poem' : '');
  if (shown && typed && s.check) put(ans, ...renderTokens(s.check.et, 'exp'));
  else ans.textContent = poem ? it.text : it.a;
  ans.hidden = !shown;
  if (shown && wasHidden) { void ans.offsetWidth; ans.classList.add('show'); }

  const tb = $('typeBox'), ti = $('typeInput');
  tb.hidden = !(typed && !shown);
  if (typed && !shown) {
    ti.className = poem ? 'poem' : '';
    ti.rows = poem ? 12 : 2;
    $('typeLabel').textContent = poem ? 'Your poem' : 'Your answer';
    if (ti.value !== s.typed) ti.value = s.typed;
  }
  const tc = $('typedCopy');
  tc.hidden = !(shown && typed && s.check);
  if (shown && typed && s.check) put($('typedText'), s.typed.trim() ? renderTokens(s.check.tt, 'typed') : h('em', { text: '(nothing typed)' }));

  const vb = $('verdictBox');
  vb.hidden = !shown || (!typed && !poem);
  if (shown && (typed || poem)) {
    const o = outcome(s, d, it);
    const overruled = s.override != null;
    const flip = h('button', { type: 'button', class: 'linkbtn', onclick: () => { s.override = overruled ? null : !o.right; renderCard(); } },
      overruled ? 'Undo my call' : (o.right ? 'Count it as missed' : 'Count it as right'));
    const line = h('div', { class: 'verdict ' + (o.right ? 'ok' : 'bad'), id: 'verdictLine' }, h('span', { text: verdictText(o, overruled) }), flip);
    if (!typed && poem) {
      const lines = poemLines(it.text);
      const stepInput = h('input', { type: 'number', id: 'linesMissed', min: '0', max: String(lines), value: String(s.linesMissed), 'aria-label': 'Lines missed', inputmode: 'numeric' });
      stepInput.addEventListener('input', () => { s.linesMissed = clampInt(stepInput.value, 0, lines, 0); s.override = null; renderVerdictOnly(); });
      const bump = (dlt) => { s.linesMissed = clampInt(s.linesMissed + dlt, 0, lines, 0); s.override = null; stepInput.value = String(s.linesMissed); renderVerdictOnly(); };
      put(vb, h('div', { class: 'stack-sm' },
        h('div', { class: 'lines-missed' },
          h('span', { class: 'label', style: 'margin:0', text: 'Lines I missed' }),
          h('div', { class: 'stepper', role: 'group', 'aria-label': 'Lines missed' },
            h('button', { type: 'button', 'aria-label': 'One fewer', onclick: () => bump(-1) }, '−'),
            stepInput,
            h('button', { type: 'button', 'aria-label': 'One more', onclick: () => bump(1) }, '+')),
          h('span', { class: 'help', text: `of ${lines}` })),
        line));
    } else {
      const gaps = (s.check && s.check.gaps) || [];
      put(vb, h('div', { class: 'stack-sm' }, line,
        gaps.length ? h('p', { class: 'missing' }, h('b', { text: 'Missing: ' }),
          gaps.slice(0, 10).map(g => `“${g}”`).join(', ') + (gaps.length > 10 ? `, and ${gaps.length - 10} more` : '')) : null));
    }
  }

  const left = [];
  const right = [];
  if (!shown) {
    left.push(h('button', { type: 'button', class: 'linkbtn quiet', onclick: skip }, "Skip, don't count it"));
    if (poem && s.hint < 2) left.push(h('button', { type: 'button', class: 'linkbtn', onclick: () => { s.hint++; renderCard(); } }, s.hint === 0 ? 'Hint: first line' : 'Hint: first words'));
    right.push(h('button', { type: 'button', class: 'btn primary big', 'data-primary': '1', onclick: revealOrCheck }, typed ? 'Check' : (poem ? 'Reveal the poem' : 'Reveal answer')));
  } else if (!typed && !poem) {
    right.push(h('button', { type: 'button', class: 'btn miss big', onclick: () => commit(false) }, 'Missed it'));
    right.push(h('button', { type: 'button', class: 'btn primary big', 'data-primary': '1', onclick: () => commit(true) }, 'Got it'));
  } else {
    const last = s.i + 1 >= s.queue.length;
    right.push(h('button', { type: 'button', class: 'btn primary big', 'data-primary': '1', onclick: () => commit(outcome(s, d, it).right) }, last ? 'Finish set' : 'Next'));
  }
  put($('sessActions'), h('div', { class: 'row' }, ...left), h('div', { class: 'main' }, ...right));

  const u = s.undo.length ? ' · U undo' : '';
  $('keysHint').textContent = !shown
    ? (typed ? (poem ? 'Ctrl/⌘ + Enter checks' : 'Enter checks') : 'Space reveals · S skips' + (poem ? ' · H hint' : '')) + u
    : (!typed && !poem ? '← or 1 missed · → or 2 got it' : 'Enter next') + u;
}
function renderVerdictOnly() {
  const s = S.session; const cur = currentItem(); if (!cur) return;
  const o = outcome(s, cur.d, cur.it);
  const line = $('verdictLine'); if (!line) return;
  line.className = 'verdict ' + (o.right ? 'ok' : 'bad');
  line.firstChild.textContent = verdictText(o, false);
  line.lastChild.textContent = o.right ? 'Count it as missed' : 'Count it as right';
}
function focusPrimary() {
  const s = S.session; if (!s || s.finished) return;
  if (s.mode === 'type' && s.phase === 'ask') { $('typeInput').focus({ preventScroll: true }); return; }
  const b = $('sessActions').querySelector('[data-primary]');
  if (b) b.focus({ preventScroll: true });
}
function revealOrCheck() {
  const s = S.session; if (!s || s.finished || s.phase !== 'ask') return;
  const cur = currentItem(); if (!cur) return;
  if (s.mode === 'type') {
    s.typed = $('typeInput').value;
    const poem = s.kind === 'poems';
    s.check = grade(poem ? cur.it.text : cur.it.a, s.typed, s.kind);
  }
  s.phase = 'shown';
  renderCard();
  focusPrimary();
}
function record(ref, right) {
  const key = progKey(ref.deckId, ref.itemId);
  const prev = S.progress[key] || null;
  const day = dayKey();
  const entry = {
    n: (prev ? Number(prev.n) || 0 : 0) + (right ? 1 : 0),
    m: (prev ? Number(prev.m) || 0 : 0) + (right ? 0 : 1),
    t: Date.now(), r: right ? 1 : 0,
  };
  save(setDoc(doc(db, 'progress', myUid()), { p: { [key]: entry }, updatedAt: serverTimestamp() }, { merge: true }));
  save(setDoc(doc(db, 'stats', myUid()), { days: { [day]: { n: increment(1), r: increment(right ? 1 : 0) } }, lastActive: Date.now() }, { merge: true }));
  scheduleStatsSync(2500);
  return { key, prev, day, right };
}
function snapshotSession(s) { const { undo: _u, ...rest } = s; return JSON.parse(JSON.stringify(rest)); }
function commit(right) {
  const s = S.session; if (!s || s.finished || s.phase !== 'shown') return;
  const cur = currentItem(); if (!cur) return;
  const snap = snapshotSession(s);
  const o = outcome(s, cur.d, cur.it);
  const write = cur.ref.retry ? null : record(cur.ref, right);
  s.results.push({ deckId: cur.ref.deckId, itemId: cur.ref.itemId, retry: cur.ref.retry, right, off: o.off, hinted: s.hint > 0, overruled: s.override != null });
  if (!right && !cur.ref.retry) s.queue.push({ deckId: cur.ref.deckId, itemId: cur.ref.itemId, retry: true });
  s.undo.push({ snap, write });
  advance();
}
function skip() {
  const s = S.session; if (!s || s.finished) return;
  const cur = currentItem(); if (!cur) return;
  const snap = snapshotSession(s);
  s.results.push({ deckId: cur.ref.deckId, itemId: cur.ref.itemId, retry: cur.ref.retry, skipped: true });
  s.undo.push({ snap, write: null });
  advance();
}
function advance() {
  const s = S.session;
  s.i++; resetCard(s);
  $('typeInput').value = '';
  if (s.i >= s.queue.length) s.finished = true;
  renderStudy();
  if (!s.finished) { window.scrollTo({ top: 0 }); focusPrimary(); }
  else { const a = $('againBtn'); if (a) a.focus({ preventScroll: true }); }
}
function undo() {
  const s = S.session; if (!s || !s.undo.length) return;
  const last = s.undo.pop();
  if (last.write) {
    const { key, prev, day, right } = last.write;
    save(setDoc(doc(db, 'progress', myUid()), { p: { [key]: prev || deleteField() }, updatedAt: serverTimestamp() }, { merge: true }));
    save(setDoc(doc(db, 'stats', myUid()), { days: { [day]: { n: increment(-1), r: increment(right ? -1 : 0) } } }, { merge: true }));
    scheduleStatsSync(2500);
  }
  const stack = s.undo;
  S.session = Object.assign(last.snap, { undo: stack, finished: false });
  $('typeInput').value = S.session.typed || '';
  renderStudy();
  window.scrollTo({ top: 0 });
  focusPrimary();
}
function endSet() {
  const s = S.session; if (!s) return;
  if (!s.results.some(r => !r.skipped)) { S.session = null; renderStudy(); return; }
  s.finished = true; renderStudy();
}
function renderDone() {
  const s = S.session;
  const poem = s.kind === 'poems';
  const noun = poem ? 'poem' : 'fact';
  const main = s.results.filter(r => !r.retry && !r.skipped);
  const right = main.filter(r => r.right);
  const missed = main.filter(r => !r.right);
  const retries = new Map(s.results.filter(r => r.retry && !r.skipped).map(r => [r.deckId + '_' + r.itemId, r.right]));
  const skipped = s.results.filter(r => r.skipped && !r.retry).length;
  const lede = main.length
    ? `${right.length} of ${main.length} right (${pct(right.length / main.length * 100)})` + (skipped ? `, ${skipped} skipped` : '') + '.'
    : 'Nothing recorded.';
  const row = (r) => {
    const d = S.decks.get(r.deckId); const it = d && d.items[r.itemId];
    if (!it) return null;
    const notes = [];
    if (r.off != null && r.off > 0) notes.push(`${pct(r.off)} off`);
    if (r.hinted) notes.push('used a hint');
    if (r.overruled) notes.push('your call');
    const rt = retries.get(r.deckId + '_' + r.itemId);
    if (!r.right && rt != null) notes.push(rt ? 'right on retry' : 'missed on retry');
    return h('li', null,
      h('span', { class: 'dp hand', text: poem ? it.title : it.p }),
      h('span', { class: 'da' + (poem ? '' : ' hand'), text: [poem ? (it.author || '') : it.a, ...notes].filter(Boolean).join(' · ') }));
  };
  put($('study-done'),
    h('div', null,
      h('h1', { text: main.length ? (missed.length ? 'Set finished' : 'Clean sweep') : 'Set ended' }),
      h('p', { class: 'lede', text: lede })),
    missed.length ? h('div', { class: 'deck-section' }, h('h3', { text: 'Missed' }), h('ul', { class: 'done-list' }, ...missed.map(row))) : null,
    right.length ? h('div', { class: 'deck-section' }, h('h3', { text: 'Right' }), h('ul', { class: 'done-list' }, ...right.map(row))) : null,
    h('div', { class: 'row' },
      missed.length ? h('button', { type: 'button', class: 'btn primary big', id: 'againBtn', onclick: () => startSession(missed.map(r => ({ deckId: r.deckId, itemId: r.itemId }))) }, `Practice the ${plural(missed.length, 'miss', 'misses')} again`) : null,
      h('button', { type: 'button', class: missed.length ? 'btn ghost big' : 'btn primary big', id: missed.length ? 'drawBtn' : 'againBtn', onclick: () => { S.session = null; startSession(); } }, 'Draw another set'),
      h('button', { type: 'button', class: 'btn ghost big', onclick: () => { S.session = null; renderStudy(); } }, 'Change decks or count')),
    s.undo.length ? h('div', null, h('button', { type: 'button', class: 'linkbtn quiet', onclick: undo }, `Undo the last ${noun}`)) : null
  );
}

// ---------------------------------------------------------------- decks
function deckPills(d) {
  return [
    h('span', { class: 'pill kind', text: d.kind === 'poems' ? 'Poems' : 'Facts' }),
    h('span', { class: 'pill ' + (d.visibility === 'shared' ? 'shared' : 'private'), text: d.visibility === 'shared' ? 'Shared' : 'Private' }),
    d.visibility === 'shared' && d.friendsCanEdit ? h('span', { class: 'pill edit', text: 'Friends can edit' }) : null,
  ];
}
function deckRow(d, showOwner, now) {
  const st = deckStats(d, now);
  const studyable = category(d) !== 'other';
  return h('li', { class: 'deck-row' },
    h('div', { style: 'min-width:0' },
      h('button', { type: 'button', class: 'dn', onclick: () => openDeck(d.id) }, d.name),
      h('div', { class: 'dm' }, ...deckPills(d), showOwner ? h('span', { text: 'by ' + ownerLabel(d) }) : null,
        h('span', { text: plural(st.total, d.kind === 'poems' ? 'poem' : 'fact') + (studyable && st.total ? ` · ${st.due} due` : '') }))),
    studyable && st.total ? h('div', { class: 'mastery', title: 'Mastered: right at least 3 times, including the last time' },
      h('span', { class: 'bar', 'aria-hidden': 'true' }, h('i', { style: `width:${Math.round(st.masteredPct)}%` })),
      h('span', { class: 'mono', text: pct(st.masteredPct) + ' mastered' })) : h('span'));
}
function openDeck(id) {
  S.dv = { ...freshDv(), open: id };
  renderDecks(true);
  window.scrollTo({ top: 0 });
}
function renderDecks(force) {
  const root = $('view-decks');
  if (!force && (S.dv.editing || S.dv.renaming || S.dv.creating)) return;   // keep forms the person is typing in
  if (!S.decksLoaded) { put(root, h('div', { class: 'block-note' }, h('p', { text: 'Loading your decks…' }))); return; }
  if (S.dv.open && S.decks.has(S.dv.open)) return renderDeckDetail(root);
  S.dv.open = null;

  const now = Date.now();
  const all = sortDecks([...S.decks.values()]);
  const sec = (title, list, empty, showOwner) => h('div', { class: 'deck-section' }, h('h3', { text: title }),
    list.length ? h('ul', { class: 'deck-list' }, ...list.map(d => deckRow(d, showOwner, now))) : h('p', { class: 'empty-line', text: empty }));
  const sections = [sec('My decks', all.filter(d => category(d) === 'mine'), 'You have no decks yet. Make one with New deck.', false)];
  if (S.isAdmin) {
    const others = all.filter(d => d.ownerId !== myUid());
    const byOwner = new Map();
    for (const d of others) { if (!byOwner.has(d.ownerId)) byOwner.set(d.ownerId, []); byOwner.get(d.ownerId).push(d); }
    const groups = [...byOwner.entries()].sort((a, b) => ownerLabel(a[1][0]).localeCompare(ownerLabel(b[1][0])));
    sections.push(h('div', { class: 'deck-section' }, h('h3', { text: "Everyone else's decks" }),
      groups.length ? h('div', null, ...groups.map(([, ds]) => h('div', { class: 'owner-group' },
        h('span', { class: 'owner-name', text: ownerLabel(ds[0]) }),
        h('ul', { class: 'deck-list' }, ...ds.map(d => deckRow(d, false, now))))))
        : h('p', { class: 'empty-line', text: 'Nobody else has made a deck yet.' })));
  } else {
    sections.push(sec('Shared by friends', all.filter(d => category(d) === 'shared'), 'When friends share one of their decks, it shows up here.', true));
  }
  put(root,
    h('div', { class: 'row', style: 'align-items:flex-start' },
      h('div', { style: 'flex:1 1 18rem;min-width:0' }, h('h1', { text: 'Decks' }),
        h('p', { class: 'lede', text: S.isAdmin ? 'Your decks, and every deck your friends have made.' : 'Your decks, and the ones friends share with you.' })),
      h('button', { type: 'button', class: 'btn primary', onclick: () => { S.dv.creating = true; renderDecks(true); const n = $('ndName'); if (n) n.focus(); } }, 'New deck')),
    S.dv.creating ? newDeckBox() : null,
    ...sections);
}
function newDeckBox() {
  const name = h('input', { type: 'text', id: 'ndName', maxlength: '80', placeholder: 'e.g. Poems we love', autocomplete: 'off' });
  let kind = 'facts';
  let allowTouched = false;
  const status = h('p', { class: 'status', role: 'status' });
  const edit = check('ndEdit', 'Friends can edit it too', false);
  const share = check('ndShare', 'Share with friends', true, (v) => { edit.hidden = !v; });
  const allowSel = allowSelect('ndAllow', DEFAULT_ALLOW.facts, () => { allowTouched = true; });
  const radio = (value, label, checked) => {
    const id = 'nd-kind-' + value;
    const r = h('input', { type: 'radio', name: 'nd-kind', id, value, checked });
    r.addEventListener('change', () => { kind = value; if (!allowTouched) allowSel.value = String(DEFAULT_ALLOW[kind]); });
    return h('label', { class: 'check', for: id }, r, h('span', { text: label }));
  };
  const close = () => { S.dv.creating = false; renderDecks(true); };
  const create = async () => {
    const n = name.value.trim();
    if (!n) { status.className = 'status err'; status.textContent = 'Give the deck a name.'; name.focus(); return; }
    status.className = 'status'; status.textContent = 'Creating…';
    try {
      const shared = $('ndShare').checked;
      const id = await createDeck({ name: n, kind, visibility: shared ? 'shared' : 'private', friendsCanEdit: shared && $('ndEdit').checked, allowPct: Number(allowSel.value) });
      S.dv.creating = false;
      S.add = { kind, deckId: id, chosen: true };
      toast(`Created ${n}. Add to it here.`);
      go('add');
    } catch (e) { status.className = 'status err'; status.textContent = dataError(e); }
  };
  name.addEventListener('keydown', (e) => { if (e.key === 'Enter') { e.preventDefault(); create(); } });
  return h('div', { class: 'panel-box' },
    h('h2', { text: 'New deck' }),
    field('Name', name),
    h('div', { class: 'field' }, h('span', { class: 'label', text: 'Holds' }),
      h('div', { class: 'radios' }, radio('facts', 'Facts (prompt and answer)', true), radio('poems', 'Poems (written out whole)', false))),
    h('div', { class: 'stack-sm' }, share, edit),
    h('div', { class: 'field' }, h('label', { class: 'label', for: 'ndAllow', text: 'Allowed mistakes (standard)' }), allowSel),
    h('div', { class: 'row' }, h('button', { type: 'button', class: 'btn primary', onclick: create }, 'Create deck'), h('button', { type: 'button', class: 'btn ghost', onclick: close }, 'Cancel')),
    status);
}
function deckSettings(d) {
  const ref = doc(db, 'decks', d.id);
  const shared = d.visibility === 'shared';
  return h('div', { class: 'settings' },
    check('dsShare', 'Share with friends', shared, (v) => save(updateDoc(ref, { visibility: v ? 'shared' : 'private', ...(v ? {} : { friendsCanEdit: false }), updatedAt: serverTimestamp() }),
      v ? 'Friends can now see and study this deck.' : 'This deck is private again.')),
    check('dsEdit', 'Friends can edit it too (add, change and delete items)', shared && d.friendsCanEdit, (v) => save(updateDoc(ref, { friendsCanEdit: v, updatedAt: serverTimestamp() }),
      v ? 'Friends can now edit this deck.' : 'Only you can edit this deck now.'), !shared),
    h('div', { class: 'row' }, h('label', { class: 'label', for: 'dsAllow', style: 'margin:0', text: 'Allowed mistakes' }),
      allowSelect('dsAllow', d.allowPct, (v) => save(updateDoc(ref, { allowPct: v, updatedAt: serverTimestamp() }), `Standard set to ${v}%.`))));
}
function renderDeckDetail(root) {
  const d = S.decks.get(S.dv.open);
  const dv = S.dv;
  const manage = canManage(d);
  const editItems = canEditItems(d);
  const poem = d.kind === 'poems';
  const noun = poem ? 'poem' : 'fact';
  const now = Date.now();
  const items = itemsOf(d);
  const st = deckStats(d, now);

  let actions;
  if (dv.renaming) {
    const inp = h('input', { type: 'text', id: 'renameInput', maxlength: '80', 'aria-label': 'Deck name', value: d.name });
    const done = () => { dv.renaming = false; renderDecks(true); };
    const saveName = async () => {
      const v = inp.value.trim();
      if (!v) { toast('Give the deck a name.'); return; }
      done();
      await save(updateDoc(doc(db, 'decks', d.id), { name: v.slice(0, 80), updatedAt: serverTimestamp() }));
    };
    inp.addEventListener('keydown', (e) => { if (e.key === 'Enter') saveName(); if (e.key === 'Escape') done(); });
    actions = h('div', { class: 'row', style: 'width:100%' }, h('div', { style: 'flex:1 1 12rem;min-width:0' }, inp),
      h('button', { type: 'button', class: 'btn primary', onclick: saveName }, 'Save name'), h('button', { type: 'button', class: 'btn ghost', onclick: done }, 'Cancel'));
    setTimeout(() => inp.focus(), 0);
  } else if (dv.confirmDeck) {
    actions = h('div', { class: 'confirm' },
      h('span', { text: `Delete ${d.name} and its ${plural(items.length, noun)}${d.visibility === 'shared' ? ' for everyone' : ''}?` }),
      h('button', { type: 'button', class: 'btn danger', onclick: async () => {
        dv.confirmDeck = false; dv.open = null;
        await save(deleteDoc(doc(db, 'decks', d.id)), `Deleted ${d.name}.`);
        renderDecks(true);
      } }, 'Delete deck'),
      h('button', { type: 'button', class: 'btn ghost', onclick: () => { dv.confirmDeck = false; renderDecks(true); } }, 'Keep it'));
  } else {
    actions = h('div', { class: 'stack-sm', style: 'justify-items:start;width:100%' },
      h('div', { class: 'row' },
        category(d) !== 'other' && items.length ? h('button', { type: 'button', class: 'btn primary', onclick: () => { S.study.kind = d.kind; S.study.sel[d.kind] = new Set([d.id]); savePrefs(); S.session = null; go('study'); } }, 'Study this deck') : null,
        editItems ? h('button', { type: 'button', class: 'btn ghost', onclick: () => { S.add = { kind: d.kind, deckId: d.id, chosen: true }; go('add'); } }, poem ? 'Add a poem' : 'Add facts') : null),
      manage ? deckSettings(d) : null,
      manage ? h('div', { class: 'row' },
        h('button', { type: 'button', class: 'linkbtn', onclick: () => { dv.renaming = true; renderDecks(true); } }, 'Rename'),
        h('button', { type: 'button', class: 'linkbtn warn', onclick: () => { dv.confirmDeck = true; renderDecks(true); } }, 'Delete deck')) : null);
  }

  const metaBits = [plural(st.total, noun)];
  if (category(d) !== 'other' && st.total) metaBits.push(`${st.due} due for you`, `${pct(st.masteredPct)} mastered`);
  if (!manage) metaBits.push(`${d.allowPct}% mistakes allowed`);
  const head = h('div', { class: 'deck-head' },
    h('div', { class: 'title' },
      h('h1', { text: d.name }),
      h('div', { class: 'meta' }, ...deckPills(d), h('span', { text: d.ownerId === myUid() ? 'yours' : 'by ' + ownerLabel(d) })),
      h('p', { class: 'help', text: metaBits.join(' · ') }),
      !editItems ? h('p', { class: 'help', text: 'You can study this deck, but only its owner can change it.' })
        : (!manage ? h('p', { class: 'help', text: `${ownerLabel(d)} lets friends add to and edit this deck.` }) : null)),
    actions);

  const q = norm(dv.q);
  let rows = items.map(([iid, it]) => ({ iid, it, pr: progOf(d.id, iid) }));
  if (q) rows = rows.filter(r => poem
    ? (norm(r.it.title).includes(q) || norm(r.it.author).includes(q) || norm(r.it.text).includes(q))
    : (norm(r.it.p).includes(q) || norm(r.it.a).includes(q)));
  rows.forEach(r => { r.w = weightOf(r.it, r.pr, now); });
  rows.sort((a, b) => b.w - a.w);
  const maxW = rows.length ? rows[0].w : 1;
  const shown = rows.slice(0, MAX_LIST);
  for (const id of [...dv.picked]) if (!d.items[id]) dv.picked.delete(id);

  const search = h('input', { type: 'search', id: 'deckSearch', placeholder: 'Search this deck', 'aria-label': 'Search this deck', autocomplete: 'off', value: dv.q });
  let tmr = 0;
  search.addEventListener('input', () => { clearTimeout(tmr); tmr = setTimeout(() => { dv.q = search.value; dv.editing = null; renderDecks(true); const s2 = $('deckSearch'); if (s2) { s2.focus(); s2.setSelectionRange(s2.value.length, s2.value.length); } }, 150); });
  const fallback = h('textarea', { readonly: true, hidden: true, 'aria-label': 'Deck as text', class: 'data' });
  const copyBtn = h('button', { type: 'button', class: 'btn ghost', onclick: () => {
    const text = poem
      ? items.map(([, it]) => `${it.title}${it.author ? ' — ' + it.author : ''}\n\n${it.text}`).join('\n\n---\n\n')
      : items.map(([, it]) => `${it.p} | ${String(it.a).replace(/\r?\n/g, ' ')}`).join('\n');
    copyText(text, fallback, `Copied ${plural(items.length, noun)}.`);
  } }, 'Copy');
  const selectBtn = editItems && items.length ? h('button', { type: 'button', class: 'btn ghost', 'aria-pressed': dv.selecting ? 'true' : 'false', onclick: () => { dv.selecting = !dv.selecting; dv.picked = new Set(); dv.editing = null; renderDecks(true); } }, dv.selecting ? 'Done' : 'Select') : null;

  put(root,
    h('div', null, h('button', { type: 'button', class: 'linkbtn quiet', onclick: () => { S.dv = freshDv(); renderDecks(true); } }, '← All decks')),
    head,
    items.length ? h('div', { class: 'tools', style: 'grid-template-columns:minmax(0,1fr) auto auto' }, search, selectBtn || h('span'), copyBtn) : null,
    fallback,
    h('p', { class: 'list-note', text: rows.length
      ? `${plural(rows.length, noun)}${q ? ' match' : ''}, most likely to come up for you first${rows.length > shown.length ? `. Showing the first ${MAX_LIST}; search to narrow.` : '.'}`
      : (q ? 'Nothing matches that search.' : `No ${noun}s in this deck yet.`) }),
    shown.length ? h('ul', { class: 'items' }, ...shown.map(r => itemRow(d, r, maxW, now, editItems))) : null,
    dv.selecting ? selectionBar(d, shown) : null);
}
function deleteItemsWithUndo(d, ids) {
  const backup = {};
  for (const id of ids) if (d.items[id]) backup[id] = d.items[id];
  const keys = Object.keys(backup);
  if (!keys.length) return;
  const noun = d.kind === 'poems' ? 'poem' : 'fact';
  const first = backup[keys[0]];
  const label = keys.length === 1 ? `Deleted “${d.kind === 'poems' ? first.title : first.p}”.` : `Deleted ${plural(keys.length, noun)}.`;
  save(removeItems(d.id, keys), label, { label: 'Undo', run: () => save(addItems(d.id, backup), 'Restored.') });
}
function selectionBar(d, shown) {
  const dv = S.dv;
  const n = dv.picked.size;
  const noun = d.kind === 'poems' ? 'poem' : 'fact';
  const targets = sortDecks([...S.decks.values()].filter(x => x.id !== d.id && x.kind === d.kind && canEditItems(x)));
  const move = h('select', { id: 'moveTo', 'aria-label': 'Move to deck' },
    h('option', { value: '', text: 'Move to…' }), ...targets.map(t => h('option', { value: t.id, text: t.name + (t.ownerId !== myUid() ? ` (${ownerLabel(t)})` : '') })));
  move.disabled = !n || !targets.length;
  move.addEventListener('change', async () => {
    const target = S.decks.get(move.value); if (!target) return;
    const ids = [...dv.picked].filter(id => d.items[id]);
    const moving = {}; for (const id of ids) moving[id] = d.items[id];
    if (bytes(Object.assign({}, target.items, moving)) > MAX_DECK_BYTES) { toast(`${target.name} doesn't have room for these.`); move.value = ''; return; }
    const batch = writeBatch(db);
    batch.update(doc(db, 'decks', target.id), itemsPatch(moving));
    const del = { updatedAt: serverTimestamp() }; for (const id of ids) del['items.' + id] = deleteField();
    batch.update(doc(db, 'decks', d.id), del);
    const ok = await save(batch.commit(), `Moved ${plural(ids.length, noun)} to ${target.name}.`);
    if (ok) {
      const p = {};
      for (const id of ids) { const pr = progOf(d.id, id); if (pr) { p[progKey(target.id, id)] = pr; p[progKey(d.id, id)] = deleteField(); } }
      if (Object.keys(p).length) save(setDoc(doc(db, 'progress', myUid()), { p, updatedAt: serverTimestamp() }, { merge: true }));
    }
    dv.picked = new Set(); renderDecks(true);
  });
  const allIds = shown.map(r => r.iid);
  const allOn = allIds.length > 0 && allIds.every(id => dv.picked.has(id));
  return h('div', { class: 'selbar', role: 'region', 'aria-label': 'Selected items' },
    h('span', { text: n ? `${n} selected` : `Pick ${noun}s below` }),
    h('button', { type: 'button', class: 'linkbtn', onclick: () => { dv.picked = allOn ? new Set() : new Set(allIds); renderDecks(true); } }, allOn ? 'Clear' : 'Select all'),
    h('span', { class: 'spacer' }),
    move,
    h('button', { type: 'button', class: 'btn danger', disabled: !n, onclick: () => { const ids = [...dv.picked]; dv.picked = new Set(); deleteItemsWithUndo(d, ids); } }, 'Delete'));
}
function itemRow(d, r, maxW, now, editItems) {
  const dv = S.dv;
  const poem = d.kind === 'poems';
  if (dv.editing === r.iid) return itemEditRow(d, r);
  const n = r.pr ? Number(r.pr.n) || 0 : 0;
  const open = dv.expanded.has(r.iid);
  const status = category(d) !== 'other' ? statusOf(r.pr, now) : null;
  const label = poem ? r.it.title : r.it.p;
  const side = h('div', { class: 'item-side' },
    h('div', { class: 'row', style: 'justify-content:flex-end;gap:.4rem' },
      status ? h('span', { class: 'pill ' + status[0], text: status[1] }) : null,
      r.pr && Number(r.pr.t) ? h('span', { class: 'mono', text: (n ? `right ${n}× · ` : '') + ago(Number(r.pr.t), now) }) : null),
    h('span', { class: 'bar', title: 'How likely it is to come up for you', 'aria-hidden': 'true' }, h('i', { style: `width:${Math.max(4, Math.round(r.w / maxW * 100))}%` })),
    !dv.selecting ? h('div', { class: 'row', style: 'justify-content:flex-end;gap:.85rem' },
      poem ? h('button', { type: 'button', class: 'linkbtn', 'aria-expanded': open ? 'true' : 'false', onclick: () => { if (open) dv.expanded.delete(r.iid); else dv.expanded.add(r.iid); renderDecks(true); } }, open ? 'Hide' : 'Read') : null,
      editItems ? h('button', { type: 'button', class: 'linkbtn', onclick: () => { dv.editing = r.iid; renderDecks(true); const f = $('edit1'); if (f) f.focus(); } }, 'Edit') : null,
      editItems ? h('button', { type: 'button', class: 'linkbtn warn', 'aria-label': `Delete ${label}`, onclick: () => deleteItemsWithUndo(d, [r.iid]) }, 'Delete') : null) : null);
  const main = poem
    ? h('div', { style: 'min-width:0' }, h('p', { class: 'item-p', text: r.it.title }),
        h('p', { class: 'item-sub', text: [r.it.author ? 'by ' + r.it.author : '', plural(poemLines(r.it.text), 'line')].filter(Boolean).join(' · ') }),
        !open ? h('p', { class: 'item-a hand', text: poemFirstLine(r.it.text) + ' …' }) : null)
    : h('div', { style: 'min-width:0' }, h('p', { class: 'item-p', text: r.it.p }), h('p', { class: 'item-a hand', text: r.it.a }));
  const pick = dv.selecting ? h('input', { type: 'checkbox', class: 'pick', checked: dv.picked.has(r.iid), 'aria-label': `Select ${label}`, 'data-key': 'pick-' + r.iid,
    onchange: (e) => { if (e.target.checked) dv.picked.add(r.iid); else dv.picked.delete(r.iid); const root = $('view-decks'); withFocus(root, () => renderDecks(true)); } }) : null;
  return h('li', { class: 'item' + (dv.selecting ? ' sel-mode' : '') }, pick, main, side, poem && open ? h('pre', { class: 'poem-full', text: r.it.text }) : null);
}
function itemEditRow(d, r) {
  const dv = S.dv;
  const poem = d.kind === 'poems';
  const close = () => { dv.editing = null; renderDecks(true); };
  let f1, f2, f3;
  if (poem) {
    f1 = h('input', { type: 'text', id: 'edit1', maxlength: '200', value: r.it.title });
    f2 = h('input', { type: 'text', id: 'edit2', maxlength: '200', value: r.it.author || '' });
    f3 = h('textarea', { id: 'edit3', class: 'poem-input', maxlength: String(MAX_POEM) }); f3.value = r.it.text;
  } else {
    f1 = h('textarea', { id: 'edit1', rows: '2', maxlength: String(MAX_FIELD) }); f1.value = r.it.p;
    f2 = h('textarea', { id: 'edit2', rows: '2', maxlength: String(MAX_FIELD) }); f2.value = r.it.a;
  }
  const doSave = async () => {
    let next;
    if (poem) {
      const title = f1.value.trim(), text = cleanPoem(f3.value);
      if (!title || !text) { toast('A poem needs a title and its text.'); return; }
      next = { title, author: f2.value.trim(), text, c: Number(r.it.c) || Date.now() };
    } else {
      const p = f1.value.trim(), a = f2.value.trim();
      if (!p || !a) { toast('A fact needs both a prompt and an answer.'); return; }
      next = { p, a, c: Number(r.it.c) || Date.now() };
    }
    close();
    await save(addItems(d.id, { [r.iid]: next }), 'Saved.');
  };
  const fields = poem
    ? [h('div', { class: 'grid-2' }, field('Title', f1), field('Poet', f2)), field('Poem', f3)]
    : [field('Prompt', f1), field('Answer', f2)];
  return h('li', { class: 'item' }, h('div', { class: 'item-edit' }, ...fields,
    h('div', { class: 'row' },
      h('button', { type: 'button', class: 'btn primary', onclick: doSave }, 'Save'),
      h('button', { type: 'button', class: 'btn ghost', onclick: close }, 'Cancel'),
      h('span', { class: 'spacer' }),
      h('button', { type: 'button', class: 'linkbtn warn', onclick: () => { close(); deleteItemsWithUndo(d, [r.iid]); } }, poem ? 'Delete poem' : 'Delete fact'))));
}

// ---------------------------------------------------------------- add
let lastParse = { rows: [], skipped: [] };
function writableDecks(kind) {
  return sortDecks([...S.decks.values()].filter(d => d.kind === kind && (d.ownerId === myUid() || (category(d) === 'shared' && d.friendsCanEdit))));
}
function mountAdd() {
  mounted.add = true;
  const factsBox = h('div', { id: 'addFactsBox', class: 'stack-sm' },
    h('label', { class: 'label', for: 'pasteBox', text: 'Your facts' }),
    h('textarea', { id: 'pasteBox', class: 'data', spellcheck: 'false', placeholder: 'Capital of Australia | Canberra\nNumber of bones in the adult human body | 206\nChemistry | Chemical symbol for potassium | K' }),
    h('p', { class: 'help' }, 'One fact per line, prompt first: ', h('code', { text: 'prompt | answer' }), '. To send lines to other decks in the same paste, start the line with the deck name: ', h('code', { text: 'deck | prompt | answer' }), '. Tab-separated columns from a spreadsheet work too.'),
    h('div', { class: 'preview', id: 'preview', hidden: true }));
  const poemBox = h('div', { id: 'addPoemBox', class: 'stack-sm', hidden: true },
    h('div', { class: 'grid-2' },
      field('Title', h('input', { type: 'text', id: 'poemTitle', maxlength: '200', autocomplete: 'off' })),
      field('Poet (optional)', h('input', { type: 'text', id: 'poemAuthor', maxlength: '200', autocomplete: 'off' }))),
    field('The poem', h('textarea', { id: 'poemText', class: 'poem-input', maxlength: String(MAX_POEM), placeholder: 'Paste or type the poem here. Line breaks and stanza gaps are kept.' })),
    h('p', { class: 'help', id: 'poemInfo' }));
  const newDeck = h('div', { id: 'addNewDeck', class: 'panel-box', hidden: true },
    field('New deck name', h('input', { type: 'text', id: 'newDeckName', maxlength: '80', autocomplete: 'off', placeholder: 'e.g. Biology terms' })),
    h('div', { class: 'stack-sm' },
      check('adShare', 'Share with friends', true, () => updateAdd()),
      check('adEdit', 'Friends can edit it too', false)),
    h('p', { class: 'help', text: 'You can change these, and the allowed mistakes, later on the deck\'s page.' }));
  put($('view-add'),
    h('div', { class: 'row', style: 'align-items:flex-start' },
      h('div', { style: 'flex:1 1 18rem;min-width:0' }, h('h1', { text: 'Add' }), h('p', { class: 'lede', id: 'addLede' })),
      seg('addKind', [['facts', 'Facts'], ['poems', 'Poems']], S.add.kind, (k) => { S.add.kind = k; S.add.chosen = false; S.add.deckId = null; $('addStatus').textContent = ''; renderAdd(); })),
    h('div', { class: 'field' }, h('label', { class: 'label', for: 'addDeck', text: 'Add to' }), h('select', { id: 'addDeck' })),
    newDeck, factsBox, poemBox,
    h('div', { class: 'row' }, h('button', { type: 'button', class: 'btn primary big', id: 'addBtn', disabled: true }, 'Add'), h('p', { class: 'status', id: 'addStatus', role: 'status' })));
  $('addDeck').addEventListener('change', (e) => { S.add.deckId = e.target.value; S.add.chosen = true; renderAdd(); if (S.add.deckId === '__new') $('newDeckName').focus(); });
  let t = 0;
  const later = () => { clearTimeout(t); t = setTimeout(updateAdd, 120); $('addStatus').textContent = ''; };
  for (const id of ['pasteBox', 'newDeckName', 'poemTitle', 'poemAuthor', 'poemText']) $(id).addEventListener('input', later);
  $('addBtn').addEventListener('click', () => (S.add.kind === 'poems' ? addPoem() : addFacts()));
}
function renderAdd() {
  if (!mounted.add) mountAdd();
  const kind = S.add.kind;
  setSeg('addKind', kind);
  $('addLede').textContent = kind === 'poems' ? 'Add one poem at a time. You\'ll practice writing it out whole.' : 'Paste as many as you like. Each line becomes one fact.';
  const decks = writableDecks(kind);
  let val = S.add.deckId;
  if (!S.add.chosen || (val !== '__new' && !decks.some(d => d.id === val))) {
    const mine = decks.find(d => d.ownerId === myUid());
    val = (mine || decks[0] || { id: '__new' }).id;
  }
  S.add.deckId = val;
  const sel = $('addDeck');
  const mine = decks.filter(d => d.ownerId === myUid());
  const theirs = decks.filter(d => d.ownerId !== myUid());
  put(sel,
    mine.length ? h('optgroup', { label: 'My decks' }, ...mine.map(d => h('option', { value: d.id, text: `${d.name} (${itemsOf(d).length})` }))) : null,
    theirs.length ? h('optgroup', { label: "Friends' decks you can edit" }, ...theirs.map(d => h('option', { value: d.id, text: `${d.name} · ${ownerLabel(d)} (${itemsOf(d).length})` }))) : null,
    h('option', { value: '__new', text: 'New deck…' }));
  sel.value = val;
  $('addNewDeck').hidden = val !== '__new';
  $('addFactsBox').hidden = kind !== 'facts';
  $('addPoemBox').hidden = kind !== 'poems';
  updateAdd();
}
function newDeckChoice() {
  const shared = $('adShare').checked;
  return { name: $('newDeckName').value.trim(), visibility: shared ? 'shared' : 'private', friendsCanEdit: shared && $('adEdit').checked };
}
function targetName() {
  if (S.add.deckId === '__new') return $('newDeckName').value.trim();
  const d = S.decks.get(S.add.deckId);
  return d ? d.name : '';
}
function parseFacts(text) {
  const target = targetName();
  const writable = writableDecks('facts');
  const byName = (n) => writable.find(d => norm(d.name) === norm(n)) || null;
  const rows = [], skipped = [];
  const seen = new Map();
  text.split(/\r?\n/).forEach((raw, idx) => {
    const line = raw.trim();
    if (!line) return;
    let parts = (line.includes('\t') ? line.split('\t') : line.split('|')).map(p => p.trim());
    while (parts.length > 2 && parts[parts.length - 1] === '') parts.pop();
    let deck, p, a, routed = false;
    if (parts.length === 2) { deck = target; [p, a] = parts; }
    else if (parts.length >= 3) { deck = parts[0]; p = parts[1]; a = parts.slice(2).join(' | '); routed = true; }
    else { skipped.push({ n: idx + 1, why: 'no | between prompt and answer' }); return; }
    if (!p) { skipped.push({ n: idx + 1, why: 'empty prompt' }); return; }
    if (!a) { skipped.push({ n: idx + 1, why: 'empty answer' }); return; }
    if (!deck) { skipped.push({ n: idx + 1, why: 'name the new deck above, or start the line with a deck' }); return; }
    if (p.length > MAX_FIELD || a.length > MAX_FIELD) { skipped.push({ n: idx + 1, why: 'longer than 2,000 characters' }); return; }
    deck = deck.slice(0, 80);
    const existing = (!routed && S.add.deckId !== '__new') ? (S.decks.get(S.add.deckId) || null) : byName(deck);
    const dk = existing ? 'id:' + existing.id : 'new:' + norm(deck);
    const pk = norm(p);
    if (existing && itemsOf(existing).some(([, it]) => norm(it.p) === pk)) { skipped.push({ n: idx + 1, why: `already in ${existing.name}` }); return; }
    if (!seen.has(dk)) seen.set(dk, new Set());
    if (seen.get(dk).has(pk)) { skipped.push({ n: idx + 1, why: 'repeated in this paste' }); return; }
    seen.get(dk).add(pk);
    rows.push({ key: dk, deck: existing ? existing.name : deck, deckId: existing ? existing.id : null, p, a, isNew: !existing, routed });
  });
  return { rows, skipped };
}
function updateAdd() {
  const kind = S.add.kind;
  const isNew = S.add.deckId === '__new';
  $('adEdit').closest('label').hidden = !$('adShare').checked;
  const btn = $('addBtn');
  if (kind === 'poems') {
    const title = $('poemTitle').value.trim();
    const text = cleanPoem($('poemText').value);
    $('poemInfo').textContent = text ? `${plural(poemLines(text), 'line')}${title ? '' : ' · add a title'}` : 'Tip: keep a blank line between stanzas.';
    btn.disabled = !title || !text || (isNew && !$('newDeckName').value.trim());
    btn.textContent = 'Add poem';
    return;
  }
  const pv = $('preview');
  const text = $('pasteBox').value;
  if (!text.trim()) { pv.hidden = true; btn.disabled = true; btn.textContent = 'Add facts'; lastParse = { rows: [], skipped: [] }; return; }
  const r = parseFacts(text);
  lastParse = r;
  const touched = new Map();
  for (const row of r.rows) if (!touched.has(row.key)) touched.set(row.key, row);
  const newOnes = [...touched.values()].filter(x => x.isNew);
  const kids = [h('div', { class: 'preview-sum' },
    h('span', null, h('b', { text: r.rows.length.toLocaleString() }), ' ready to add'),
    touched.size > 1 ? h('span', null, 'across ', h('b', { text: String(touched.size) }), ' decks') : null,
    newOnes.length ? h('span', { class: 'pill new', text: newOnes.length === 1 ? `new deck: ${newOnes[0].deck}` : `${newOnes.length} new decks` }) : null,
    r.skipped.length ? h('span', { class: 'pill skip', text: `${r.skipped.length} skipped` }) : null)];
  if (r.rows.length) {
    const showDeck = touched.size > 1;
    const shownRows = r.rows.slice(0, 6);
    kids.push(h('div', { class: 'tablewrap' }, h('table', { class: 'pv' },
      h('thead', null, h('tr', null, showDeck ? h('th', { text: 'Deck' }) : null, h('th', { text: 'Prompt' }), h('th', { text: 'Answer' }))),
      h('tbody', null, ...shownRows.map(row => h('tr', null, showDeck ? h('td', { text: row.deck }) : null, h('td', { text: row.p }), h('td', { text: row.a }))),
        r.rows.length > shownRows.length ? h('tr', null, h('td', { colspan: showDeck ? '3' : '2', text: `…and ${(r.rows.length - shownRows.length).toLocaleString()} more` })) : null))));
  }
  if (r.skipped.length) kids.push(h('ul', { class: 'skipped' }, ...r.skipped.slice(0, 8).map(s => h('li', { text: `Line ${s.n}: ${s.why}` })), r.skipped.length > 8 ? h('li', { text: `…and ${r.skipped.length - 8} more` }) : null));
  if (newOnes.some(x => x.routed)) kids.push(h('p', { class: 'help', text: 'Decks named at the start of a line that you don\'t have yet are created as private decks of your own.' }));
  put(pv, ...kids);
  pv.hidden = false;
  btn.disabled = !r.rows.length;
  btn.textContent = r.rows.length ? `Add ${plural(r.rows.length, 'fact')}` : 'Add facts';
}
async function addFacts() {
  const { rows } = lastParse;
  if (!rows.length) return;
  const status = $('addStatus'); const btn = $('addBtn');
  btn.disabled = true; status.className = 'status'; status.textContent = 'Saving…';
  const groups = new Map();
  for (const r of rows) { if (!groups.has(r.key)) groups.set(r.key, { r, rows: [] }); groups.get(r.key).rows.push(r); }
  const now = Date.now();
  const choice = newDeckChoice();
  const plans = [];
  for (const g of groups.values()) {
    const items = {};
    g.rows.forEach((r, i) => { items[rid('i') + i.toString(36)] = { p: r.p, a: r.a, c: now }; });
    if (g.r.deckId) {
      const d = S.decks.get(g.r.deckId);
      if (bytes(Object.assign({}, d.items, items)) > MAX_DECK_BYTES) { status.className = 'status err'; status.textContent = `${d.name} would go over its size limit (several thousand facts). Put these in a new deck.`; btn.disabled = false; return; }
      plans.push({ kind: 'add', id: d.id, items, name: d.name, n: g.rows.length });
    } else {
      if (bytes(items) > MAX_DECK_BYTES) { status.className = 'status err'; status.textContent = 'That is more than one deck holds. Split it across two decks.'; btn.disabled = false; return; }
      const fromBox = !g.r.routed;
      plans.push({ kind: 'create', name: g.r.deck, visibility: fromBox ? choice.visibility : 'private', friendsCanEdit: fromBox && choice.friendsCanEdit, items, n: g.rows.length, fromBox });
    }
  }
  try {
    let createdFromBox = null;
    for (const p of plans) {
      if (p.kind === 'add') await addItems(p.id, p.items);
      else { const id = await createDeck({ name: p.name, kind: 'facts', visibility: p.visibility, friendsCanEdit: p.friendsCanEdit, items: p.items }); if (p.fromBox) createdFromBox = id; }
    }
    const total = plans.reduce((a, p) => a + p.n, 0);
    status.className = 'status ok';
    status.textContent = plans.length === 1 ? `Added ${plural(total, 'fact')} to ${plans[0].name}.` : `Added ${plural(total, 'fact')} across ${plans.length} decks.`;
    $('pasteBox').value = '';
    if (createdFromBox) { S.add.deckId = createdFromBox; S.add.chosen = true; $('newDeckName').value = ''; }
    renderAdd();
  } catch (e) {
    console.error(e);
    status.className = 'status err'; status.textContent = dataError(e); btn.disabled = false;
  }
}
async function addPoem() {
  const status = $('addStatus'); const btn = $('addBtn');
  const title = $('poemTitle').value.trim();
  const author = $('poemAuthor').value.trim();
  const text = cleanPoem($('poemText').value);
  if (!title || !text) { status.className = 'status err'; status.textContent = 'A poem needs a title and its text.'; return; }
  const item = { title, author, text, c: Date.now() };
  const id = rid('i');
  btn.disabled = true; status.className = 'status'; status.textContent = 'Saving…';
  try {
    let deckName;
    if (S.add.deckId === '__new') {
      const ch = newDeckChoice();
      if (!ch.name) { status.className = 'status err'; status.textContent = 'Name the new deck.'; btn.disabled = false; return; }
      const newId = await createDeck({ name: ch.name, kind: 'poems', visibility: ch.visibility, friendsCanEdit: ch.friendsCanEdit, items: { [id]: item } });
      S.add.deckId = newId; S.add.chosen = true; deckName = ch.name; $('newDeckName').value = '';
    } else {
      const d = S.decks.get(S.add.deckId);
      if (!d) throw new Error('missing deck');
      if (itemsOf(d).some(([, it]) => norm(it.title) === norm(title))) { status.className = 'status err'; status.textContent = `${d.name} already has a poem called ${title}.`; btn.disabled = false; return; }
      if (bytes(Object.assign({}, d.items, { [id]: item })) > MAX_DECK_BYTES) { status.className = 'status err'; status.textContent = `${d.name} is full. Start a new poem deck.`; btn.disabled = false; return; }
      await addItems(d.id, { [id]: item });
      deckName = d.name;
    }
    status.className = 'status ok'; status.textContent = `Added “${title}” to ${deckName}.`;
    for (const f of ['poemTitle', 'poemAuthor', 'poemText']) $(f).value = '';
    renderAdd();
    $('poemTitle').focus();
  } catch (e) {
    console.error(e);
    status.className = 'status err'; status.textContent = dataError(e); btn.disabled = false;
  }
}

// ---------------------------------------------------------------- people (admin)
function randomPassword() {
  const a = new Uint32Array(4); crypto.getRandomValues(a);
  return Array.from(a, x => x.toString(36)).join('') + 'A1!';
}
function mountPeople() {
  mounted.people = true;
  const name = h('input', { type: 'text', id: 'npName', maxlength: '60', autocomplete: 'off' });
  const email = h('input', { type: 'email', id: 'npEmail', autocomplete: 'off' });
  const pwMode = (value, label, checked) => {
    const id = 'npPw-' + value;
    const r = h('input', { type: 'radio', name: 'npPw', id, value, checked });
    r.addEventListener('change', () => { $('npTempWrap').hidden = value !== 'temp'; });
    return h('label', { class: 'check', for: id }, r, h('span', { text: label }));
  };
  const temp = h('input', { type: 'text', id: 'npTemp', autocomplete: 'off', placeholder: 'At least 8 characters' });
  const status = h('p', { class: 'status', role: 'status', id: 'npStatus' });
  const btn = h('button', { type: 'submit', class: 'btn primary' }, 'Create account');
  const create = async () => {
    const n = name.value.trim(), e = email.value.trim();
    const mode = document.querySelector('input[name="npPw"]:checked').value;
    if (!n || !e) { status.className = 'status err'; status.textContent = 'Add their name and email.'; return; }
    if (mode === 'temp' && temp.value.length < 8) { status.className = 'status err'; status.textContent = 'Make the temporary password at least 8 characters.'; return; }
    btn.disabled = true; status.className = 'status'; status.textContent = 'Creating…';
    try {
      // A second Firebase app makes the account without signing you out.
      const second = getApps().find(a => a.name === 'creator') || initializeApp(firebaseConfig, 'creator');
      const sAuth = getAuth(second);
      await setPersistence(sAuth, inMemoryPersistence);
      const cred = await createUserWithEmailAndPassword(sAuth, e, mode === 'temp' ? temp.value : randomPassword());
      const uid = cred.user.uid;
      await signOut(sAuth);
      await setDoc(doc(db, 'users', uid), { name: n, email: e, active: true, createdAt: serverTimestamp() });
      if (mode === 'link') await sendPasswordResetEmail(auth, e);
      status.className = 'status ok';
      status.textContent = mode === 'link'
        ? `Account made. ${n} will get an email with a link to set their password (it may land in spam).`
        : `Account made. Give ${n} their email and the temporary password; they can change it from their account page.`;
      name.value = ''; email.value = ''; temp.value = '';
    } catch (err) {
      console.error(err);
      const c = (err && err.code) || '';
      status.className = 'status err';
      status.textContent = c.includes('email-already-in-use')
        ? 'That email already has a sign-in. Ask them to sign in (with "Forgot your password?" if needed) and tap Request access. They\'ll show up here to approve.'
        : (c.startsWith('auth/') ? authError(err) : dataError(err));
    }
    btn.disabled = false;
  };
  put($('view-people'),
    h('div', null, h('h1', { text: 'People' }), h('p', { class: 'lede', text: 'Make accounts for your friends. Everyone can make their own decks and choose who sees and edits them.' })),
    h('form', { class: 'panel-box', novalidate: true, onsubmit: (ev) => { ev.preventDefault(); create(); } },
      h('h2', { text: 'Add a person' }),
      h('div', { class: 'grid-2' }, field('Name', name), field('Email', email)),
      h('div', { class: 'field' }, h('span', { class: 'label', text: 'Password' }),
        h('div', { class: 'radios' }, pwMode('link', 'Email them a link to set their own', true), pwMode('temp', 'I\'ll set a temporary one', false))),
      h('div', { id: 'npTempWrap', hidden: true }, field('Temporary password', temp)),
      h('div', { class: 'row' }, btn), status),
    h('div', { id: 'requestsBox' }),
    h('div', { class: 'deck-section' }, h('h3', { text: 'Accounts' }), h('ul', { class: 'people', id: 'peopleList' })));
}
function renderPeople(force) {
  if (!S.isAdmin) return;
  if (!mounted.people) mountPeople();
  const reqs = [...S.requests.entries()];
  put($('requestsBox'), reqs.length ? h('div', { class: 'deck-section' }, h('h3', { text: 'Waiting for you to approve' }),
    h('ul', { class: 'people' }, ...reqs.map(([uid, r]) => h('li', { class: 'person' },
      h('div', { style: 'min-width:0' }, h('div', { class: 'pn', text: String(r.name || 'Someone') }), h('div', { class: 'pe', text: String(r.email || '') })),
      h('div', { class: 'row' },
        h('button', { type: 'button', class: 'btn primary', onclick: async () => {
          const ok = await save(setDoc(doc(db, 'users', uid), { name: String(r.name || 'Friend').slice(0, 60), email: String(r.email || ''), active: true, createdAt: serverTimestamp() }), `${r.name || 'They'} can now sign in and study.`);
          if (ok) save(deleteDoc(doc(db, 'requests', uid)));
        } }, 'Approve'),
        h('button', { type: 'button', class: 'btn ghost', onclick: () => save(deleteDoc(doc(db, 'requests', uid)), 'Request dismissed.') }, 'Dismiss')))))) : null);
  if (S.pp.renaming && !force) return;   // keep the rename box while someone types
  const list = $('peopleList');
  const deckCounts = new Map();
  for (const d of S.decks.values()) {
    const c = deckCounts.get(d.ownerId) || { all: 0, shared: 0 };
    c.all++; if (d.visibility === 'shared') c.shared++;
    deckCounts.set(d.ownerId, c);
  }
  const people = [...S.people.entries()].sort((a, b) => {
    if (a[0] === S.adminUid) return -1; if (b[0] === S.adminUid) return 1;
    return String(a[1].name).localeCompare(String(b[1].name));
  });
  withFocus(list, () => put(list, ...people.map(([uid, p]) => personRow(uid, p, deckCounts.get(uid)))));
}
function personRow(uid, p, counts) {
  const isAdminRow = uid === S.adminUid;
  const c = counts || { all: 0, shared: 0 };
  const deckLine = `${plural(c.all, 'deck')}${c.shared ? `, ${c.shared} shared` : ''}`;
  if (S.pp.renaming === uid) {
    const inp = h('input', { type: 'text', id: 'ppRename', maxlength: '60', value: String(p.name || ''), 'aria-label': 'Name' });
    const done = () => { S.pp.renaming = null; renderPeople(true); };
    const go2 = async () => {
      const v = inp.value.trim(); if (!v) return;
      done();
      await save(updateDoc(doc(db, 'users', uid), { name: v.slice(0, 60) }), 'Name changed.');
      if (isAdminRow) save(updateDoc(doc(db, 'meta', 'admin'), { name: v.slice(0, 60) }));
    };
    inp.addEventListener('keydown', (e) => { if (e.key === 'Enter') go2(); if (e.key === 'Escape') done(); });
    setTimeout(() => inp.focus(), 0);
    return h('li', { class: 'person' }, h('div', { class: 'row', style: 'grid-column:1/-1' },
      h('div', { style: 'flex:1 1 12rem;min-width:0' }, inp),
      h('button', { type: 'button', class: 'btn primary', onclick: go2 }, 'Save'),
      h('button', { type: 'button', class: 'btn ghost', onclick: done }, 'Cancel')));
  }
  return h('li', { class: 'person' },
    h('div', { style: 'min-width:0' },
      h('div', { class: 'pn' }, h('span', { text: String(p.name || 'Unnamed') }),
        isAdminRow ? h('span', { class: 'pill admin', text: 'Admin' }) : null,
        !isAdminRow && p.active !== true ? h('span', { class: 'pill off', text: 'Turned off' }) : null),
      h('div', { class: 'pe', text: String(p.email || '') }),
      h('div', { class: 'pd', text: deckLine })),
    h('div', { class: 'row', style: 'justify-content:flex-end' },
      h('button', { type: 'button', class: 'linkbtn', onclick: () => { S.pp.renaming = uid; renderPeople(true); } }, 'Rename'),
      p.email ? h('button', { type: 'button', class: 'linkbtn', onclick: async () => {
        try { await sendPasswordResetEmail(auth, p.email); toast(`Sent a password reset link to ${p.email}.`); } catch (e) { toast(authError(e)); }
      } }, 'Send password reset') : null),
    !isAdminRow ? h('div', { class: 'pc' },
      check('act-' + uid, 'Account on', p.active === true,
        (v) => save(updateDoc(doc(db, 'users', uid), { active: v }), v ? `${p.name} can sign in again.` : `${p.name}'s account is turned off. Their decks are kept.`))) : null);
}

// ---------------------------------------------------------------- theme picker (account page)
function themeSwatch(id, name, finish, spec, note) {
  const t = deriveTheme(spec);
  const on = (S.theme && S.theme.id) === id;
  return h('button', { type: 'button', class: 'theme-swatch', 'aria-pressed': on ? 'true' : 'false', title: note || name, 'data-key': 'th-' + id,
    onclick: () => { if (id === 'custom') { openCustomEditor(); return; } closeCustomEditor(false); saveTheme({ id }); renderThemePicker(); } },
    h('span', { class: 'ts-prev', 'aria-hidden': 'true', style: `background:${t['--paper']}` },
      h('span', { class: 'ts-card', style: `background:${t['--card']};box-shadow:0 0 0 1px ${t['--line']}` },
        h('i', { class: 'ts-margin', style: `background:${t['--margin']}` }),
        h('i', { class: 'ts-line', style: `background:${t['--ink']}` }),
        h('i', { class: 'ts-line short', style: `background:${t['--pen']}` })),
      h('span', { class: 'ts-btn', style: `background:${t['--accent']}` }),
      finish ? h('span', { class: 'ts-finish', style: `background:${finish}` }) : null),
    h('span', { class: 'ts-name', text: name }));
}
function renderThemePicker() {
  const box = $('themePicker'); if (!box) return;
  const custom = (S.themeSaved && S.themeSaved.id === 'custom' && S.themeSaved.custom) || (S.theme.id === 'custom' && S.theme.custom) || suggestColors('#EEF2F7');
  withFocus(box, () => put(box,
    h('div', { class: 'theme-group' }, h('h3', { text: 'Classic & your own' }),
      h('div', { class: 'theme-grid' },
        themeSwatch('classic', 'Classic', null, CLASSIC_PREVIEW, 'Follows your device\'s light or dark setting'),
        themeSwatch('custom', 'Custom', null, custom, 'Pick your own colors'))),
    ...THEME_GROUPS.map(([group, list]) => h('div', { class: 'theme-group' }, h('h3', { text: group }),
      h('div', { class: 'theme-grid' }, ...list.map(([id, name, finish, spec, note]) => themeSwatch(id, name, finish, spec, note)))))));
}
let customDraft = null;
function openCustomEditor() {
  const ed = $('customEditor'); if (!ed) return;
  const start = (S.theme.id === 'custom' && S.theme.custom) || (S.themeSaved && S.themeSaved.custom) || suggestColors(deriveTheme(themeSpec(S.theme) || CLASSIC_PREVIEW)['--paper']);
  customDraft = { bg: start.bg, accent: start.accent, pen: start.pen || start.accent, margin: start.margin || '#D8524A' };
  const note = h('p', { class: 'help', id: 'customNote' });
  const picker = (key, label, help) => {
    const id = 'cu-' + key;
    const inp = h('input', { type: 'color', id, value: customDraft[key] });
    inp.addEventListener('input', () => { customDraft[key] = inp.value.toUpperCase(); previewCustom(); });
    return h('label', { class: 'color-field', for: id }, inp, h('span', null, h('b', { text: label }), h('small', { text: help })));
  };
  const fields = h('div', { class: 'color-grid' },
    picker('bg', 'Background', 'The page itself'),
    picker('accent', 'Accent', 'Buttons, links, highlights'),
    picker('pen', 'Answer ink', 'How answers are written'),
    picker('margin', 'Margin line', 'The red line on each card'));
  put(ed,
    h('h3', { text: 'Custom theme' }),
    h('p', { class: 'help', text: 'Changes show on the whole page as you pick. Light or dark is chosen from your background.' }),
    fields,
    note,
    h('div', { class: 'row' },
      h('button', { type: 'button', class: 'btn ghost', onclick: () => {
        const s2 = suggestColors(customDraft.bg);
        Object.assign(customDraft, s2);
        for (const k of ['accent', 'pen', 'margin']) $('cu-' + k).value = customDraft[k];
        previewCustom();
      } }, 'Match colors to my background'),
      h('span', { class: 'spacer' }),
      h('button', { type: 'button', class: 'btn ghost', onclick: () => closeCustomEditor(true) }, 'Cancel'),
      h('button', { type: 'button', class: 'btn primary', onclick: async () => { const th = { id: 'custom', custom: { ...customDraft } }; closeCustomEditor(false); await saveTheme(th); renderThemePicker(); } }, 'Save theme')));
  ed.hidden = false;
  previewCustom();
  ed.scrollIntoView({ block: 'nearest' });
}
function previewCustom() {
  if (!customDraft) return;
  S.themePreview = true;
  applyTheme({ id: 'custom', custom: { ...customDraft } });
  const t = deriveTheme(customDraft);
  const changed = [];
  if (t['--accent'] !== customDraft.accent.toUpperCase()) changed.push('accent');
  if (t['--pen'] !== customDraft.pen.toUpperCase()) changed.push('answer ink');
  if (t['--margin'] !== customDraft.margin.toUpperCase()) changed.push('margin line');
  const n = $('customNote');
  if (n) n.textContent = changed.length ? `Your ${changed.join(' and ')} ${changed.length > 1 ? 'were' : 'was'} adjusted a little so text stays easy to read.` : '';
}
function closeCustomEditor(revert) {
  const ed = $('customEditor');
  if (ed) ed.hidden = true;
  customDraft = null;
  if (revert && S.themePreview) { S.themePreview = false; applyTheme(S.themeSaved || { id: 'classic' }); }
}

// ---------------------------------------------------------------- friends
function dayCount(v) { return typeof v === 'number' ? v : Number(v && v.n) || 0; }
function streakFrom(days) {
  const d = new Date(); d.setHours(12, 0, 0, 0);
  const today = dayCount(days[dayKey(d)]);
  if (!today) d.setDate(d.getDate() - 1);
  let count = 0;
  while (dayCount(days[dayKey(d)]) > 0) { count++; d.setDate(d.getDate() - 1); }
  return { count, today };
}
function summarizeStats(st) {
  const days = (st && st.days) || {};
  const d = new Date(); d.setHours(12, 0, 0, 0);
  let week = 0, weekKnown = 0, weekRight = 0;
  const strip = [];
  for (let i = 0; i < 14; i++) {
    const k = dayKey(d); const v = days[k]; const n = dayCount(v);
    strip.unshift({ k, n });
    if (i < 7) { week += n; if (v && typeof v === 'object' && typeof v.r === 'number') { weekKnown += n; weekRight += v.r; } }
    d.setDate(d.getDate() - 1);
  }
  const s = streakFrom(days);
  return {
    streak: s.count, today: s.today, week, strip,
    acc: weekKnown ? Math.max(0, Math.min(100, (weekRight / weekKnown) * 100)) : null,
    mastered: Number(st && st.mastered) || 0, total: Number(st && st.total) || 0,
    lastActive: Number(st && st.lastActive) || 0,
    decks: (st && st.decks && typeof st.decks === 'object') ? st.decks : {},
  };
}
function ensureFriendsListener() {
  if (S.friendsListening || !dataUnsubs) return;
  S.friendsListening = true;
  dataUnsubs.push(onSnapshot(collection(db, 'stats'), (snap) => {
    const m = new Map(); snap.forEach(d => m.set(d.id, d.data()));
    S.stats = m; S.friendsLoaded = true; refresh();
  }, (e) => { console.error(e); S.friendsLoaded = true; refresh(); }));
}
function initialsOf(name) { return String(name || '?').split(/\s+/).filter(Boolean).slice(0, 2).map(w => w[0].toUpperCase()).join('') || '?'; }
function renderFriends() {
  ensureFriendsListener();
  const root = $('view-friends');
  if (!S.friendsLoaded || !S.profilesLoaded) { put(root, h('div', { class: 'block-note' }, h('p', { text: 'Loading everyone\'s progress…' }))); return; }
  const now = Date.now();
  const rows = [...S.profiles.entries()].filter(([, p]) => p.active !== false)
    .map(([uid, p]) => ({ uid, name: String(p.name || 'Friend'), me: uid === myUid(), s: summarizeStats(S.stats.get(uid)) }));
  const sortKey = S.friendsSort || 'week';
  rows.sort((a, b) => (sortKey === 'streak' ? b.s.streak - a.s.streak : sortKey === 'mastered' ? b.s.mastered - a.s.mastered : b.s.week - a.s.week) || a.name.localeCompare(b.name));
  const groupWeek = rows.reduce((a, r) => a + r.s.week, 0);
  const maxStrip = Math.max(1, ...rows.flatMap(r => r.s.strip.map(x => x.n)));
  const row = (r) => {
    const s = r.s;
    const deckList = Object.values(s.decks).filter(x => x && x.name).sort((a, b) => String(a.name).localeCompare(String(b.name)));
    const line = [
      h('span', null, h('b', { text: String(s.streak) }), s.streak === 1 ? ' day streak' : ' day streak'),
      h('span', null, h('b', { text: String(s.week) }), ' this week'),
      s.acc != null ? h('span', null, h('b', { text: pct(s.acc) }), ' right') : null,
    ];
    return h('li', { class: 'friend' + (r.me ? ' me' : '') },
      h('span', { class: 'f-avatar', 'aria-hidden': 'true', text: initialsOf(r.name) }),
      h('div', { class: 'f-main' },
        h('div', { class: 'f-name' }, h('span', { text: r.name }), r.me ? h('span', { class: 'pill uni', text: 'you' }) : null,
          h('span', { class: 'f-last', text: s.lastActive ? 'studied ' + ago(s.lastActive, now) : 'no activity yet' })),
        h('div', { class: 'f-line' }, ...line),
        h('div', { class: 'f-strip', role: 'img', 'aria-label': `Last 14 days: ${s.strip.map(x => x.n).join(', ')}` },
          ...s.strip.map(x => h('i', { title: `${x.k}: ${x.n}`, style: x.n ? `opacity:${(0.3 + 0.7 * Math.min(1, x.n / maxStrip)).toFixed(2)}` : '', class: x.n ? 'on' : '' }))),
        h('div', { class: 'f-mast' },
          h('span', { class: 'bar', 'aria-hidden': 'true' }, h('i', { style: `width:${s.total ? Math.round(s.mastered / s.total * 100) : 0}%` })),
          h('span', { text: s.total ? `${s.mastered.toLocaleString()} of ${s.total.toLocaleString()} mastered` : 'nothing to study yet' })),
        deckList.length ? h('details', { class: 'f-decks' }, h('summary', { text: `Shared decks (${deckList.length})` }),
          h('ul', null, ...deckList.map(x => h('li', null,
            h('span', { class: 'fd-name', text: String(x.name) }),
            h('span', { class: 'bar', 'aria-hidden': 'true' }, h('i', { style: `width:${x.total ? Math.round((Number(x.mastered) || 0) / x.total * 100) : 0}%` })),
            h('span', { class: 'mono', text: `${Number(x.mastered) || 0}/${Number(x.total) || 0}` }))))) : null));
  };
  put(root,
    h('div', { class: 'row', style: 'align-items:flex-start' },
      h('div', { style: 'flex:1 1 18rem;min-width:0' }, h('h1', { text: 'Friends' }),
        h('p', { class: 'lede', text: `How everyone is doing, updated live. The group wrote ${groupWeek.toLocaleString()} this week.` })),
      seg('friendsSort', [['week', 'This week'], ['streak', 'Streak'], ['mastered', 'Mastered']], sortKey, (k) => { S.friendsSort = k; renderFriends(); })),
    rows.length ? h('ul', { class: 'friends' }, ...rows.map(row)) : h('p', { class: 'empty-line', text: 'No one here yet.' }),
    h('p', { class: 'help', text: 'Totals include everyone\'s private decks, but only shared decks are listed by name. "Mastered" means right at least 3 times, including the last time.' }));
}

// ---------------------------------------------------------------- keeping names and summaries in sync
function stableStr(v) {
  if (Array.isArray(v)) return '[' + v.map(stableStr).join(',') + ']';
  if (v && typeof v === 'object') return '{' + Object.keys(v).sort().map(k => JSON.stringify(k) + ':' + stableStr(v[k])).join(',') + '}';
  return JSON.stringify(v);
}
function computeMyStats() {
  let mastered = 0, studied = 0, total = 0;
  const decks = {};
  for (const d of S.decks.values()) {
    if (category(d) === 'other') continue;
    const its = itemsOf(d);
    let dm = 0, ds = 0;
    for (const [iid] of its) { const pr = progOf(d.id, iid); if (pr && Number(pr.t)) ds++; if (isMastered(pr)) dm++; }
    total += its.length; mastered += dm; studied += ds;
    if (d.visibility === 'shared' && ds > 0) decks[d.id] = { name: d.name.slice(0, 80), kind: d.kind, total: its.length, mastered: dm, studied: ds };
  }
  return { mastered, studied, total, decks };
}
let statsTimer = 0;
// Runs at most once per delay, even while answers keep coming in.
function scheduleStatsSync(delay) {
  if (statsTimer) return;
  statsTimer = setTimeout(() => { statsTimer = 0; syncMyStats(); }, delay);
}
function syncMyStats() {
  if (!S.decksLoaded || !S.progressLoaded || !S.myStatsLoaded || !myUid()) return;
  const sum = computeMyStats();
  const cur = S.myStats || {};
  const same = cur.mastered === sum.mastered && cur.studied === sum.studied && cur.total === sum.total && stableStr(cur.decks || {}) === stableStr(sum.decks);
  // Days counted by version 2.0 (before the Friends tab) get copied over once, so streaks carry on.
  const legacy = {};
  for (const [k, v] of Object.entries(S.days || {})) if (Number(v) > 0 && !(cur.days && cur.days[k])) legacy[k] = { n: Number(v) };
  if (Object.keys(legacy).length && !S.legacyDaysCopied) {
    S.legacyDaysCopied = true;
    save(setDoc(doc(db, 'stats', myUid()), { days: legacy }, { merge: true }));
  }
  if (same) return;
  save(setDoc(doc(db, 'stats', myUid()), { ...sum, updatedAt: serverTimestamp() }, { mergeFields: ['mastered', 'studied', 'total', 'decks', 'updatedAt'] }));
}
let profileSyncing = false;
function syncProfiles() {
  if (!S.profilesLoaded || profileSyncing) return;
  const uid = myUid();
  if (S.isAdmin) {
    if (!S.peopleLoaded) return;
    const ops = [];
    for (const [id, u] of S.people) {
      const p = S.profiles.get(id);
      const want = { name: String(u.name || 'Friend').slice(0, 60), active: id === S.adminUid ? true : u.active === true };
      if (!p || p.name !== want.name || p.active !== want.active) ops.push([id, want]);
    }
    if (!ops.length) return;
    profileSyncing = true;
    const b = writeBatch(db);
    for (const [id, w] of ops) b.set(doc(db, 'profiles', id), w);
    save(b.commit()).finally(() => { profileSyncing = false; });
  } else if (S.me && !S.profiles.has(uid)) {
    profileSyncing = true;
    save(setDoc(doc(db, 'profiles', uid), { name: String(S.me.name || 'Friend').slice(0, 60) })).finally(() => { profileSyncing = false; });
  }
}

// ---------------------------------------------------------------- account
function renderAccount() {
  if (mounted.account) return;
  mounted.account = true;
  const name = h('input', { type: 'text', id: 'acName', maxlength: '60', value: myName(), autocomplete: 'name' });
  const status = h('p', { class: 'status', role: 'status' });
  const saveName = async () => {
    const v = name.value.trim();
    if (!v) { status.className = 'status err'; status.textContent = 'Your name can\'t be empty.'; return; }
    const ok = await save(updateDoc(doc(db, 'users', myUid()), { name: v.slice(0, 60) }));
    if (ok) await save(setDoc(doc(db, 'profiles', myUid()), { name: v.slice(0, 60) }, { merge: true }));
    if (ok && S.isAdmin) await save(updateDoc(doc(db, 'meta', 'admin'), { name: v.slice(0, 60) }));
    if (ok) { status.className = 'status ok'; status.textContent = 'Saved. Everyone will see the new name.'; }
  };
  put($('view-account'),
    h('div', null, h('h1', { text: 'Your account' }), h('p', { class: 'lede', text: (S.fbUser.email || '') + (S.isAdmin ? ' · admin' : '') })),
    h('form', { class: 'panel-box', novalidate: true, onsubmit: (e) => { e.preventDefault(); saveName(); } },
      field('Your name', name), h('div', { class: 'row' }, h('button', { type: 'submit', class: 'btn primary' }, 'Save name')), status),
    h('div', { class: 'panel-box' },
      h('h2', { text: 'Theme' }),
      h('p', { class: 'help', text: 'Colors from the iPhone lineups, each with its own matching accents. Your choice follows you to any device you sign in on.' }),
      h('div', { id: 'customEditor', class: 'custom-editor', hidden: true }),
      h('div', { id: 'themePicker', class: 'stack' })),
    h('div', { class: 'panel-box' },
      h('h2', { text: 'Password' }),
      h('p', { class: 'help', text: 'We\'ll email you a link to set a new password.' }),
      h('div', { class: 'row' }, h('button', { type: 'button', class: 'btn ghost', onclick: async () => {
        try { await sendPasswordResetEmail(auth, S.fbUser.email); toast('Check your email for a link to set a new password.'); } catch (e) { toast(authError(e)); }
      } }, 'Email me a reset link'))),
    h('div', null, h('button', { type: 'button', class: 'btn ghost', onclick: () => signOut(auth) }, 'Sign out')));
  renderThemePicker();
}

// ---------------------------------------------------------------- events
for (const b of document.querySelectorAll('.tab')) b.addEventListener('click', () => go(b.dataset.view));
$('whoBtn').addEventListener('click', () => go('account'));
$('endBtn').addEventListener('click', endSet);
$('undoBtn').addEventListener('click', undo);
$('typeInput').addEventListener('input', (e) => { if (S.session) S.session.typed = e.target.value; });
$('typeInput').addEventListener('keydown', (e) => {
  const s = S.session; if (!s || s.phase !== 'ask') return;
  const poem = s.kind === 'poems';
  if (e.key === 'Enter' && (poem ? (e.metaKey || e.ctrlKey) : !e.shiftKey)) { e.preventDefault(); revealOrCheck(); }
});
document.addEventListener('keydown', (e) => {
  const s = S.session;
  if (S.phase !== 'app' || S.view !== 'study' || !s) return;
  const tag = (e.target && e.target.tagName) || '';
  if (/INPUT|TEXTAREA|SELECT/.test(tag) || e.metaKey || e.ctrlKey || e.altKey) return;
  const k = e.key;
  if ((k === 'u' || k === 'U') && s.undo.length) { e.preventDefault(); undo(); return; }
  if (s.finished) return;
  const onOther = tag === 'BUTTON' && !e.target.hasAttribute('data-primary');
  const poem = s.kind === 'poems';
  if (s.phase === 'ask') {
    if (onOther && (k === ' ' || k === 'Enter')) return;
    if (k === ' ' || k === 'Enter') { e.preventDefault(); revealOrCheck(); }
    else if (k === 's' || k === 'S') { e.preventDefault(); skip(); }
    else if ((k === 'h' || k === 'H') && poem && s.hint < 2) { e.preventDefault(); s.hint++; renderCard(); }
    return;
  }
  if (s.mode === 'paper' && !poem) {
    if (k === 'ArrowLeft' || k === '1' || k === 'm' || k === 'M') { e.preventDefault(); commit(false); }
    else if (k === 'ArrowRight' || k === '2' || k === 'g' || k === 'G') { e.preventDefault(); commit(true); }
    else if (k === 'Enter' && !onOther) { e.preventDefault(); commit(true); }
  } else if (k === 'Enter' && !onOther) {
    e.preventDefault();
    const cur = currentItem(); if (cur) commit(outcome(s, cur.d, cur.it).right);
  }
});

try { S.themeSaved = JSON.parse(localStorage.getItem('rbh.theme') || 'null'); } catch (e) { S.themeSaved = null; }
applyTheme(S.themeSaved || { id: 'classic' });
boot();
