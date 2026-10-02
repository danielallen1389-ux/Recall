// Recall by Hand: draw a weighted set of facts or poems to write out by hand.
import { firebaseConfig } from './firebase-config.js';
import { initializeApp, getApps } from 'https://www.gstatic.com/firebasejs/12.19.0/firebase-app.js';
import {
  getAuth, onAuthStateChanged, signInWithEmailAndPassword, createUserWithEmailAndPassword,
  signOut, sendPasswordResetEmail, setPersistence, inMemoryPersistence
} from 'https://www.gstatic.com/firebasejs/12.19.0/firebase-auth.js';
import {
  initializeFirestore, persistentLocalCache, persistentMultipleTabManager,
  doc, collection, query, where, onSnapshot, setDoc, updateDoc, deleteDoc, deleteField, serverTimestamp, writeBatch, increment, getDocs
} from 'https://www.gstatic.com/firebasejs/12.19.0/firebase-firestore.js';

// Bump this with every release, and match it in index.html (twice) and version.json.
const APP_VERSION = '4.0.0';
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
const freshStudy = () => ({ kind: 'facts', sel: { facts: new Set(), poems: new Set() }, count: { facts: 10, poems: 1 }, mode: 'type', allow: 'deck' });
const freshDv = () => ({ open: null, q: '', editing: null, renaming: false, confirmDeck: false, creating: false, creatingFolder: false, expanded: new Set(), selecting: false, picked: new Set(),
  selectingDecks: false, pickedDecks: new Set(), folderEdit: null, folderConfirm: null, folderTools: null });
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
  folders: new Map(), folderParts: {}, foldersLoaded: false, pendingFolders: new Map(), placements: {}, placementsLoaded: false,
  bugs: new Map(), bugsLoaded: false, bugsListening: false, lastView: 'study',
  open: new Set(), pickOpen: new Set(),
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
// Each theme starts from an iPhone finish. Every theme has a light and a dark version and several accent sets.
// Only a few colors are picked by hand; the rest are derived and checked for readable contrast.
const CLASSIC_TOKENS = {
  light: {
    '--paper': '#EDF1F6', '--card': '#FFFFFF', '--ink': '#16203A', '--ink-soft': '#586379', '--line': '#D5DDE9', '--rule': '#D6E0EF',
    '--margin': '#D8524A', '--margin-text': '#C2413A', '--accent': '#2944C4', '--accent-text': '#2944C4', '--accent-soft': '#E3E8FA', '--accent-ink': '#FFFFFF',
    '--pen': '#2340B8', '--hl': '#FFE45E', '--hl-ink': '#352B00', '--ok': '#1F7A4D', '--ok-soft': '#DDF2E6', '--danger': '#B23A30', '--danger-soft': '#FBE7E4',
    '--case-up': '#7A3FC8', '--case-down': '#0B7A84',
    '--shadow': '0 1px 0 rgba(22,32,58,.05), 0 10px 26px -14px rgba(22,32,58,.32)', 'color-scheme': 'light',
  },
  dark: {
    '--paper': '#10141D', '--card': '#1A2030', '--ink': '#E7EBF3', '--ink-soft': '#9AA4B8', '--line': '#2B3446', '--rule': '#28334A',
    '--margin': '#E2716A', '--margin-text': '#E2716A', '--accent': '#8EA4FF', '--accent-text': '#8EA4FF', '--accent-soft': '#232C48', '--accent-ink': '#0E1430',
    '--pen': '#A9BAFF', '--hl': '#E9CF4E', '--hl-ink': '#2A2200', '--ok': '#6FD3A0', '--ok-soft': '#173225', '--danger': '#F08A80', '--danger-soft': '#3A1F1E',
    '--case-up': '#C9A6FF', '--case-down': '#66D3DD',
    '--shadow': '0 1px 0 rgba(0,0,0,.3), 0 12px 30px -14px rgba(0,0,0,.75)', 'color-scheme': 'dark',
  },
};
const THEME_KEYS = Object.keys(CLASSIC_TOKENS.light);
// [id, name, finish color, native mode, hand-picked colors for the native mode]
const THEME_LIST = [
  ['classic', 'Classic', '#C9D3E3', 'light', { bg: '#EDF1F6', card: '#FFFFFF', accent: '#2944C4', pen: '#2340B8', margin: '#D8524A', hl: '#FFE45E' }],
  ['white', 'White', '#F6F6F6', 'light', { bg: '#FAFAFA', card: '#FFFFFF', accent: '#2563EB', pen: '#1D4ED8', margin: '#E5413B', hl: '#FDE68A' }],
  ['cloud-white', 'Cloud White', '#F2F2EE', 'light', { bg: '#F5F5F2', accent: '#3E63DD', pen: '#2B49B8', margin: '#E05A4F', hl: '#FFE58A' }],
  ['silver', 'Silver', '#E2E3E4', 'light', { bg: '#EDEEF0', accent: '#3A4A63', pen: '#2D4C82', margin: '#D4544A', hl: '#FFE45E' }],
  ['white-titanium', 'White Titanium', '#EEEDE8', 'light', { bg: '#F4F3EF', accent: '#7A6544', pen: '#2B4762', margin: '#C2553E', hl: '#F3E1A6' }],
  ['natural-titanium', 'Natural Titanium', '#BDB7AD', 'light', { bg: '#EFEDE8', accent: '#4D5C6B', pen: '#2F4760', margin: '#BF4F2E', hl: '#F0DE9A' }],
  ['glacier', 'Glacier', '#C9DCE6', 'light', { bg: '#E9F1F5', accent: '#2C6E8F', pen: '#1D5B7A', margin: '#D8634D', hl: '#FFE3A6' }],
  ['sky-blue', 'Sky Blue', '#DCEAF4', 'light', { bg: '#EDF5FB', accent: '#2C74B0', pen: '#1C5A92', margin: '#E46A58', hl: '#FFF0A0' }],
  ['mist-blue', 'Mist Blue', '#9DB4D6', 'light', { bg: '#ECF1F8', accent: '#3A5C97', pen: '#284B88', margin: '#DB6E52', hl: '#FFE1A0' }],
  ['ultramarine', 'Ultramarine', '#8F9FF2', 'light', { bg: '#EEF0FD', accent: '#4352D6', pen: '#2F3DB8', margin: '#D9701F', hl: '#FFD8A6' }],
  ['deep-blue', 'Deep Blue', '#32374A', 'dark', { bg: '#11162A', accent: '#F29A4A', pen: '#AFC4FF', margin: '#F29A4A', hl: '#F2C14A' }],
  ['lavender', 'Lavender', '#DCCBEB', 'light', { bg: '#F4EFFA', accent: '#7046A8', pen: '#55348F', margin: '#C9577F', hl: '#E4F2A2' }],
  ['pink', 'Pink', '#F2B3D6', 'light', { bg: '#FDF0F6', accent: '#B83C78', pen: '#7A2C5B', margin: '#2F8A5B', hl: '#CDEFD8' }],
  ['burgundy', 'Burgundy', '#5E1A28', 'dark', { bg: '#1A0E12', accent: '#E8798F', pen: '#F4B9C6', margin: '#E3B65C', hl: '#E3B65C' }],
  ['cosmic-orange', 'Cosmic Orange', '#F77E2D', 'light', { bg: '#FFF1E6', accent: '#C4520E', pen: '#2350B5', margin: '#2F5BD3', hl: '#FFD3A8' }],
  ['desert-titanium', 'Desert Titanium', '#BFA38C', 'light', { bg: '#F5EEE6', accent: '#87553A', pen: '#2D4A6E', margin: '#B44E36', hl: '#F2D6A2' }],
  ['light-gold', 'Light Gold', '#EFE2C6', 'light', { bg: '#FAF4E4', accent: '#8E6210', pen: '#33489C', margin: '#C0533B', hl: '#F4D684' }],
  ['sage', 'Sage', '#A9B78C', 'light', { bg: '#F0F3E8', accent: '#4A6A2A', pen: '#2C4F33', margin: '#B4546C', hl: '#F5E49C' }],
  ['teal', 'Teal', '#A6D3CF', 'light', { bg: '#E9F5F3', accent: '#1C7670', pen: '#145954', margin: '#D2664A', hl: '#FFD9C7' }],
  ['black-titanium', 'Black Titanium', '#3A3A3B', 'dark', { bg: '#131313', accent: '#CDBA9C', pen: '#D6E1EC', margin: '#E07A5F', hl: '#CDBA9C' }],
  ['space-black', 'Space Black', '#2B2C30', 'dark', { bg: '#0D0E11', accent: '#7DD3FC', pen: '#C2DCFF', margin: '#FF6B6B', hl: '#F5D565' }],
  ['black', 'Black', '#232426', 'dark', { bg: '#101113', accent: '#9FB4FF', pen: '#C7D4FF', margin: '#FF7A6B', hl: '#E9CF4E' }],
].map(([id, name, finish, native, spec]) => ({ id, name, finish, native, spec }));
const THEME_BY_ID = new Map(THEME_LIST.map(t => [t.id, t]));
// Hand-picked accent pairings for some themes (hue, name); the rest come from color theory.
const THEME_PICKS = {
  sage: [[14, 'Terracotta'], [318, 'Plum'], [40, 'Honey']], pink: [[160, 'Mint'], [205, 'Sky'], [36, 'Apricot']],
  lavender: [[44, 'Honey'], [168, 'Jade'], [345, 'Rose']], glacier: [[14, 'Coral'], [40, 'Amber'], [265, 'Violet']],
  burgundy: [[44, 'Gold'], [168, 'Jade'], [212, 'Sky']], 'cosmic-orange': [[220, 'Blue'], [188, 'Teal'], [275, 'Violet']],
  'deep-blue': [[30, 'Orange'], [160, 'Jade'], [345, 'Rose']], teal: [[14, 'Coral'], [42, 'Amber'], [300, 'Plum']],
  'light-gold': [[222, 'Navy'], [14, 'Terracotta'], [168, 'Jade']], 'desert-titanium': [[200, 'Denim'], [150, 'Sage'], [345, 'Rose']],
};
for (const [id, picks] of Object.entries(THEME_PICKS)) THEME_BY_ID.get(id).picks = picks;
THEME_BY_ID.get('classic').other = { bg: '#10141D', card: '#1A2030', accent: '#8EA4FF', pen: '#A9BAFF', margin: '#E2716A', hl: '#E9CF4E' };

// ----- color math
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
// Nudges a color toward white (or black) until it reads clearly on every background given.
function ensureContrast(fg, bgs, ratio, towardWhite) {
  let c = fg;
  for (let i = 0; i < 40 && bgs.some(b => contrastRatio(c, b) < ratio); i++) c = mix(c, towardWhite ? '#FFFFFF' : '#000000', 0.07);
  return c;
}
function hexHsl(hex) {
  const [r, g, b] = hexRgb(hex).map(v => v / 255);
  const max = Math.max(r, g, b), min = Math.min(r, g, b), l = (max + min) / 2;
  if (max === min) return [0, 0, l * 100];
  const d = max - min, s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
  const hh = max === r ? (g - b) / d + (g < b ? 6 : 0) : max === g ? (b - r) / d + 2 : (r - g) / d + 4;
  return [hh * 60, s * 100, l * 100];
}
function hslHex(hh, s, l) {
  hh = ((hh % 360) + 360) % 360; s /= 100; l /= 100;
  const k = (n) => (n + hh / 30) % 12, a = s * Math.min(l, 1 - l);
  const f = (n) => l - a * Math.max(-1, Math.min(k(n) - 3, Math.min(9 - k(n), 1)));
  return rgbHex([f(0) * 255, f(8) * 255, f(4) * 255]);
}
const hueDist = (a, b) => { const d = Math.abs((((a - b) % 360) + 360) % 360); return Math.min(d, 360 - d); };
const colorDiff = (a, b) => { const A = hexRgb(a), B = hexRgb(b); return Math.abs(A[0] - B[0]) + Math.abs(A[1] - B[1]) + Math.abs(A[2] - B[2]); };
const prefersLightText = (bg) => contrastRatio('#FFFFFF', bg) >= contrastRatio('#111111', bg);

// ----- light/dark versions and accent sets
// The other mode's background keeps the finish's hue: Sage turns deep green, Pink turns plum, Burgundy turns pale rose.
function bgFor(t, mode) {
  if (t.native === mode) return t.spec.bg;
  if (t.other && t.other.bg) return t.other.bg;
  const [hh, s] = hexHsl(t.finish);
  if (mode === 'dark') return hslHex(hh, s < 10 ? 7 : Math.min(42, Math.max(24, s * 0.6)), 12);
  return hslHex(hh, s < 10 ? 9 : Math.min(48, Math.max(30, s * 0.8)), 94);
}
const ROLE_L = { accent: [38, 72], pen: [30, 80], margin: [46, 68], hl: [82, 62] };
function retune(hex, role, mode) {
  const [hh, s] = hexHsl(hex);
  return hslHex(hh, Math.min(85, role === 'hl' ? Math.max(s, 60) : Math.max(s, 35)), ROLE_L[role][mode === 'dark' ? 1 : 0]);
}
const HUE_NAMES = [[8, 'Red'], [18, 'Coral'], [32, 'Orange'], [44, 'Amber'], [56, 'Gold'], [72, 'Olive'], [95, 'Lime'], [140, 'Green'], [165, 'Jade'],
  [185, 'Teal'], [200, 'Cyan'], [215, 'Sky'], [235, 'Blue'], [255, 'Indigo'], [275, 'Violet'], [295, 'Purple'], [318, 'Plum'], [338, 'Magenta'], [352, 'Rose'], [361, 'Red']];
function hueName(hh) { hh = ((hh % 360) + 360) % 360; for (const [m, n] of HUE_NAMES) if (hh < m) return n; return 'Red'; }
function makeSet(hue, mode, name) {
  const d = mode === 'dark';
  return { name: name || hueName(hue), accent: hslHex(hue, 66, d ? 70 : 38), pen: hslHex(hue + 14, 56, d ? 80 : 30), margin: hslHex(hue + 150, 64, d ? 67 : 47), hl: hslHex(hue + 48, 85, d ? 62 : 82) };
}
// Accent sets that suit a base color: its original pairing first, then complementary and split-complementary hues.
function accentSets(baseHex, mode, original, picks) {
  const [H, S0] = hexHsl(baseHex);
  const hues = [...(picks || []), ...(S0 < 12 ? [222, 12, 168, 272, 40] : [H + 180, H + 150, H + 210, H + 120, H + 240, H + 35]).map(x => [x])];
  const out = original ? [original] : [];
  const hueOf = (x) => hexHsl(x.accent)[0];
  for (const [hue, name] of hues) {
    if (out.length >= 4) break;
    const set = makeSet(hue, mode, name);
    if (out.every(o => hueDist(hueOf(o), hueOf(set)) >= (name ? 20 : 35))) out.push(set);   // hand-picked ones may sit closer
  }
  return out;
}
function themeSets(t, mode) {
  const src = t.native === mode ? t.spec : (t.other || null);
  const original = src
    ? { name: 'Original', accent: src.accent, pen: src.pen, margin: src.margin, hl: src.hl }
    : { name: 'Original', accent: retune(t.spec.accent, 'accent', mode), pen: retune(t.spec.pen, 'pen', mode), margin: retune(t.spec.margin, 'margin', mode), hl: retune(t.spec.hl, 'hl', mode) };
  return accentSets(t.finish, mode, original, t.picks);
}
function presetSpec(t, mode, idx) {
  const sets = themeSets(t, mode);
  const set = sets[idx] || sets[0];
  const src = t.native === mode ? t.spec : t.other;
  return { mode, bg: bgFor(t, mode), card: src && src.card, accent: set.accent, pen: set.pen, margin: set.margin, hl: set.hl };
}

// ----- turning a few colors into the full set the page uses
// Backgrounds that are neither light nor dark (a bright blue or red) get cards in a deeper or lighter shade,
// so accents can keep their real color. Fills (buttons, bars) need less contrast than text, so they change less.
function deriveTheme(spec) {
  if (spec.ink || spec.mode) return deriveFor(spec, spec.ink ? lum(spec.ink) > lum(spec.bg) : spec.mode === 'dark');
  // A custom theme without a text color: use whichever of light or dark text keeps your colors closest to what you picked.
  const a = deriveFor(spec, true), b = deriveFor(spec, false);
  const cost = (t) => ['accent', 'pen', 'margin'].reduce((sum, k) => sum + (spec[k] ? colorDiff(spec[k], t['--' + k]) : 0), 0);
  const ca = cost(a), cb = cost(b);
  return Math.abs(ca - cb) < 24 ? (prefersLightText(spec.bg) ? a : b) : (ca < cb ? a : b);
}
function deriveFor(spec, dark) {
  const bg = spec.bg;
  const mid = Math.max(contrastRatio('#FFFFFF', bg), contrastRatio('#111111', bg)) < 7;
  const card = spec.card || (mid ? (dark ? mix(bg, '#000000', 0.42) : mix(bg, '#FFFFFF', 0.62)) : (dark ? mix(bg, '#FFFFFF', 0.07) : mix(bg, '#FFFFFF', 0.72)));
  const surf = [bg, card];
  const ink = spec.ink ? ensureContrast(spec.ink, surf, 4.5, dark) : ensureContrast(dark ? mix('#F1F3F7', spec.accent, 0.08) : mix('#15171D', spec.accent, 0.1), surf, 12, dark);
  const inkSoft = ensureContrast(mix(ink, bg, 0.42), surf, 4.6, dark);
  const accentSoft = mix(bg, spec.accent, dark ? 0.2 : 0.13);
  let accent = ensureContrast(spec.accent, surf, 3, dark);
  const accentText = ensureContrast(spec.accent, [bg, card, accentSoft], 4.5, dark);
  const accentInk = contrastRatio(accent, '#FFFFFF') >= contrastRatio(accent, '#111111') ? '#FFFFFF' : '#111111';
  accent = ensureContrast(accent, [accentInk], 4.5, accentInk !== '#FFFFFF');   // button text stays readable
  const pen = ensureContrast(spec.pen || spec.accent, [card], 4.5, dark);
  const marginBase = spec.margin || (dark ? '#E2716A' : '#D8524A');
  const hlBase = spec.hl || (dark ? '#E9CF4E' : '#FFE45E');
  const hlInk = contrastRatio(hlBase, '#111111') >= contrastRatio(hlBase, '#FFFFFF') ? '#111111' : '#FFFFFF';
  const hl = ensureContrast(hlBase, [hlInk], 4.5, hlInk !== '#FFFFFF');
  const okBase = dark ? '#6FD3A0' : '#1F7A4D', dangerBase = dark ? '#F08A80' : '#B23A30';
  const okSoft = mix(bg, okBase, dark ? 0.18 : 0.14), dangerSoft = mix(bg, dangerBase, dark ? 0.18 : 0.12);
  return {
    '--paper': bg, '--card': card, '--ink': ink, '--ink-soft': inkSoft,
    '--line': mix(card, ink, dark ? 0.18 : 0.15), '--rule': mix(card, spec.accent, dark ? 0.22 : 0.16),
    '--margin': ensureContrast(marginBase, [card], 2.2, dark), '--margin-text': ensureContrast(marginBase, [card], 4.5, dark),
    '--accent': accent, '--accent-text': accentText, '--accent-soft': accentSoft, '--accent-ink': accentInk,
    '--pen': pen, '--hl': hl, '--hl-ink': hlInk,
    '--ok': ensureContrast(okBase, [card, okSoft], 4.5, dark), '--ok-soft': okSoft,
    '--danger': ensureContrast(dangerBase, [card, dangerSoft], 4.5, dark), '--danger-soft': dangerSoft,
    '--case-up': ensureContrast(dark ? '#C9A6FF' : '#7A3FC8', [card], 4.5, dark), '--case-down': ensureContrast(dark ? '#66D3DD' : '#0B7A84', [card], 4.5, dark),
    '--shadow': dark ? '0 1px 0 rgba(0,0,0,.3), 0 12px 30px -14px rgba(0,0,0,.75)' : '0 1px 0 rgba(22,32,58,.05), 0 10px 26px -14px rgba(22,32,58,.32)',
    'color-scheme': dark ? 'dark' : 'light',
  };
}
// Which of your picked colors had to change noticeably to stay readable.
function adjustedColors(spec, tokens) {
  const pairs = [['text', spec.ink, '--ink'], ['accent', spec.accent, '--accent'], ['answer ink', spec.pen, '--pen'], ['margin line', spec.margin, '--margin']];
  return pairs.filter(([, mine, key]) => mine && colorDiff(mine, tokens[key]) > 48).map(([name]) => name);
}
const listWords = (a) => (a.length <= 1 ? a.join('') : a.slice(0, -1).join(', ') + ' and ' + a[a.length - 1]);
const deviceDark = () => !!(window.matchMedia && matchMedia('(prefers-color-scheme: dark)').matches);

// ----- saved themes: { id, mode: 'light'|'dark' (classic also 'auto'), accent: index } or { id: 'custom', custom: {...} }
function themeTokens(theme) {
  const th = theme || { id: 'classic' };
  if (th.id === 'custom') return th.custom && th.custom.bg && th.custom.accent ? deriveTheme(th.custom) : null;
  const t = THEME_BY_ID.get(th.id) || THEME_BY_ID.get('classic');
  const idx = Number(th.accent) || 0;
  if (t.id === 'classic') {
    if ((!th.mode || th.mode === 'auto') && !idx) return null;   // follows the device setting
    const m = th.mode === 'light' || th.mode === 'dark' ? th.mode : (deviceDark() ? 'dark' : 'light');
    return idx ? deriveTheme(presetSpec(t, m, idx)) : CLASSIC_TOKENS[m];
  }
  const mode = th.mode === 'light' || th.mode === 'dark' ? th.mode : t.native;
  return deriveTheme(presetSpec(t, mode, idx));
}
function themeMode(theme) {
  const th = theme || { id: 'classic' };
  if (th.id === 'classic' && (!th.mode || th.mode === 'auto')) return deviceDark() ? 'dark' : 'light';
  const tok = themeTokens(th);
  return tok && tok['color-scheme'] === 'dark' ? 'dark' : 'light';
}
function applyTheme(theme) {
  const root = document.documentElement;
  const tokens = themeTokens(theme);
  for (const k of THEME_KEYS) root.style.removeProperty(k);
  if (tokens) for (const [k, v] of Object.entries(tokens)) root.style.setProperty(k, v);
  const meta = document.querySelector('meta[name="theme-color"]');
  if (meta) meta.setAttribute('content', (tokens && tokens['--paper']) || (deviceDark() ? '#10141D' : '#EDF1F6'));
  S.theme = theme && theme.id ? theme : { id: 'classic' };
  return tokens;
}
function cacheTheme(theme) { try { localStorage.setItem('rbh.theme', JSON.stringify(theme)); } catch (e) { /* ignore */ } }
async function saveTheme(theme) {
  S.themeSaved = theme; S.themePreview = false;
  applyTheme(theme); cacheTheme(theme);
  if (myUid()) await save(updateDoc(doc(db, 'users', myUid()), { theme }));
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
// 2 = same word, 1 = small typo, 0 = different word. Capitals, accents and punctuation never count.
function wordScore(a, b) {
  if (a === b) return 2;
  const L = Math.max(a.length, b.length);
  if (L < 4 || Math.abs(a.length - b.length) > 2) return 0;
  return charDist(a, b) <= Math.max(1, Math.floor(L / 5)) ? 1 : 0;
}
// Pairs up as many of your words with the answer's words as possible, in reading order (earliest pairing wins ties).
function alignWords(a, b) {
  const n = a.length, m = b.length;
  if ((n + 1) * (m + 1) > 4e6) {
    const aSt = a.map((x, k) => (b[k] === x ? 'ok' : 'miss')), bSt = b.map((x, k) => (a[k] === x ? 'ok' : 'extra'));
    return { aSt, bSt, aPair: a.map((x, k) => (b[k] === x ? k : -1)) };
  }
  const W = m + 1;
  const s = new Uint16Array((n + 1) * W);
  for (let i = n - 1; i >= 0; i--) for (let j = m - 1; j >= 0; j--) {
    const down = s[(i + 1) * W + j], right = s[i * W + j + 1];
    let best = down > right ? down : right;
    const w = wordScore(a[i], b[j]);
    if (w) { const diag = s[(i + 1) * W + j + 1] + w; if (diag > best) best = diag; }
    s[i * W + j] = best;
  }
  const aSt = new Array(n).fill('miss'), bSt = new Array(m).fill('extra'), aPair = new Array(n).fill(-1);
  let i = 0, j = 0;
  while (i < n && j < m) {
    const w = wordScore(a[i], b[j]);
    if (w && s[i * W + j] === s[(i + 1) * W + j + 1] + w) { aSt[i] = bSt[j] = w === 2 ? 'ok' : 'typo'; aPair[i] = j; i++; j++; }
    else if (s[(i + 1) * W + j] >= s[i * W + j + 1]) i++;
    else j++;
  }
  return { aSt, bSt, aPair };
}
// Letters to add, remove, change or swap (a swapped pair like "fiebr" counts as one).
function charDist(a, b) {
  if (a === b) return 0;
  let prev2 = null, prev = Array.from({ length: b.length + 1 }, (_, j) => j);
  for (let i = 1; i <= a.length; i++) {
    const cur = [i];
    for (let j = 1; j <= b.length; j++) {
      let v = Math.min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (a[i - 1] === b[j - 1] ? 0 : 1));
      if (prev2 && i > 1 && j > 1 && a[i - 1] === b[j - 2] && a[i - 2] === b[j - 1]) v = Math.min(v, prev2[j - 2] + 1);
      cur[j] = v;
    }
    prev2 = prev; prev = cur;
  }
  return prev[b.length];
}
// Capitals don't count against you, but they're marked: 'up' = should be uppercase, 'down' = should be lowercase.
const caseLetters = (raw) => String(raw).normalize('NFC').replace(/[^\p{L}\p{N}]/gu, '');
function caseKind(expRaw, typedRaw) {
  const a = caseLetters(expRaw), b = caseLetters(typedRaw);
  if (a === b || a.length !== b.length || a.toLowerCase() !== b.toLowerCase()) return null;
  for (let k = 0; k < a.length; k++) if (a[k] !== b[k]) return a[k] !== a[k].toLowerCase() ? 'up' : 'down';
  return null;
}
function markCase(expWords, typedWords, aPair) {
  let n = 0;
  expWords.forEach((t, i) => {
    const j = aPair[i];
    if (t.st !== 'ok' || j < 0 || !typedWords[j]) return;
    const k = caseKind(t.raw, typedWords[j].raw);
    if (k) { t.cs = k; typedWords[j].cs = k; n++; }
  });
  return n;
}
const cleanEnds = (g) => String(g).replace(/^[^\p{L}\p{N}]+|[^\p{L}\p{N}]+$/gu, '');

// A plain answer (no lists): word by word, strictly in order. Short fact answers (1–2 words) go letter by letter.
function gradePlain(expected, typed, kind) {
  const et = tokens(expected), tt = tokens(typed);
  const ew = et.filter(t => t.word), tw = tt.filter(t => t.word);
  const r = alignWords(ew.map(t => t.norm), tw.map(t => t.norm));
  ew.forEach((t, k) => { t.st = r.aSt[k]; });
  tw.forEach((t, k) => { t.st = r.bSt[k]; });
  const cases = markCase(ew, tw, r.aPair);
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
  return { off: Math.min(100, off), et, tt, cases, gaps: gaps.map(cleanEnds).filter(Boolean) };
}

// ----- any-order lists
// {a; b; c} = these, in any order. {2: a; b; c} = at least 2 of these. Lists can sit inside list items.
// Returns null when the braces don't balance or a list is empty.
function parseAnswer(src) {
  const s = String(src || '');
  let i = 0;
  function seq(inList) {
    const parts = []; let buf = '';
    while (i < s.length) {
      const c = s[i];
      if (c === '{') {
        if (buf) parts.push({ t: 'text', raw: buf });
        buf = ''; i++;
        const l = list(); if (!l) return null;
        parts.push(l); continue;
      }
      if (c === '}') { if (!inList) return null; break; }
      if (c === ';' && inList) break;
      buf += c; i++;
    }
    if (buf) parts.push({ t: 'text', raw: buf });
    return { parts };
  }
  function list() {
    let min = null, minRaw = '';
    const m = /^\s*(\d{1,3})\s*:/.exec(s.slice(i));
    if (m) { min = Number(m[1]); minRaw = m[0]; i += m[0].length; }
    const items = [];
    for (;;) {
      const it = seq(true);
      if (!it || i >= s.length) return null;
      const c = s[i]; i++;
      if (it.parts.some(p => p.t === 'list' || normText(p.raw))) items.push(it);
      if (c === '}') break;
    }
    if (!items.length) return null;
    if (min != null && (min < 1 || min > items.length)) { items[0].parts.unshift({ t: 'text', raw: minRaw }); min = null; }   // e.g. {1945: …} is text
    return { t: 'list', min, items };
  }
  const root = seq(false);
  return root && i >= s.length ? root : null;
}
const hasList = (node) => !!node && node.parts.some(p => p.t === 'list');
function buildTree(node) {
  const segs = node.parts.map(p => (p.t === 'text' ? { t: 'text', toks: tokens(p.raw) } : { t: 'list', min: p.min, items: p.items.map(buildTree) }));
  const first = segs[0], last = segs[segs.length - 1];
  if (first && first.t === 'text') while (first.toks.length && first.toks[0].space) first.toks.shift();
  if (last && last.t === 'text') while (last.toks.length && last.toks[last.toks.length - 1].space) last.toks.pop();
  return { segs };
}
function nodeWords(n, out = []) {
  for (const seg of n.segs) {
    if (seg.t === 'text') { for (const t of seg.toks) if (t.word) out.push(t); }
    else for (const it of seg.items) nodeWords(it, out);
  }
  return out;
}
const ownWords = (n) => n.segs.filter(s => s.t === 'text').flatMap(s => s.toks.filter(t => t.word));
const nodeHasList = (n) => n.segs.some(s => s.t === 'list');
function nodeLabel(n) {
  const own = ownWords(n);
  const w = own.length ? own : nodeWords(n);
  const words = w.slice(0, 5).map(t => t.raw);
  return cleanEnds(words.join(' ')) + (w.length > 5 ? '…' : '');
}
// Where in your typed words an item fits best (local alignment); needs at least one exact word to count.
function localBest(itemNorms, tn, from, to) {
  const m = itemNorms.length, n = to - from;
  if (!m || n <= 0) return { score: 0, start: -1 };
  let prev = new Float32Array(n + 1), prevSt = new Int32Array(n + 1);
  let best = 0, bestStart = -1;
  for (let i = 1; i <= m; i++) {
    const cur = new Float32Array(n + 1), curSt = new Int32Array(n + 1);
    for (let j = 1; j <= n; j++) {
      const w = wordScore(itemNorms[i - 1], tn[from + j - 1]);
      const diag = prev[j - 1] + (w === 2 ? 2 : w === 1 ? 1 : -1);
      const up = prev[j] - 1, left = cur[j - 1] - 1;
      let v = 0, st = from + j - 1;
      if (diag > v) { v = diag; st = prev[j - 1] > 0 ? prevSt[j - 1] : from + j - 1; }
      if (up > v) { v = up; st = prevSt[j]; }
      if (left > v) { v = left; st = curSt[j - 1]; }
      cur[j] = v; curSt[j] = st;
      if (v > best || (v === best && v > 0 && st < bestStart)) { best = v; bestStart = st; }
    }
    prev = cur; prevSt = curSt;
  }
  return { score: best, start: bestStart };
}
// Finds where you typed each list item and gives it a stretch of your words to be checked against,
// so a sub-item only counts under its own parent ("fiber" written under Oranges doesn't count for Apples).
function placeItems(node, tn, from, to) {
  for (const seg of node.segs) {
    if (seg.t !== 'list') continue;
    // An item with its own sub-list is found by its own words ("Apples"), so its sub-items stay with it.
    // If you left that label out, it's looked for by its sub-items, but only in words no labeled item has claimed.
    const strong = [], weak = [];
    seg.items.forEach((it, k) => {
      const own = ownWords(it);
      if (nodeHasList(it) && own.length) {
        const r = localBest(own.map(t => t.norm), tn, from, to);
        if (r.score >= 2) strong.push({ it, k, score: r.score, start: r.start }); else weak.push({ it, k });
      } else {
        const r = localBest(nodeWords(it).map(t => t.norm), tn, from, to);
        if (r.score >= 1) strong.push({ it, k, score: r.score, start: r.start }); else weak.push({ it, k });
      }
    });
    strong.sort((a, b) => a.start - b.start || b.score - a.score || a.k - b.k);
    const freeEnd = strong.length ? strong[0].start : to;
    const weakHits = [];
    for (const w of weak) {
      const r = localBest(nodeWords(w.it).map(t => t.norm), tn, from, freeEnd);
      if (r.score >= 2) weakHits.push({ ...w, score: r.score, start: r.start, end: freeEnd }); else { w.it.region = [to, to]; placeItems(w.it, tn, to, to); }
    }
    weakHits.sort((a, b) => a.start - b.start || a.k - b.k);
    const assign = (list, limit) => list.forEach((f, idx) => {
      const end = idx + 1 < list.length ? Math.max(f.start + 1, list[idx + 1].start) : limit;
      f.it.region = [f.start, Math.min(limit, end)];
      placeItems(f.it, tn, f.it.region[0], f.it.region[1]);
    });
    assign(weakHits, freeEnd);
    assign(strong, to);
  }
}
// Checks sub-items inside their stretch first, then this part's own words against what's left, in order.
function alignNode(node, tw, tn, from, to, used, cases) {
  for (const seg of node.segs) if (seg.t === 'list') for (const it of seg.items) alignNode(it, tw, tn, it.region[0], it.region[1], used, cases);
  const own = ownWords(node);
  const idx = [];
  for (let k = from; k < to; k++) if (!used[k]) idx.push(k);
  const r = alignWords(own.map(t => t.norm), idx.map(k => tn[k]));
  own.forEach((t, i) => {
    t.st = r.aSt[i];
    const j = r.aPair[i];
    if (j < 0) return;
    const k = idx[j];
    used[k] = 1; tw[k].st = r.aSt[i];
    if (t.st === 'ok') { const c = caseKind(t.raw, tw[k].raw); if (c) { t.cs = c; tw[k].cs = c; cases.n++; } }
  });
}
// Within any list, each item counts the same; an item's own words and each of its sub-items share its part equally.
function scoreTree(node) {
  const parts = [];
  const own = ownWords(node);
  if (own.length) parts.push(own.reduce((a, t) => a + (t.st === 'ok' ? 1 : t.st === 'typo' ? 0.5 : 0), 0) / own.length);
  for (const seg of node.segs) {
    if (seg.t !== 'list') continue;
    const sc = seg.items.map(scoreTree);
    if (seg.min) {
      const ranked = seg.items.map((it, k) => ({ it, s: sc[k], k })).sort((a, b) => b.s - a.s || a.k - b.k);
      ranked.forEach((r, k) => { r.it.counted = k < seg.min; });
      parts.push(...ranked.slice(0, seg.min).map(r => r.s));
    } else {
      seg.items.forEach(it => { it.counted = true; });
      parts.push(...sc);
    }
  }
  node.score = parts.length ? parts.reduce((a, b) => a + b, 0) / parts.length : 1;
  return node.score;
}
// Items you didn't need (past a list's minimum) aren't marked as missing.
function markOptional(node, opt) {
  for (const seg of node.segs) {
    if (seg.t === 'text') { if (opt) for (const t of seg.toks) if (t.word && t.st === 'miss') t.st = 'opt'; }
    else for (const it of seg.items) markOptional(it, opt || (it.counted === false && !(it.score > 0)));
  }
}
// ownPath prefixes gaps in this part's own words; subPath prefixes gaps inside its sub-list ("Apples → vitamin C").
function collectGaps(node, ownPath, subPath, out) {
  const prefix = (p) => (p.length ? p.join(' → ') + ' → ' : '');
  let run = [];
  const flush = () => { if (run.length) { const g = cleanEnds(run.join(' ')); if (g) out.push(prefix(ownPath) + g); run = []; } };
  for (const seg of node.segs) {
    if (seg.t === 'text') { for (const t of seg.toks) { if (!t.word) continue; if (t.st === 'miss') run.push(t.raw); else flush(); } continue; }
    flush();
    const pre = prefix(subPath);
    const into = (it) => collectGaps(it, subPath, nodeHasList(it) ? [...subPath, nodeLabel(it)] : subPath, out);
    if (seg.min) {
      const got = seg.items.filter(it => it.score > 0).length;
      if (got < seg.min) {
        const left = seg.items.filter(it => !(it.score > 0)).map(nodeLabel);
        out.push(pre + `${seg.min - got} more of: ${left.slice(0, 6).join(', ')}${left.length > 6 ? ', …' : ''}`);
      }
      for (const it of seg.items) if (it.counted && it.score > 0 && it.score < 1) into(it);
    } else {
      for (const it of seg.items) {
        if (!(it.score > 0)) out.push(pre + nodeLabel(it));
        else if (it.score < 1) into(it);
      }
    }
  }
  flush();
}
const SEPARATORS = new Set(['and', 'or', 'then', 'also', 'plus', 'as', 'well']);
function gradeList(tree0, typed) {
  const tree = buildTree(tree0);
  const tt = tokens(typed), tw = tt.filter(t => t.word), tn = tw.map(t => t.norm);
  for (const t of tw) t.st = 'extra';
  placeItems(tree, tn, 0, tn.length);
  const used = new Uint8Array(tn.length), cases = { n: 0 };
  alignNode(tree, tw, tn, 0, tn.length, used, cases);
  for (const t of tw) if (t.st === 'extra' && SEPARATORS.has(t.norm)) t.st = 'sep';
  scoreTree(tree);
  markOptional(tree, false);
  const gaps = [];
  collectGaps(tree, [], [], gaps);
  return { off: Math.min(100, Math.max(0, (1 - tree.score) * 100)), tree, tt, cases: cases.n, gaps };
}
// How far off a typed answer is (0–100), which words to mark, and what's missing.
function grade(expected, typed, kind) {
  const parsed = kind === 'facts' ? parseAnswer(expected) : null;
  if (parsed && hasList(parsed)) return gradeList(parsed, typed);
  return gradePlain(expected, typed, kind);
}
function answerTree(src) { const p = parseAnswer(src); return p && hasList(p) ? buildTree(p) : null; }
// A one-line version of an answer for lists: fiber · vitamin C · antioxidants.
function answerPlain(src) {
  const p = parseAnswer(src);
  if (!p || !hasList(p)) return String(src || '');
  const walk = (node) => node.parts.map(pt => (pt.t === 'text' ? pt.raw
    : '(' + (pt.min ? `any ${pt.min} of: ` : '') + pt.items.map(it => walk(it).trim()).join(' · ') + ')')).join('');
  const out = walk(p).replace(/\s+/g, ' ').trim();
  return out.startsWith('(') && out.endsWith(')') && p.parts.length === 1 ? out.slice(1, -1) : out;
}

// ----- drawing marked answers
function tokenClass(t, side) {
  if (!t.word) return null;
  const c = [];
  if (t.st === 'typo') c.push('w-typo');
  else if (side === 'exp' && t.st === 'miss') c.push('w-miss');
  else if (side === 'exp' && t.st === 'opt') c.push('w-opt');
  else if (side === 'typed' && t.st === 'extra') c.push('w-extra');
  if (t.cs) c.push(t.cs === 'up' ? 'w-case-up' : 'w-case-down');
  return c.length ? c.join(' ') : null;
}
function renderTokens(list, side) {
  return list.map(t => (t.space ? document.createTextNode(t.raw) : h('span', { class: tokenClass(t, side), text: t.raw })));
}
function renderNode(node, marked) {
  const out = [];
  for (const seg of node.segs) {
    if (seg.t === 'text') {
      if (marked) out.push(...renderTokens(seg.toks, 'exp'));
      else out.push(document.createTextNode(seg.toks.map(t => t.raw).join('')));
      continue;
    }
    out.push(h('span', { class: 'ans-tag', text: seg.min ? `any ${seg.min} of these · any order` : 'any order' }));
    out.push(h('ul', { class: 'ans-list' }, ...seg.items.map(it => h('li', { class: marked && it.counted === false && !(it.score > 0) ? 'opt' : null }, ...renderNode(it, marked)))));
  }
  return out;
}
// Fills an element with the answer: marked against a check when there is one, with lists drawn as lists.
function renderAnswer(el, src, check) {
  if (check && check.et) return put(el, ...renderTokens(check.et, 'exp'));
  const tree = check && check.tree ? check.tree : answerTree(src);
  if (!tree) { el.textContent = String(src || ''); return el; }
  return put(el, ...renderNode(tree, !!(check && check.tree)));
}
function caseKey(check) {
  if (!check || !check.cases) return null;
  const words = [...(check.et || nodeWords(check.tree))];
  const up = words.some(t => t.cs === 'up'), down = words.some(t => t.cs === 'down');
  return h('p', { class: 'case-key' },
    h('span', { text: "Capitals don't count against you: " }),
    up ? h('span', null, h('span', { class: 'w-case-up', text: 'Aa' }), ' should be uppercase') : null,
    up && down ? h('span', { text: ' · ' }) : null,
    down ? h('span', null, h('span', { class: 'w-case-down', text: 'aA' }), ' should be lowercase') : null);
}

// ---------------------------------------------------------------- prefs (per person, per device)
function loadPrefs() {
  try {
    const p = JSON.parse(localStorage.getItem('rbh.prefs.' + myUid()) || '{}');
    if (p.kind === 'facts' || p.kind === 'poems') S.study.kind = p.kind;
    if (p.count) { S.study.count.facts = clampInt(p.count.facts, 1, 200, 10); S.study.count.poems = clampInt(p.count.poems, 1, 50, 1); }
    if (p.sel) for (const k of ['facts', 'poems']) if (Array.isArray(p.sel[k])) S.study.sel[k] = new Set(p.sel[k].filter(x => typeof x === 'string'));
    // How you answer is saved to your account instead (see setStudyMode), and starts as "Type it".
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
    shareSelf: typeof v.shareSelf === 'boolean' ? v.shareSelf : (legacyUniversal || v.visibility === 'shared'),
    hasShareSelf: typeof v.shareSelf === 'boolean',
    folderId: typeof v.folderId === 'string' && v.folderId ? v.folderId : null,
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
// What a study selection key (a deck, a folder, or 'u:<id>' for everything a friend shares) covers.
function deckKeys(d) {
  if (d.ownerId === myUid() || filedByMe(d)) return folderChain(myFolderFor(d)).map(f => f.id);
  const fid = d.folderId && S.folders.get(d.folderId) ? d.folderId : null;
  return [...folderChain(fid).map(f => f.id), 'u:' + d.ownerId];
}
const inSelection = (d, sel) => !sel || !sel.size || sel.has(d.id) || deckKeys(d).some(k => sel.has(k));
function pool(kind, sel) {
  const out = [];
  for (const d of studyDecks(kind)) {
    if (!inSelection(d, sel)) continue;
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

async function createDeck({ name, kind, visibility, friendsCanEdit, allowPct, items, folderId }) {
  const ref = doc(collection(db, 'decks'));
  const shareSelf = visibility === 'shared';
  const folder = folderId && S.folders.get(folderId) && S.folders.get(folderId).ownerId === myUid() ? folderId : null;
  const data = {
    name: name.slice(0, 80), kind, shareSelf, folderId: folder,
    visibility: shareSelf && (!folder || effectiveShared(folder)) ? 'shared' : 'private',
    friendsCanEdit: shareSelf && !!friendsCanEdit,
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
    await save(updateDoc(doc(db, 'decks', d.id), { scope: deleteField(), visibility: 'shared', shareSelf: true, friendsCanEdit: editors, updatedAt: serverTimestamp() }));
  }
}

// ---------------------------------------------------------------- folders
// Everyone has their own folder tree. A folder or deck is visible to friends only if it and every folder
// above it are shared ("private wins"). Filing a friend's shared deck into your own folder only changes your view.
function normFolder(id, v) {
  return {
    id, name: String(v.name || 'Untitled folder'), ownerId: String(v.ownerId || ''),
    parentId: typeof v.parentId === 'string' && v.parentId ? v.parentId : null,
    shareSelf: v.shareSelf !== false, visibility: v.visibility === 'shared' ? 'shared' : 'private',
  };
}
const foldersOf = (ownerId) => [...S.folders.values()].filter(f => f.ownerId === ownerId);
function folderChain(fid) {
  const out = [], seen = new Set();
  let f = fid ? S.folders.get(fid) : null;
  while (f && !seen.has(f.id)) { seen.add(f.id); out.push(f); f = f.parentId ? S.folders.get(f.parentId) : null; }
  return out;
}
const folderPath = (fid) => folderChain(fid).reverse().map(f => f.name).join(' / ');
const effectiveShared = (fid) => folderChain(fid).every(f => f.shareSelf);
const privateAncestor = (fid) => folderChain(fid).find(f => !f.shareSelf) || null;
function descendants(fid) {
  const out = new Set([fid]);
  let grew = true;
  while (grew) { grew = false; for (const f of S.folders.values()) if (f.parentId && out.has(f.parentId) && !out.has(f.id)) { out.add(f.id); grew = true; } }
  return out;
}
// Where a deck sits in your own tree: your decks by their folder, friends' decks where you filed them.
function myFolderFor(d) {
  const fid = d.ownerId === myUid() ? d.folderId : S.placements[d.id];
  const f = fid ? S.folders.get(fid) : null;
  return f && f.ownerId === myUid() ? f.id : null;
}
const filedByMe = (d) => d.ownerId !== myUid() && !!myFolderFor(d);
function folderOptions(excludeIds) {
  const mine = foldersOf(myUid()).filter(f => !(excludeIds && excludeIds.has(f.id)));
  return mine.map(f => ({ id: f.id, label: folderPath(f.id) })).sort((a, b) => a.label.localeCompare(b.label, undefined, { sensitivity: 'base' }));
}

// Writes the change you made plus any folders and decks whose "shared for real" status changed because of it.
async function commitTree(ownerId, explicit, extraOps) {
  const patches = new Map();
  const add = (col, id, p) => { const k = col + '/' + id; patches.set(k, { ...(patches.get(k) || {}), ...p }); };
  for (const [k, p] of explicit || []) { const [col, id] = k.split('/'); add(col, id, p); }
  for (const f of foldersOf(ownerId)) {
    const vis = effectiveShared(f.id) ? 'shared' : 'private';
    if (f.visibility !== vis) { add('folders', f.id, { visibility: vis }); f.visibility = vis; }
  }
  for (const d of S.decks.values()) {
    if (d.ownerId !== ownerId) continue;
    const f = d.folderId ? S.folders.get(d.folderId) : null;
    const inFolder = !!(f && f.ownerId === ownerId);
    if (d.folderId && !inFolder && S.foldersLoaded) { add('decks', d.id, { folderId: null }); d.folderId = null; }
    const vis = d.shareSelf && (!d.folderId || effectiveShared(d.folderId)) ? 'shared' : 'private';
    if (d.visibility !== vis) { add('decks', d.id, { visibility: vis }); d.visibility = vis; }
    if (!d.hasShareSelf) { add('decks', d.id, { shareSelf: d.shareSelf }); d.hasShareSelf = true; }
  }
  const ops = [...patches.entries()].map(([k, p]) => { const [col, id] = k.split('/'); return { ref: doc(db, col, id), patch: { ...p, updatedAt: serverTimestamp() } }; });
  const all = [...ops, ...(extraOps || [])];
  let ok = true;
  for (let i = 0; i < all.length; i += 400) {
    const b = writeBatch(db);
    for (const op of all.slice(i, i + 400)) {
      if (op.del) b.delete(op.ref);
      else if (op.set) b.set(op.ref, op.set, op.opts || {});
      else b.update(op.ref, op.patch);
    }
    ok = (await save(b.commit())) && ok;
  }
  return ok;
}
let treeChecked = false;
function checkTreeOnce() {
  if (treeChecked || !S.decksLoaded || !S.foldersLoaded || !myUid()) return;
  treeChecked = true;
  commitTree(myUid());
}

async function createFolder({ name, parentId, shareSelf }) {
  const ref = doc(collection(db, 'folders'));
  const parent = parentId && S.folders.get(parentId) && S.folders.get(parentId).ownerId === myUid() ? parentId : null;
  const vis = shareSelf && (!parent || effectiveShared(parent)) ? 'shared' : 'private';
  const data = { name: name.slice(0, 80), ownerId: myUid(), parentId: parent, shareSelf: !!shareSelf, visibility: vis };
  const local = normFolder(ref.id, data);
  S.pendingFolders.set(ref.id, local);
  S.folders.set(ref.id, local);
  await setDoc(ref, { ...data, createdAt: serverTimestamp(), updatedAt: serverTimestamp() });
  return ref.id;
}
function renameFolder(f, name) {
  f.name = name.slice(0, 80);
  return save(updateDoc(doc(db, 'folders', f.id), { name: f.name, updatedAt: serverTimestamp() }));
}
function setFolderShare(f, v) {
  f.shareSelf = v;
  return commitTree(f.ownerId, [['folders/' + f.id, { shareSelf: v }]]);
}
function moveFolder(f, parentId) {
  if (parentId && descendants(f.id).has(parentId)) { toast("A folder can't go inside itself."); return Promise.resolve(false); }
  f.parentId = parentId || null;
  return commitTree(f.ownerId, [['folders/' + f.id, { parentId: f.parentId }]]);
}
// Deleting a folder keeps what's inside: its folders and decks move up one level.
function deleteFolder(f) {
  const up = f.parentId || null;
  const explicit = [];
  for (const c of S.folders.values()) if (c.parentId === f.id) { c.parentId = up; explicit.push(['folders/' + c.id, { parentId: up }]); }
  for (const d of S.decks.values()) if (d.ownerId === f.ownerId && d.folderId === f.id) { d.folderId = up; explicit.push(['decks/' + d.id, { folderId: up }]); }
  const extra = [{ del: true, ref: doc(db, 'folders', f.id) }];
  if (f.ownerId === myUid()) {
    const moved = {};
    for (const [deckId, fid] of Object.entries(S.placements)) if (fid === f.id) { moved[deckId] = up || deleteField(); if (up) S.placements[deckId] = up; else delete S.placements[deckId]; }
    if (Object.keys(moved).length) extra.push({ ref: doc(db, 'placements', myUid()), set: { decks: moved, updatedAt: serverTimestamp() }, opts: { merge: true } });
  }
  S.folders.delete(f.id);
  return commitTree(f.ownerId, explicit, extra);
}
// Moves decks into one of your folders (null = top level). Your decks move for real; friends' decks are filed for you only.
async function moveDecks(deckIds, folderId) {
  const fid = folderId || null;
  const own = [], filed = {};
  for (const id of deckIds) {
    const d = S.decks.get(id); if (!d) continue;
    if (d.ownerId === myUid()) { d.folderId = fid; own.push(['decks/' + d.id, { folderId: fid }]); }
    else { filed[d.id] = fid || deleteField(); if (fid) S.placements[d.id] = fid; else delete S.placements[d.id]; }
  }
  const extra = Object.keys(filed).length ? [{ ref: doc(db, 'placements', myUid()), set: { decks: filed, updatedAt: serverTimestamp() }, opts: { merge: true } }] : [];
  return commitTree(myUid(), own, extra);
}
function setDeckShare(d, v) {
  d.shareSelf = v;
  return commitTree(d.ownerId, [['decks/' + d.id, { shareSelf: v }]]);
}

// ----- trees for display: which folders and decks sit at each level
function makeTree(folders, decks, placeOf) {
  const ids = new Set(folders.map(f => f.id));
  const kids = new Map();
  const get = (k) => { if (!kids.has(k)) kids.set(k, { folders: [], decks: [] }); return kids.get(k); };
  for (const f of folders) get(f.parentId && ids.has(f.parentId) ? f.parentId : '').folders.push(f);
  for (const d of decks) { const p = placeOf(d); get(p && ids.has(p) ? p : '').decks.push(d); }
  const seen = new Set();
  const walk = (k) => { for (const f of (kids.get(k) || { folders: [] }).folders) if (!seen.has(f.id)) { seen.add(f.id); walk(f.id); } };
  walk('');
  for (const f of folders) if (!seen.has(f.id)) {   // a folder caught in a loop shows at the top level
    for (const v of kids.values()) v.folders = v.folders.filter(x => x.id !== f.id);
    get('').folders.push(f); seen.add(f.id); walk(f.id);
  }
  const byName = (a, b) => a.name.localeCompare(b.name, undefined, { sensitivity: 'base' });
  for (const v of kids.values()) { v.folders.sort(byName); v.decks.sort(byName); }
  return { at: (k) => kids.get(k || '') || { folders: [], decks: [] } };
}
function treeDecks(tree, k, out = []) {
  const n = tree.at(k);
  out.push(...n.decks);
  for (const f of n.folders) treeDecks(tree, f.id, out);
  return out;
}
const myTreeDecks = (filter) => [...S.decks.values()].filter(d => (d.ownerId === myUid() || (filedByMe(d) && category(d) !== 'other')) && (!filter || filter(d)));
const myTree = (filter) => makeTree(foldersOf(myUid()), myTreeDecks(filter), myFolderFor);
// Someone else's decks you haven't filed, in their folders.
function ownerTree(uid, filter) {
  const decks = [...S.decks.values()].filter(d => d.ownerId === uid && !filedByMe(d) && (S.isAdmin || d.visibility === 'shared') && (!filter || filter(d)));
  return { decks, tree: makeTree(foldersOf(uid), decks, d => d.folderId) };
}
function otherOwners(filter) {
  const ids = new Set();
  for (const d of S.decks.values()) if (d.ownerId !== myUid() && !filedByMe(d) && (S.isAdmin || d.visibility === 'shared') && (!filter || filter(d))) ids.add(d.ownerId);
  return [...ids].sort((a, b) => ownerLabel({ ownerId: a }).localeCompare(ownerLabel({ ownerId: b })));
}
function loadOpen() {
  try {
    const o = JSON.parse(localStorage.getItem('rbh.open.' + myUid()) || '{}');
    S.open = new Set(Array.isArray(o.decks) ? o.decks : []);
    S.pickOpen = new Set(Array.isArray(o.pick) ? o.pick : []);
  } catch (e) { S.open = new Set(); S.pickOpen = new Set(); }
}
function saveOpen() {
  try { localStorage.setItem('rbh.open.' + myUid(), JSON.stringify({ decks: [...S.open], pick: [...S.pickOpen] })); } catch (e) { /* ignore */ }
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
    loadOpen();
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
    if (S.me && (S.me.studyMode === 'type' || S.me.studyMode === 'paper') && !S.session) S.study.mode = S.me.studyMode;
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
  const fpart = (name) => (snap) => {
    const m = new Map();
    snap.forEach(d => m.set(d.id, normFolder(d.id, d.data())));
    S.folderParts[name] = m;
    const merged = new Map();
    for (const p of Object.values(S.folderParts)) for (const [k, v] of p) merged.set(k, v);
    for (const [k, v] of S.pendingFolders) { if (merged.has(k)) S.pendingFolders.delete(k); else merged.set(k, v); }
    S.folders = merged;
    S.foldersLoaded = Object.keys(S.folderParts).length >= expected;
    refresh();
  };
  const folders = collection(db, 'folders');
  if (S.isAdmin) dataUnsubs.push(onSnapshot(folders, fpart('all'), onErr));
  else {
    dataUnsubs.push(onSnapshot(query(folders, where('ownerId', '==', uid)), fpart('mine'), onErr));
    dataUnsubs.push(onSnapshot(query(folders, where('visibility', '==', 'shared')), fpart('shared'), onErr));
  }
  dataUnsubs.push(onSnapshot(doc(db, 'placements', uid), (s) => {
    const d = s.exists() ? s.data() : {};
    S.placements = (d.decks && typeof d.decks === 'object') ? { ...d.decks } : {};
    S.placementsLoaded = true;
    refresh();
  }, (e) => { console.error(e); S.placementsLoaded = true; }));
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
  S.folders = new Map(); S.folderParts = {}; S.foldersLoaded = false; S.pendingFolders = new Map(); S.placements = {}; S.placementsLoaded = false;
  S.bugs = new Map(); S.bugsLoaded = false; S.bugsListening = false; treeChecked = false;
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
  checkTreeOnce();
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
  if (view === 'account' && S.view !== 'account') S.lastView = S.view;
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
  who.title = S.isAdmin ? 'Settings (admin)' : 'Settings';
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
          seg('answerMode', [['type', 'Type it'], ['paper', 'On paper']], S.study.mode, (k) => setStudyMode(k)),
          h('p', { class: 'help', id: 'modeHelp', style: 'margin-top:.45rem' })),
        h('div', null, h('label', { class: 'label', for: 'allowSel', text: 'Allowed mistakes' }),
          allowSelect('allowSel', S.study.allow, (v) => { S.study.allow = v; savePrefs(); renderSetup(); }, true),
          h('p', { class: 'help', id: 'allowHelp', style: 'margin-top:.45rem' }))),
      h('dl', { class: 'stats', id: 'poolStats' }),
      h('div', { id: 'likelyWrap' }, h('span', { class: 'label', text: 'Most likely to come up' }), h('ul', { class: 'likely', id: 'likely' })),
      h('div', null, h('button', { type: 'button', class: 'btn primary big', id: 'startBtn', onclick: () => startSession() }, 'Draw')),
      helpPanel('study'),
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
  if (!loading && S.foldersLoaded) for (const k of [...sel]) {
    const ok = decks.some(d => d.id === k || 'u:' + d.ownerId === k) || S.folders.has(k);
    if (!ok) sel.delete(k);
  }
  const all = pool(kind, null);
  $('studyLoading').hidden = !loading;
  $('studyEmpty').hidden = loading || all.length > 0;
  $('studyMain').hidden = loading || all.length === 0;
  $('studyEmptyText').textContent = kind === 'poems'
    ? 'No poems yet. Add one and it will be ready to draw here.'
    : 'No facts yet. Paste a batch and they will be ready to draw here.';
  if (loading || !all.length) return;

  renderPicker(kind, sel, all.length);

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
  const deckAllows = [...new Set(decks.filter(d => inSelection(d, sel)).map(d => d.allowPct))].sort((a, b) => a - b);
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
  const how = S.study.mode === 'type' ? ' · typing' : ' · on paper';
  b.textContent = !items.length ? `No ${noun}s in these decks` : (items.length < curCount() ? `Draw all ${plural(items.length, noun)}` : `Draw ${plural(k, noun)}`) + (items.length ? how : '');
}

// The "Draw from" picker: your folders and decks, then each friend's shared folders and decks.
// Ticking a folder (or a friend) includes everything inside it, including decks added later.
function renderPicker(kind, sel, allCount) {
  const box = $('chipGroups');
  const has = (d) => d.kind === kind && category(d) !== 'other';
  const count = (list) => list.reduce((a, d) => a + itemsOf(d).length, 0);
  const rerender = () => { savePrefs(); renderSetup(); };
  const row = (key, label, n, ancestors, opts) => {
    const inherited = ancestors.some(k => sel.has(k));
    const id = 'pk-' + key.replace(/[^A-Za-z0-9_-]/g, '_');
    const cb = h('input', { type: 'checkbox', id, checked: inherited || sel.has(key), disabled: inherited, 'data-key': id });
    cb.addEventListener('change', () => { if (cb.checked) sel.add(key); else sel.delete(key); rerender(); });
    const caret = opts.folder
      ? h('button', { type: 'button', class: 'pick-caret', 'aria-expanded': opts.open ? 'true' : 'false', 'aria-label': (opts.open ? 'Close ' : 'Open ') + label, 'data-key': 'pc-' + id,
          onclick: () => { if (opts.open) S.pickOpen.delete(key); else S.pickOpen.add(key); saveOpen(); renderSetup(); } }, opts.open ? '▾' : '▸')
      : h('span', { class: 'pick-caret', 'aria-hidden': 'true' });
    return h('div', { class: 'pick-row' + (opts.folder ? ' is-folder' : '') }, caret,
      h('label', { class: 'check', for: id }, cb, opts.person ? h('span', { class: 'person-icon', 'aria-hidden': 'true', text: (label.trim()[0] || '?').toUpperCase() }) : opts.folder ? h('span', { class: 'folder-icon', 'aria-hidden': 'true' }) : null,
        h('span', { class: 'pick-name', text: label }), opts.by ? h('span', { class: 'by', text: 'by ' + opts.by }) : null),
      h('span', { class: 'pick-n mono', text: n.toLocaleString() }));
  };
  const branch = (tree, k, ancestors) => {
    const at = tree.at(k), out = [];
    for (const f of at.folders) {
      const ds = treeDecks(tree, f.id);
      if (!ds.length) continue;
      const open = S.pickOpen.has(f.id);
      out.push(h('li', null, row(f.id, f.name, count(ds), ancestors, { folder: true, open }),
        open ? h('ul', { class: 'pick-tree' }, ...branch(tree, f.id, [...ancestors, f.id])) : null));
    }
    for (const d of at.decks) out.push(h('li', null, row(d.id, d.name, itemsOf(d).length, ancestors, { by: d.ownerId !== myUid() ? ownerLabel(d) : null })));
    return out;
  };
  const mine = branch(makeTree(foldersOf(myUid()), myTreeDecks(has), myFolderFor), '', []);
  const friends = otherOwners(has).map(uid => {
    const { decks: ds, tree } = ownerTree(uid, has);
    if (!ds.length) return null;
    const key = 'u:' + uid, open = S.pickOpen.has(key);
    return h('li', null, row(key, ownerLabel({ ownerId: uid }), count(ds), [], { folder: true, person: true, open }),
      open ? h('ul', { class: 'pick-tree' }, ...branch(tree, '', [key])) : null);
  }).filter(Boolean);
  withFocus(box, () => put(box,
    h('div', { class: 'chips' }, chip(kind === 'poems' ? 'All poems' : 'All facts', allCount, sel.size === 0, () => { sel.clear(); rerender(); }, 'pool', 'all'),
      sel.size ? h('span', { class: 'help', text: 'or pick below' }) : h('span', { class: 'help', text: 'or tick folders and decks below' })),
    mine.length ? h('div', { class: 'chip-group' }, h('h3', { text: 'Mine' }), h('ul', { class: 'pick-tree' }, ...mine)) : null,
    friends.length ? h('div', { class: 'chip-group' }, h('h3', { text: 'Shared by friends' }), h('ul', { class: 'pick-tree' }, ...friends)) : null));
}
// "Type it" or "On paper": saved to your account so it follows you to every device.
function setStudyMode(k) {
  if (k !== 'type' && k !== 'paper') return;
  S.study.mode = k;
  savePrefs();
  if (S.me && S.me.studyMode !== k && myUid()) save(updateDoc(doc(db, 'users', myUid()), { studyMode: k }));
  renderSetup();
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
  if (poem) { if (shown && typed && s.check) put(ans, ...renderTokens(s.check.et, 'exp')); else ans.textContent = it.text; }
  else renderAnswer(ans, it.a, shown && typed ? s.check : null);
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
          gaps.slice(0, 10).map(g => `“${g}”`).join(', ') + (gaps.length > 10 ? `, and ${gaps.length - 10} more` : '')) : null,
        caseKey(s.check)));
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
      h('span', { class: 'da' + (poem ? '' : ' hand'), text: [poem ? (it.author || '') : answerPlain(it.a), ...notes].filter(Boolean).join(' · ') }));
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
  const dv = S.dv;
  const pick = dv.selectingDecks ? h('input', { type: 'checkbox', class: 'pick', checked: dv.pickedDecks.has(d.id), 'aria-label': `Select ${d.name}`, 'data-key': 'pd-' + d.id,
    onchange: (e) => { if (e.target.checked) dv.pickedDecks.add(d.id); else dv.pickedDecks.delete(d.id); withFocus($('view-decks'), () => renderDecks(true)); } }) : null;
  return h('li', { class: 'deck-row' + (pick ? ' sel-mode' : '') }, pick,
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
function folderSelect(id, current, excludeIds, topLabel) {
  const sel = h('select', { id, 'data-key': id },
    h('option', { value: '', text: topLabel || 'Top level (no folder)' }),
    ...folderOptions(excludeIds).map(o => h('option', { value: o.id, text: o.label })));
  sel.value = current || '';
  return sel;
}
// One folder in a tree, with its contents when open. manage: you can rename, share, move and delete it.
function folderNode(tree, f, opts, now) {
  const dv = S.dv;
  const open = S.open.has(f.id);
  const tools = open && opts.manage && (dv.folderTools === f.id || dv.folderEdit === f.id || dv.folderConfirm === f.id);
  const inside = treeDecks(tree, f.id);
  const hiddenBy = f.shareSelf ? privateAncestor(f.parentId) : null;
  const toggle = () => { if (open) S.open.delete(f.id); else S.open.add(f.id); saveOpen(); renderDecks(true); };
  const head = h('div', { class: 'folder-head' },
    h('button', { type: 'button', class: 'folder-toggle', 'aria-expanded': open ? 'true' : 'false', 'data-key': 'ft-' + f.id, onclick: toggle },
      h('span', { class: 'caret', 'aria-hidden': 'true', text: open ? '▾' : '▸' }),
      h('span', { class: 'folder-icon', 'aria-hidden': 'true' }),
      h('span', { class: 'folder-name', text: f.name })),
    h('span', { class: 'dm' },
      opts.manage ? h('span', { class: 'pill ' + (f.visibility === 'shared' ? 'shared' : 'private'), text: f.visibility === 'shared' ? 'Shared' : 'Private' }) : null,
      h('span', { text: plural(inside.length, 'deck') }),
      opts.manage ? h('button', { type: 'button', class: 'linkbtn quiet folder-opts', 'aria-expanded': tools ? 'true' : 'false', 'data-key': 'fo-' + f.id,
        'aria-label': (tools ? 'Close options for ' : 'Options for ') + f.name,
        onclick: () => { dv.folderTools = tools ? null : f.id; dv.folderEdit = null; dv.folderConfirm = null; if (!tools) { S.open.add(f.id); saveOpen(); } renderDecks(true); } }, tools ? 'Done' : 'Options') : null));
  const kids = [];
  if (open) {
    if (tools) {
      if (dv.folderEdit === f.id) {
        const inp = h('input', { type: 'text', id: 'folderRename', maxlength: '80', value: f.name, 'aria-label': 'Folder name' });
        const done = () => { dv.folderEdit = null; dv.folderTools = null; renderDecks(true); };
        const ok = () => { const v = inp.value.trim(); if (!v) { toast('Give the folder a name.'); return; } renameFolder(f, v); done(); };
        inp.addEventListener('keydown', (e) => { if (e.key === 'Enter') ok(); if (e.key === 'Escape') done(); });
        setTimeout(() => inp.focus(), 0);
        kids.push(h('div', { class: 'folder-tools row' }, h('div', { style: 'flex:1 1 12rem;min-width:0' }, inp),
          h('button', { type: 'button', class: 'btn primary', onclick: ok }, 'Save'), h('button', { type: 'button', class: 'btn ghost', onclick: done }, 'Cancel')));
      } else if (dv.folderConfirm === f.id) {
        kids.push(h('div', { class: 'folder-tools confirm' },
          h('span', { text: `Delete the folder ${f.name}? Everything inside moves up a level; no decks are deleted.` }),
          h('button', { type: 'button', class: 'btn danger', onclick: async () => { dv.folderConfirm = null; dv.folderTools = null; S.open.delete(f.id); saveOpen(); await deleteFolder(f); toast(`Deleted the folder ${f.name}.`); renderDecks(true); } }, 'Delete folder'),
          h('button', { type: 'button', class: 'btn ghost', onclick: () => { dv.folderConfirm = null; renderDecks(true); } }, 'Keep it')));
      } else {
        const moveSel = folderSelect('fm-' + f.id, f.parentId, descendants(f.id), 'Top level');
        moveSel.addEventListener('change', async () => { await moveFolder(f, moveSel.value || null); renderDecks(true); });
        kids.push(h('div', { class: 'folder-tools' },
          check('fs-' + f.id, 'Share with friends', f.shareSelf, async (v) => {
            await setFolderShare(f, v);
            toast(v ? (privateAncestor(f.parentId) ? `Shared, but ${privateAncestor(f.parentId).name} above it is still private.` : `Friends can now see ${f.name} and the shared decks in it.`) : `${f.name} and everything in it is private now.`);
            renderDecks(true);
          }),
          hiddenBy ? h('p', { class: 'help', text: `Friends can't see it while the folder ${hiddenBy.name} above it is private.` }) : null,
          h('div', { class: 'row' },
            h('button', { type: 'button', class: 'linkbtn', onclick: () => { dv.creatingFolder = true; dv.newFolderParent = f.id; renderDecks(true); window.scrollTo({ top: 0 }); } }, 'New folder inside'),
            h('button', { type: 'button', class: 'linkbtn', onclick: () => { dv.folderEdit = f.id; renderDecks(true); } }, 'Rename'),
            h('button', { type: 'button', class: 'linkbtn warn', onclick: () => { dv.folderConfirm = f.id; renderDecks(true); } }, 'Delete folder')),
          h('div', { class: 'row' }, h('label', { class: 'label', for: 'fm-' + f.id, style: 'margin:0', text: 'Move into' }), moveSel)));
      }
    }
    const inner = treeNodes(tree, f.id, opts, now);
    kids.push(inner.length ? h('ul', { class: 'tree' }, ...inner) : h('p', { class: 'empty-line', text: 'Empty folder.' }));
  }
  return h('li', { class: 'folder' + (open ? ' open' : '') }, head, ...kids);
}
function treeNodes(tree, k, opts, now) {
  const at = tree.at(k);
  const folders = opts.hideEmpty ? at.folders.filter(f => treeDecks(tree, f.id).length) : at.folders;
  return [...folders.map(f => folderNode(tree, f, opts, now)), ...at.decks.map(d => deckRow(d, d.ownerId !== myUid() && opts.showOwner !== false, now))];
}
function renderDecks(force) {
  const root = $('view-decks');
  const dv = S.dv;
  if (!force && (dv.editing || dv.renaming || dv.creating || dv.creatingFolder || dv.folderEdit)) return;   // keep forms the person is typing in
  if (!S.decksLoaded || !S.foldersLoaded) { put(root, h('div', { class: 'block-note' }, h('p', { text: 'Loading your decks…' }))); return; }
  if (dv.open && S.decks.has(dv.open)) return renderDeckDetail(root);
  dv.open = null;
  const now = Date.now();

  const mine = myTree();
  const mineNodes = treeNodes(mine, '', { manage: true }, now);
  const sections = [h('div', { class: 'deck-section' }, h('h3', { text: 'My decks' }),
    mineNodes.length ? h('ul', { class: 'tree' }, ...mineNodes) : h('p', { class: 'empty-line', text: 'You have no decks yet. Make one with New deck.' }))];
  const owners = otherOwners();
  const groups = owners.map(uid => {
    const { tree } = ownerTree(uid);
    const nodes = treeNodes(tree, '', { manage: S.isAdmin, hideEmpty: !S.isAdmin, showOwner: false }, now);
    return nodes.length ? h('div', { class: 'owner-group' }, h('span', { class: 'owner-name', text: ownerLabel({ ownerId: uid }) }), h('ul', { class: 'tree' }, ...nodes)) : null;
  }).filter(Boolean);
  sections.push(h('div', { class: 'deck-section' }, h('h3', { text: S.isAdmin ? "Everyone else's decks" : 'Shared by friends' }),
    groups.length ? h('div', null, ...groups) : h('p', { class: 'empty-line', text: S.isAdmin ? 'Nobody else has made a deck yet.' : 'When friends share decks, they show up here. Decks you file into your own folders move up to My decks.' })));

  put(root,
    h('div', { class: 'row', style: 'align-items:flex-start' },
      h('div', { style: 'flex:1 1 18rem;min-width:0' }, h('h1', { text: 'Decks' }),
        h('p', { class: 'lede', text: S.isAdmin ? 'Your folders and decks, and every deck your friends have made.' : 'Your folders and decks, and the ones friends share with you.' })),
      h('div', { class: 'row' },
        h('button', { type: 'button', class: 'btn ghost', 'aria-pressed': dv.selectingDecks ? 'true' : 'false', onclick: () => { dv.selectingDecks = !dv.selectingDecks; dv.pickedDecks = new Set(); renderDecks(true); } }, dv.selectingDecks ? 'Done' : 'Select'),
        h('button', { type: 'button', class: 'btn ghost', onclick: () => { dv.creatingFolder = true; dv.newFolderParent = null; dv.creating = false; renderDecks(true); const n = $('nfName'); if (n) n.focus(); } }, 'New folder'),
        h('button', { type: 'button', class: 'btn primary', onclick: () => { dv.creating = true; dv.creatingFolder = false; renderDecks(true); const n = $('ndName'); if (n) n.focus(); } }, 'New deck'))),
    helpPanel('decks'),
    dv.creating ? newDeckBox() : null,
    dv.creatingFolder ? newFolderBox() : null,
    ...sections,
    dv.selectingDecks ? deckSelectionBar() : null);
  const nf = $('nfName'); if (dv.creatingFolder && nf && document.activeElement === document.body) nf.focus();
}
function newFolderBox() {
  const dv = S.dv;
  const name = h('input', { type: 'text', id: 'nfName', maxlength: '80', placeholder: 'e.g. Bio 101', autocomplete: 'off' });
  const parent = folderSelect('nfParent', dv.newFolderParent || '', null, 'Top level');
  const share = check('nfShare', 'Share with friends', true);
  const status = h('p', { class: 'status', role: 'status' });
  const close = () => { dv.creatingFolder = false; renderDecks(true); };
  const create = async () => {
    const n = name.value.trim();
    if (!n) { status.className = 'status err'; status.textContent = 'Give the folder a name.'; name.focus(); return; }
    try {
      const pid = parent.value || null;
      await createFolder({ name: n, parentId: pid, shareSelf: $('nfShare').checked });
      if (pid) { S.open.add(pid); for (const f of folderChain(pid)) S.open.add(f.id); saveOpen(); }
      dv.creatingFolder = false;
      toast(`Made the folder ${n}.`);
      renderDecks(true);
    } catch (e) { status.className = 'status err'; status.textContent = dataError(e); }
  };
  name.addEventListener('keydown', (e) => { if (e.key === 'Enter') { e.preventDefault(); create(); } });
  return h('div', { class: 'panel-box' },
    h('h2', { text: 'New folder' }),
    field('Name', name),
    field('Inside', parent),
    share,
    h('p', { class: 'help', text: 'Private always wins: anything inside a private folder stays private, whatever its own setting.' }),
    h('div', { class: 'row' }, h('button', { type: 'button', class: 'btn primary', onclick: create }, 'Create folder'), h('button', { type: 'button', class: 'btn ghost', onclick: close }, 'Cancel')),
    status);
}
function deckSelectionBar() {
  const dv = S.dv;
  const n = dv.pickedDecks.size;
  const move = folderSelect('moveDecksTo', '', null, 'Top level (no folder)');
  move.insertBefore(h('option', { value: '__', text: 'Move to…' }), move.firstChild);
  move.value = '__';
  move.disabled = !n;
  move.addEventListener('change', async () => {
    if (move.value === '__') return;
    const target = move.value || null;
    const ids = [...dv.pickedDecks];
    await moveDecks(ids, target);
    if (target) { for (const f of folderChain(target)) S.open.add(f.id); saveOpen(); }
    toast(`Moved ${plural(ids.length, 'deck')} to ${target ? folderPath(target) : 'the top level'}.`);
    dv.pickedDecks = new Set();
    renderDecks(true);
  });
  return h('div', { class: 'selbar', role: 'region', 'aria-label': 'Selected decks' },
    h('span', { text: n ? `${plural(n, 'deck')} selected` : 'Tick decks to move them' }),
    n ? h('button', { type: 'button', class: 'linkbtn', onclick: () => { dv.pickedDecks = new Set(); renderDecks(true); } }, 'Clear') : null,
    h('span', { class: 'spacer' }),
    move,
    h('p', { class: 'help', style: 'flex-basis:100%', text: "Friends' decks are filed only in your view; your own decks move for everyone." }));
}
function newDeckBox() {
  const name = h('input', { type: 'text', id: 'ndName', maxlength: '80', placeholder: 'e.g. Poems we love', autocomplete: 'off' });
  let kind = 'facts';
  let allowTouched = false;
  const status = h('p', { class: 'status', role: 'status' });
  const edit = check('ndEdit', 'Friends can edit it too', false);
  const share = check('ndShare', 'Share with friends', true, (v) => { edit.hidden = !v; });
  const allowSel = allowSelect('ndAllow', DEFAULT_ALLOW.facts, () => { allowTouched = true; });
  const folderSel = folderSelect('ndFolder', '', null, 'Top level (no folder)');
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
      const id = await createDeck({ name: n, kind, visibility: shared ? 'shared' : 'private', friendsCanEdit: shared && $('ndEdit').checked, allowPct: Number(allowSel.value), folderId: folderSel.value || null });
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
    field('Folder', folderSel),
    h('div', { class: 'stack-sm' }, share, edit),
    h('div', { class: 'field' }, h('label', { class: 'label', for: 'ndAllow', text: 'Allowed mistakes (standard)' }), allowSel),
    h('div', { class: 'row' }, h('button', { type: 'button', class: 'btn primary', onclick: create }, 'Create deck'), h('button', { type: 'button', class: 'btn ghost', onclick: close }, 'Cancel')),
    status);
}
function deckSettings(d) {
  const ref = doc(db, 'decks', d.id);
  const hiddenBy = d.shareSelf && d.folderId ? privateAncestor(d.folderId) : null;
  return h('div', { class: 'settings' },
    check('dsShare', 'Share with friends', d.shareSelf, async (v) => {
      await setDeckShare(d, v);
      const blocker = v && d.folderId ? privateAncestor(d.folderId) : null;
      toast(v ? (blocker ? `Shared, but the folder ${blocker.name} it's in is private, so friends still can't see it.` : 'Friends can now see and study this deck.') : 'This deck is private again.');
      renderDecks(true);
    }),
    hiddenBy ? h('p', { class: 'help', text: `Friends can't see it while the folder ${hiddenBy.name} is private.` }) : null,
    check('dsEdit', 'Friends can edit it too (add, change and delete items)', d.shareSelf && d.friendsCanEdit, (v) => save(updateDoc(ref, { friendsCanEdit: v, updatedAt: serverTimestamp() }),
      v ? 'Friends can now edit this deck.' : 'Only you can edit this deck now.'), !d.shareSelf),
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
      (() => {
        const fs = folderSelect('deckFolder', myFolderFor(d), null, 'Top level (no folder)');
        fs.addEventListener('change', async () => {
          const target = fs.value || null;
          await moveDecks([d.id], target);
          if (target) { for (const f of folderChain(target)) S.open.add(f.id); saveOpen(); }
          toast(target ? `${d.ownerId === myUid() ? `Moved ${d.name} to` : `Filed ${d.name} in`} ${folderPath(target)}.` : `${d.name} is at the top level now.`);
          renderDecks(true);
        });
        return h('div', { class: 'row' }, h('label', { class: 'label', for: 'deckFolder', style: 'margin:0', text: d.ownerId === myUid() ? 'Folder' : 'File in my folder' }), fs);
      })(),
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
      h('div', { class: 'meta' }, ...deckPills(d), h('span', { text: (d.ownerId === myUid() ? 'yours' : 'by ' + ownerLabel(d)) + (myFolderFor(d) ? ' · in ' + folderPath(myFolderFor(d)) : '') })),
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
    : h('div', { style: 'min-width:0' }, h('p', { class: 'item-p', text: r.it.p }), h('p', { class: 'item-a hand', text: answerPlain(r.it.a) }));
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
    h('p', { class: 'help' }, 'One fact per line: ', h('code', { text: 'prompt | answer' }), '. Lists in any order: ', h('code', { text: '{a; b; c}' }), ', at least 2 of them: ', h('code', { text: '{2: a; b; c}' }), '. Other decks in the same paste: ', h('code', { text: 'deck | prompt | answer' }), '. "How this works" above has examples.'),
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
    helpPanel('add'),
    h('div', { class: 'field' }, h('label', { class: 'label', for: 'addDeck', text: 'Add to' }), h('select', { id: 'addDeck' })),
    newDeck, factsBox, poemBox,
    h('div', { class: 'row' }, h('button', { type: 'button', class: 'btn primary big', id: 'addBtn', disabled: true }, 'Add'), h('p', { class: 'status', id: 'addStatus', role: 'status' })));
  $('addDeck').addEventListener('change', (e) => { S.add.deckId = e.target.value; S.add.chosen = true; renderAdd(); if (S.add.deckId === '__new') $('newDeckName').focus(); });
  let t = 0;
  const later = () => { clearTimeout(t); t = setTimeout(updateAdd, 120); $('addStatus').textContent = ''; };
  for (const id of ['pasteBox', 'newDeckName', 'poemTitle', 'poemAuthor', 'poemText']) $(id).addEventListener('input', later);
  let tc = 0;
  const caretMoved = () => { clearTimeout(tc); tc = setTimeout(updateAdd, 120); };
  for (const ev of ['keyup', 'click', 'focus']) $('pasteBox').addEventListener(ev, caretMoved);
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
// caretLine: the line you're still typing. If it isn't complete yet it's "in progress", not skipped.
function parseFacts(text, caretLine) {
  const target = targetName();
  const writable = writableDecks('facts');
  const byName = (n) => writable.find(d => norm(d.name) === norm(n)) || null;
  const rows = [], skipped = [];
  let inProgress = null;
  const seen = new Map();
  text.split(/\r?\n/).forEach((raw, idx) => {
    const line = raw.trim();
    if (!line) return;
    const unfinished = (why) => { if (idx === caretLine) inProgress = { idx, raw }; else skipped.push({ n: idx + 1, why }); };
    let parts = (line.includes('\t') ? line.split('\t') : line.split('|')).map(p => p.trim());
    while (parts.length > 2 && parts[parts.length - 1] === '') parts.pop();
    let deck, p, a, routed = false;
    if (parts.length === 2) { deck = target; [p, a] = parts; }
    else if (parts.length >= 3) { deck = parts[0]; p = parts[1]; a = parts.slice(2).join(' | '); routed = true; }
    else { unfinished('no | between prompt and answer'); return; }
    if (!p) { unfinished('empty prompt'); return; }
    if (!a) { unfinished('empty answer'); return; }
    if (/[{}]/.test(a) && !parseAnswer(a)) { unfinished("a { } list isn't closed or is empty"); return; }
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
  return { rows, skipped, inProgress };
}
function caretLineOf(ta) {
  const pos = typeof ta.selectionStart === 'number' ? ta.selectionStart : ta.value.length;
  return ta.value.slice(0, pos).split('\n').length - 1;
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
  const r = parseFacts(text, caretLineOf($('pasteBox')));
  lastParse = r;
  const touched = new Map();
  for (const row of r.rows) if (!touched.has(row.key)) touched.set(row.key, row);
  const newOnes = [...touched.values()].filter(x => x.isNew);
  const kids = [h('div', { class: 'preview-sum' },
    h('span', null, h('b', { text: r.rows.length.toLocaleString() }), ' ready to add'),
    touched.size > 1 ? h('span', null, 'across ', h('b', { text: String(touched.size) }), ' decks') : null,
    newOnes.length ? h('span', { class: 'pill new', text: newOnes.length === 1 ? `new deck: ${newOnes[0].deck}` : `${newOnes.length} new decks` }) : null,
    r.skipped.length ? h('span', { class: 'pill skip', text: `${r.skipped.length} skipped` }) : null,
    r.inProgress ? h('span', { class: 'pill progress', text: '1 fact in progress' }) : null)];
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
    const keep = lastParse.inProgress ? lastParse.inProgress.raw : '';   // the line you're still typing stays
    const ta = $('pasteBox');
    ta.value = keep;
    if (keep) { ta.focus(); ta.setSelectionRange(keep.length, keep.length); }
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
    helpPanel('people'),
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

// ---------------------------------------------------------------- theme picker (settings)
function currentThemeLabel() {
  const th = S.theme || { id: 'classic' };
  if (th.id === 'custom') return 'Custom · ' + (themeMode(th) === 'dark' ? 'Dark' : 'Light');
  const t = THEME_BY_ID.get(th.id) || THEME_BY_ID.get('classic');
  const mode = t.id === 'classic' && (!th.mode || th.mode === 'auto') ? 'Matches device' : (themeMode(th) === 'dark' ? 'Dark' : 'Light');
  const sets = themeSets(t, themeMode(th));
  const set = sets[Number(th.accent) || 0] || sets[0];
  return `${t.name} · ${mode}${set && set.name !== 'Original' ? ' · ' + set.name : ''}`;
}
function miniPreview(tok, finish) {
  return h('span', { class: 'ts-prev', 'aria-hidden': 'true', style: `background:${tok['--paper']}` },
    h('span', { class: 'ts-card', style: `background:${tok['--card']};box-shadow:0 0 0 1px ${tok['--line']}` },
      h('i', { class: 'ts-margin', style: `background:${tok['--margin']}` }),
      h('i', { class: 'ts-line', style: `background:${tok['--ink']}` }),
      h('i', { class: 'ts-line short', style: `background:${tok['--pen']}` })),
    h('span', { class: 'ts-btn', style: `background:${tok['--accent']}` }),
    finish ? h('span', { class: 'ts-finish', style: `background:${finish}` }) : null);
}
function renderThemePicker() {
  const box = $('themePicker'); if (!box) return;
  const th = S.theme || { id: 'classic' };
  const mode = themeMode(th);
  const isCustom = th.id === 'custom';
  const t = isCustom ? null : (THEME_BY_ID.get(th.id) || THEME_BY_ID.get('classic'));
  const classicAuto = t && t.id === 'classic' && (!th.mode || th.mode === 'auto');

  const setMode = (m) => {
    if (m === (classicAuto ? 'auto' : mode)) return;
    if (isCustom) { saveTheme({ id: 'custom', custom: flipCustom(th.custom, m) }); }
    else saveTheme({ id: t.id, mode: m, accent: m === 'auto' ? 0 : (Number(th.accent) || 0) });
    renderThemePicker();
  };
  const modeOpts = t && t.id === 'classic' ? [['auto', 'Match device'], ['light', 'Light'], ['dark', 'Dark']] : [['light', 'Light'], ['dark', 'Dark']];
  const modeSeg = seg('themeMode', modeOpts, classicAuto ? 'auto' : mode, setMode);

  const swatch = (id, name, finish, tok) => h('button', {
    type: 'button', class: 'theme-swatch', 'aria-pressed': th.id === id ? 'true' : 'false', 'data-key': 'th-' + id,
    onclick: () => {
      if (id === 'custom') { openCustomEditor(); return; }
      closeCustomEditor(false);
      saveTheme({ id, mode: id === 'classic' && classicAuto ? 'auto' : mode, accent: 0 });
      renderThemePicker();
    } }, miniPreview(tok, finish), h('span', { class: 'ts-name', text: name }));
  const savedCustom = (S.themeSaved && S.themeSaved.id === 'custom' && S.themeSaved.custom) || (isCustom && th.custom) || null;
  const customTok = deriveTheme(savedCustom || { bg: mode === 'dark' ? '#1B2430' : '#EEF2F7', accent: mode === 'dark' ? '#F2A65A' : '#B8501E', pen: mode === 'dark' ? '#B9CCFF' : '#264A9E', margin: mode === 'dark' ? '#7DD3C0' : '#2E8B76' });
  const grid = h('div', { class: 'theme-grid' },
    ...THEME_LIST.map(x => swatch(x.id, x.name, x.id === 'classic' ? null : x.finish, x.id === 'classic' && classicAuto ? CLASSIC_TOKENS[mode] : deriveTheme(presetSpec(x, mode, 0)))),
    swatch('custom', 'Custom', null, customTok));

  let accents = null;
  if (t) {
    const sets = themeSets(t, mode);
    accents = h('div', { class: 'stack-sm' }, h('span', { class: 'label', style: 'margin:0', text: 'Accent' }),
      h('div', { class: 'acc-row' }, ...sets.map((set, i) => {
        const tok = deriveTheme(presetSpec(t, mode, i));
        return h('button', { type: 'button', class: 'acc-btn', 'aria-pressed': (Number(th.accent) || 0) === i ? 'true' : 'false', 'data-key': 'acc-' + i,
          onclick: () => { saveTheme({ id: t.id, mode: classicAuto && i === 0 ? 'auto' : mode, accent: i }); renderThemePicker(); } },
          h('span', { class: 'acc-dots', 'aria-hidden': 'true', style: `background:${tok['--paper']}` },
            h('i', { style: `background:${tok['--accent']}` }), h('i', { style: `background:${tok['--pen']}` }), h('i', { style: `background:${tok['--margin']}` })),
          h('span', { text: set.name }));
      })));
  }
  const sum = $('themeSummary'); if (sum) sum.textContent = currentThemeLabel();
  withFocus(box, () => put(box,
    h('div', { class: 'row' }, h('span', { class: 'label', style: 'margin:0', text: 'Mode' }), modeSeg),
    grid,
    accents,
    h('div', { class: 'row' },
      h('button', { type: 'button', class: 'btn ghost', onclick: () => openCustomEditor(true) }, isCustom ? 'Edit custom colors' : 'Customize this theme'))));
}
// Swaps a custom theme between light and dark, keeping its hues.
function flipCustom(c, m) {
  if (!c) return c;
  const [hh, s] = hexHsl(c.bg);
  const bg = m === 'dark' ? hslHex(hh, Math.min(s, 45), 12) : hslHex(hh, Math.min(s, 50), 94);
  return { bg, accent: retune(c.accent, 'accent', m), pen: retune(c.pen || c.accent, 'pen', m), margin: retune(c.margin || '#D8524A', 'margin', m) };
}
let customDraft = null;
// fromCurrent: start from the colors on screen now ("Customize this theme").
function openCustomEditor(fromCurrent) {
  const ed = $('customEditor'); if (!ed) return;
  const th = S.theme || { id: 'classic' };
  let start;
  if (th.id === 'custom' && th.custom) start = { ...th.custom };
  else if (fromCurrent || !(S.themeSaved && S.themeSaved.custom)) {
    const tok = themeTokens(th) || CLASSIC_TOKENS[deviceDark() ? 'dark' : 'light'];
    start = { bg: tok['--paper'], ink: tok['--ink'], accent: tok['--accent'], pen: tok['--pen'], margin: tok['--margin'] };
  } else start = { ...S.themeSaved.custom };
  const tok0 = deriveTheme(start);
  customDraft = { bg: start.bg, ink: start.ink || null, accent: start.accent, pen: start.pen || start.accent, margin: start.margin || tok0['--margin'] };
  const shown = (key) => (customDraft[key] || (key === 'ink' ? deriveTheme(customDraft)['--ink'] : '#888888'));
  const picker = (key, label, help) => {
    const id = 'cu-' + key;
    const inp = h('input', { type: 'color', id, value: shown(key) });
    inp.addEventListener('input', () => { customDraft[key] = inp.value.toUpperCase(); previewCustom(); });
    return h('label', { class: 'color-field', for: id }, inp, h('span', null, h('b', { text: label }), h('small', { text: help })));
  };
  const sugBox = h('div', { class: 'acc-row', id: 'customSuggest' });
  put(ed,
    h('h3', { text: 'Custom theme' }),
    h('p', { class: 'help', text: 'The page changes as you pick. Nothing is saved until you press Save theme.' }),
    h('div', { class: 'color-grid' },
      picker('bg', 'Background', 'The page itself'),
      picker('ink', 'Text', 'Most of the writing'),
      picker('accent', 'Accent', 'Buttons, links, highlights'),
      picker('pen', 'Answer ink', 'How answers are written'),
      picker('margin', 'Margin line', 'The line across each card')),
    h('div', { class: 'stack-sm' }, h('span', { class: 'label', style: 'margin:0', text: 'Suggested accents for this background' }), sugBox),
    h('p', { class: 'help', id: 'customNote' }),
    h('div', { class: 'row' },
      h('button', { type: 'button', class: 'btn ghost', onclick: () => {
        const m = themeMode({ id: 'custom', custom: customDraft }) === 'dark' ? 'light' : 'dark';
        customDraft = { ...flipCustom(customDraft, m), ink: null };
        for (const k of ['bg', 'ink', 'accent', 'pen', 'margin']) $('cu-' + k).value = shown(k);
        previewCustom();
      } }, 'Switch light/dark'),
      h('span', { class: 'spacer' }),
      h('button', { type: 'button', class: 'btn ghost', onclick: () => closeCustomEditor(true) }, 'Cancel'),
      h('button', { type: 'button', class: 'btn primary', onclick: async () => {
        const c = { bg: customDraft.bg, accent: customDraft.accent, pen: customDraft.pen, margin: customDraft.margin };
        if (customDraft.ink) c.ink = customDraft.ink;
        closeCustomEditor(false);
        await saveTheme({ id: 'custom', custom: c });
        toast('Theme saved.');
        renderThemePicker();
      } }, 'Save theme')));
  ed.hidden = false;
  previewCustom();
  ed.scrollIntoView({ block: 'nearest' });
}
function previewCustom() {
  if (!customDraft) return;
  S.themePreview = true;
  const spec = { bg: customDraft.bg, accent: customDraft.accent, pen: customDraft.pen, margin: customDraft.margin };
  if (customDraft.ink) spec.ink = customDraft.ink;
  const tok = applyTheme({ id: 'custom', custom: spec });
  const mode = tok['color-scheme'] === 'dark' ? 'dark' : 'light';
  const sets = accentSets(customDraft.bg, mode, null).slice(0, 4);
  const box = $('customSuggest');
  if (box) put(box, ...sets.map(set => h('button', { type: 'button', class: 'acc-btn', onclick: () => {
    Object.assign(customDraft, { accent: set.accent, pen: set.pen, margin: set.margin });
    for (const k of ['accent', 'pen', 'margin']) $('cu-' + k).value = customDraft[k];
    previewCustom();
  } }, h('span', { class: 'acc-dots', 'aria-hidden': 'true', style: `background:${customDraft.bg}` },
      h('i', { style: `background:${set.accent}` }), h('i', { style: `background:${set.pen}` }), h('i', { style: `background:${set.margin}` })),
    h('span', { text: set.name }))));
  const changed = adjustedColors(spec, tok);
  const n = $('customNote');
  if (n) n.textContent = changed.length ? `Your ${listWords(changed)} ${changed.length > 1 ? 'were' : 'was'} adjusted a little so everything stays easy to read.` : '';
}
function closeCustomEditor(revert) {
  const ed = $('customEditor');
  if (ed) ed.hidden = true;
  customDraft = null;
  if (revert && S.themePreview) { S.themePreview = false; applyTheme(S.themeSaved || { id: 'classic' }); renderThemePicker(); }
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
  const val = (r) => (sortKey === 'streak' ? r.s.streak : sortKey === 'mastered' ? r.s.mastered : r.s.week);
  rows.sort((a, b) => (val(b) - val(a)) || a.name.localeCompare(b.name));
  rows.forEach((r, i) => { r.rank = i && val(rows[i - 1]) === val(r) ? rows[i - 1].rank : i + 1; });   // ties share a rank
  const bigLabel = { week: 'this week', streak: r => (r.s.streak === 1 ? 'day streak' : 'day streak'), mastered: 'mastered' };
  const groupWeek = rows.reduce((a, r) => a + r.s.week, 0);
  const maxStrip = Math.max(1, ...rows.flatMap(r => r.s.strip.map(x => x.n)));
  const row = (r) => {
    const s = r.s;
    const deckList = Object.values(s.decks).filter(x => x && x.name).sort((a, b) => String(a.name).localeCompare(String(b.name)));
    const line = [
      sortKey !== 'streak' ? h('span', null, h('b', { text: String(s.streak) }), ' day streak') : null,
      sortKey !== 'week' ? h('span', null, h('b', { text: String(s.week) }), ' this week') : null,
      s.acc != null ? h('span', null, h('b', { text: pct(s.acc) }), ' right this week') : null,
    ];
    const big = typeof bigLabel[sortKey] === 'function' ? bigLabel[sortKey](r) : bigLabel[sortKey];
    return h('li', { class: 'friend' + (r.me ? ' me' : '') },
      h('div', { class: 'f-rank' }, h('span', { class: 'f-pos mono', text: '#' + r.rank }), h('span', { class: 'f-avatar', 'aria-hidden': 'true', text: initialsOf(r.name) })),
      h('div', { class: 'f-main' },
        h('div', { class: 'f-big' }, h('b', { class: 'mono', text: val(r).toLocaleString() }), h('span', { text: ' ' + big })),
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
      h('div', { class: 'stack-sm', style: 'justify-items:end' }, h('span', { class: 'label', style: 'margin:0', text: 'Rank by' }),
        seg('friendsSort', [['week', 'This week'], ['streak', 'Streak'], ['mastered', 'Mastered']], sortKey, (k) => { S.friendsSort = k; renderFriends(); }))),
    helpPanel('friends'),
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

// ---------------------------------------------------------------- settings
function deviceLabel() {
  const ua = navigator.userAgent || '';
  const os = /iPhone/.test(ua) ? 'iPhone' : /iPad/.test(ua) ? 'iPad' : /Android/.test(ua) ? 'Android' : /Mac OS X/.test(ua) ? 'Mac' : /Windows/.test(ua) ? 'Windows' : /CrOS/.test(ua) ? 'Chromebook' : /Linux/.test(ua) ? 'Linux' : 'unknown device';
  const br = /Edg\//.test(ua) ? 'Edge' : /OPR\//.test(ua) ? 'Opera' : /Firefox\//.test(ua) ? 'Firefox' : /CriOS|Chrome\//.test(ua) ? 'Chrome' : /Safari\//.test(ua) ? 'Safari' : 'a browser';
  return `${br} on ${os}`;
}
const VIEW_NAMES = { study: 'Study', decks: 'Decks', add: 'Add', friends: 'Friends', people: 'People', account: 'Settings' };
const BUG_STATUS = { new: ['New', 'new'], looking: ['Looking into it', 'due'], fixed: ['Fixed', 'mastered'], wontfix: ["Won't fix", 'private'] };
const tsMillis = (v) => (typeof v === 'number' ? v : v && typeof v.toMillis === 'function' ? v.toMillis() : 0);
function dateLabel(ms) {
  if (!ms) return 'just now';
  const d = new Date(ms);
  return d.toLocaleDateString(undefined, { month: 'short', day: 'numeric' }) + (d.getFullYear() !== new Date().getFullYear() ? ', ' + d.getFullYear() : '');
}
function ensureBugsListener() {
  if (S.bugsListening || !dataUnsubs) return;
  S.bugsListening = true;
  dataUnsubs.push(onSnapshot(collection(db, 'bugs'), (snap) => {
    const m = new Map(); snap.forEach(d => m.set(d.id, d.data()));
    S.bugs = m; S.bugsLoaded = true;
    if (S.view === 'account') renderBugList();
  }, (e) => { console.error(e); S.bugsLoaded = true; }));
}
function bugRows() {
  const all = [...S.bugs.entries()].map(([id, b]) => ({ id, ...b, ms: tsMillis(b.createdAt) || Date.now() }));
  const byAge = [...all].sort((a, b) => a.ms - b.ms);
  byAge.forEach((b, i) => { b.num = i + 1; });
  const open = (b) => b.status === 'new' || b.status === 'looking';
  return all.sort((a, b) => (open(b) - open(a)) || b.ms - a.ms);
}
function bugText(b) {
  const who = (S.profiles.get(b.by) || {}).name || 'Someone';
  return [`#${b.num} [${(BUG_STATUS[b.status] || BUG_STATUS.new)[0]}] from ${who}, ${dateLabel(b.ms)}`,
    `Where: ${b.where || '?'} · ${b.device || '?'} · version ${b.version || '?'}`,
    `What went wrong: ${b.text}`, b.expected ? `Expected: ${b.expected}` : null, b.note ? `Note: ${b.note}` : null].filter(Boolean).join('\n');
}
function renderBugList() {
  const box = $('bugList'); if (!box) return;
  const rows = bugRows();
  const openN = rows.filter(b => b.status === 'new' || b.status === 'looking').length;
  const cnt = $('bugCount'); if (cnt) cnt.textContent = rows.length ? `${openN} open · ${rows.length} total` : 'none yet';
  if (S.bugEditing) return;   // keep a note someone is typing
  const fallback = h('textarea', { readonly: true, hidden: true, class: 'data', 'aria-label': 'Open bugs as text' });
  withFocus(box, () => put(box,
    S.isAdmin && openN ? h('div', { class: 'row' },
      h('button', { type: 'button', class: 'btn ghost', onclick: () => copyText(rows.filter(b => b.status === 'new' || b.status === 'looking').map(bugText).join('\n\n'), fallback, `Copied ${plural(openN, 'open bug')}.`) }, 'Copy open bugs')) : null,
    fallback,
    rows.length ? h('ul', { class: 'bugs' }, ...rows.map(b => {
      const [label, cls] = BUG_STATUS[b.status] || BUG_STATUS.new;
      const who = (S.profiles.get(b.by) || {}).name || 'Someone';
      let admin = null;
      if (S.isAdmin) {
        const st = h('select', { id: 'bs-' + b.id, 'aria-label': 'Status', 'data-key': 'bs-' + b.id },
          ...Object.entries(BUG_STATUS).map(([k, [l]]) => h('option', { value: k, text: l })));
        st.value = b.status || 'new';
        const note = h('input', { type: 'text', id: 'bn-' + b.id, maxlength: '2000', placeholder: 'Note for everyone (optional)', value: b.note || '' });
        note.addEventListener('focus', () => { S.bugEditing = b.id; });
        note.addEventListener('blur', () => { setTimeout(() => { if (S.bugEditing === b.id) S.bugEditing = null; }, 200); });
        const saveIt = async () => {
          S.bugEditing = null;
          await save(updateDoc(doc(db, 'bugs', b.id), { status: st.value, note: note.value.trim().slice(0, 2000), updatedAt: serverTimestamp() }), `Bug #${b.num} updated.`);
        };
        st.addEventListener('change', saveIt);
        note.addEventListener('keydown', (e) => { if (e.key === 'Enter') { e.preventDefault(); saveIt(); } });
        admin = h('div', { class: 'row bug-admin' }, st, h('div', { style: 'flex:1 1 12rem;min-width:0' }, note), h('button', { type: 'button', class: 'btn ghost', onclick: saveIt }, 'Save'));
      }
      return h('li', { class: 'bug' },
        h('div', { class: 'row', style: 'gap:.4rem .75rem' }, h('b', { class: 'mono', text: '#' + b.num }), h('span', { class: 'pill ' + cls, text: label }),
          h('span', { class: 'help', text: `${who} · ${dateLabel(b.ms)} · ${b.where || '?'} · ${b.device || ''}` })),
        h('p', { class: 'bug-text', text: b.text }),
        b.expected ? h('p', { class: 'bug-sub' }, h('b', { text: 'Expected: ' }), b.expected) : null,
        b.note ? h('p', { class: 'bug-sub' }, h('b', { text: 'Note: ' }), b.note) : null,
        admin,
        !S.isAdmin && b.by === myUid() && b.status === 'new' ? h('div', null, h('button', { type: 'button', class: 'linkbtn quiet', onclick: () => save(deleteDoc(doc(db, 'bugs', b.id)), 'Report withdrawn.') }, 'Withdraw my report')) : null);
    })) : h('p', { class: 'empty-line', text: S.bugsLoaded ? 'No bugs reported yet.' : 'Loading…' })));
}
function bugForm() {
  const what = h('textarea', { id: 'bugWhat', rows: '4', maxlength: '4000', placeholder: 'What happened? What were you doing just before?' });
  const expected = h('textarea', { id: 'bugExpected', rows: '2', maxlength: '4000', placeholder: 'What did you expect to happen? (optional)' });
  const status = h('p', { class: 'status', role: 'status' });
  const info = h('p', { class: 'help', id: 'bugInfo' });
  const where = () => VIEW_NAMES[S.lastView] || 'Study';
  const refreshInfo = () => { info.textContent = `Sent along automatically: ${where()} page · ${deviceLabel()} · version ${APP_VERSION}.`; };
  refreshInfo();
  const send = async () => {
    const t = what.value.trim();
    if (!t) { status.className = 'status err'; status.textContent = 'Describe what went wrong first.'; what.focus(); return; }
    const data = { by: myUid(), text: t.slice(0, 4000), where: where(), device: deviceLabel(), version: APP_VERSION, status: 'new', createdAt: serverTimestamp() };
    const ex = expected.value.trim(); if (ex) data.expected = ex.slice(0, 4000);
    try {
      await setDoc(doc(collection(db, 'bugs')), data);
      what.value = ''; expected.value = '';
      status.className = 'status ok'; status.textContent = 'Thanks! Your report is in the list below.';
      const dd = $('bugListDD'); if (dd) dd.open = true;
    } catch (e) { status.className = 'status err'; status.textContent = dataError(e); }
  };
  return h('form', { class: 'stack-sm', novalidate: true, onsubmit: (e) => { e.preventDefault(); send(); } },
    field('What went wrong', what), field('What you expected', expected), info,
    h('div', { class: 'row' }, h('button', { type: 'submit', class: 'btn primary' }, 'Send report')), status);
}
function downloadJson(filename, obj) {
  const replacer = (k, v) => (v && typeof v === 'object' && typeof v.toMillis === 'function' ? v.toMillis() : v);
  const blob = new Blob([JSON.stringify(obj, replacer, 2)], { type: 'application/json' });
  const a = h('a', { href: URL.createObjectURL(blob), download: filename });
  document.body.append(a); a.click();
  setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 2000);
}
function myBackup() {
  const strip = (d) => ({ name: d.name, kind: d.kind, shareSelf: d.shareSelf, visibility: d.visibility, friendsCanEdit: d.friendsCanEdit, allowPct: d.allowPct, folderId: d.folderId, items: d.items });
  const own = [...S.decks.values()].filter(d => d.ownerId === myUid());
  return {
    app: 'Recall by Hand', version: APP_VERSION, exportedAt: new Date().toISOString(),
    you: { id: myUid(), name: myName(), email: S.fbUser && S.fbUser.email },
    decks: Object.fromEntries(own.map(d => [d.id, strip(d)])),
    folders: Object.fromEntries(foldersOf(myUid()).map(f => [f.id, { name: f.name, parentId: f.parentId, shareSelf: f.shareSelf }])),
    filedFriendDecks: S.placements,
    progress: S.progress, stats: S.myStats,
    settings: { theme: S.themeSaved, studyMode: S.study.mode },
  };
}
async function siteBackup() {
  const out = { app: 'Recall by Hand', version: APP_VERSION, exportedAt: new Date().toISOString(), collections: {} };
  for (const c of ['meta', 'users', 'profiles', 'decks', 'folders', 'placements', 'progress', 'stats', 'bugs', 'requests']) {
    const snap = await getDocs(collection(db, c));
    out.collections[c] = {};
    snap.forEach(d => { out.collections[c][d.id] = d.data(); });
  }
  return out;
}
function renderAccount() {
  ensureBugsListener();
  if (mounted.account) { renderBugList(); setSeg('setMode', S.study.mode); return; }
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
  const stamp = () => new Date().toISOString().slice(0, 10);
  put($('view-account'),
    h('div', { class: 'row', style: 'align-items:flex-start' },
      h('div', { style: 'flex:1 1 18rem;min-width:0' }, h('h1', { text: 'Settings' }), h('p', { class: 'lede', text: (S.fbUser.email || '') + (S.isAdmin ? ' · admin' : '') }))),
    h('form', { class: 'panel-box', novalidate: true, onsubmit: (e) => { e.preventDefault(); saveName(); } },
      field('Your name', name), h('div', { class: 'row' }, h('button', { type: 'submit', class: 'btn primary' }, 'Save name')), status),
    h('details', { class: 'dd', id: 'themeDD' },
      h('summary', null, h('span', { class: 'dd-title', text: 'Theme' }), h('span', { class: 'dd-val', id: 'themeSummary', text: currentThemeLabel() })),
      h('div', { class: 'dd-body' },
        h('p', { class: 'help', text: 'Pick a color, then light or dark and an accent. Your theme follows you to any device you sign in on.' }),
        h('div', { id: 'customEditor', class: 'custom-editor', hidden: true }),
        h('div', { id: 'themePicker', class: 'stack' }))),
    h('div', { class: 'panel-box' },
      h('h2', { text: 'Answering' }),
      h('div', { class: 'row' }, h('span', { class: 'label', style: 'margin:0', text: 'How you answer' }),
        seg('setMode', [['type', 'Type it'], ['paper', 'On paper']], S.study.mode, (k) => { setStudyMode(k); setSeg('setMode', k); })),
      h('p', { class: 'help', text: 'This is where every set starts. You can still switch on the Study page; that choice is saved here too.' })),
    h('details', { class: 'dd', id: 'bugDD' },
      h('summary', null, h('span', { class: 'dd-title', text: 'Report a bug' })),
      h('div', { class: 'dd-body' }, bugForm(),
        h('details', { class: 'dd inner', id: 'bugListDD' },
          h('summary', null, h('span', { class: 'dd-title', text: 'Reported bugs' }), h('span', { class: 'dd-val', id: 'bugCount' })),
          h('div', { class: 'dd-body', id: 'bugList' })))),
    h('div', { class: 'panel-box' },
      h('h2', { text: 'Backup' }),
      h('p', { class: 'help', text: 'Saves a file with your decks, folders, progress and settings. Keep it somewhere safe in case anything ever goes wrong.' }),
      h('div', { class: 'row' },
        h('button', { type: 'button', class: 'btn ghost', onclick: () => { downloadJson(`recall-backup-${stamp()}.json`, myBackup()); toast('Backup downloaded.'); } }, 'Download my backup'),
        S.isAdmin ? h('button', { type: 'button', class: 'btn ghost', onclick: async () => {
          try { toast('Gathering everything…'); downloadJson(`recall-everything-${stamp()}.json`, await siteBackup()); toast('Backup of the whole site downloaded.'); } catch (e) { toast(dataError(e)); }
        } }, 'Download everything (admin)') : null)),
    h('details', { class: 'dd', id: 'helpDD' },
      h('summary', null, h('span', { class: 'dd-title', text: 'Help' }), h('span', { class: 'dd-val', text: 'How everything works' })),
      h('div', { class: 'dd-body stack-sm' }, ...['add', 'decks', 'study', 'friends', 'settings', ...(S.isAdmin ? ['people'] : [])].map(id => helpPanel(id, true)))),
    h('div', { class: 'panel-box' },
      h('h2', { text: 'Password' }),
      h('p', { class: 'help', text: 'We\'ll email you a link to set a new password.' }),
      h('div', { class: 'row' }, h('button', { type: 'button', class: 'btn ghost', onclick: async () => {
        try { await sendPasswordResetEmail(auth, S.fbUser.email); toast('Check your email for a link to set a new password.'); } catch (e) { toast(authError(e)); }
      } }, 'Email me a reset link'))),
    h('div', { class: 'row' }, h('button', { type: 'button', class: 'btn ghost', onclick: () => signOut(auth) }, 'Sign out'),
      h('span', { class: 'help', text: 'Recall by Hand ' + APP_VERSION })));
  renderThemePicker();
  renderBugList();
}

// ---------------------------------------------------------------- help
// Each tab has a "How this works" panel; Settings → Help collects all of them.
const HELP_TITLES = { add: 'Adding facts and poems', decks: 'Decks and folders', study: 'Studying: the exact math', friends: 'The Friends tab', settings: 'Settings, themes and bug reports', people: 'People (admin only)' };
const P = (...kids) => h('p', null, ...kids);
const C = (t) => h('code', { text: t });
const B = (t) => h('b', { text: t });
const UL = (...items) => h('ul', null, ...items.map(i => h('li', null, ...(Array.isArray(i) ? i : [i]))));
const EX = (t) => h('pre', { class: 'help-ex', text: t });
const H4 = (t) => h('h4', { text: t });
function helpContent(id) {
  if (id === 'add') return [
    H4('Facts'),
    P('One fact per line, prompt first, then a ', C('|'), ', then the answer:'),
    EX('Capital of Australia | Canberra\nNumber of bones in the adult human body | 206'),
    P('To send some lines to other decks in the same paste, start those lines with the deck name. Decks you don\'t have yet are made for you as private decks.'),
    EX('Chemistry | Chemical symbol for potassium | K'),
    P('From a spreadsheet: copy two columns (prompt, answer) or three (deck, prompt, answer) and paste. Tabs work the same as ', C('|'), '.'),
    P('The preview shows exactly what will be added. Lines are skipped (with the reason) when they have no ', C('|'), ', an empty side, a prompt the deck already has, or a list that isn\'t closed. The line your cursor is on shows as "in progress" instead, and it stays in the box after you press Add so you can finish it.'),
    H4('Lists in any order'),
    P('Put items in curly braces, separated by semicolons. Only the part inside the braces can be in any order.'),
    EX('Three reasons apples are healthy | {fiber; vitamin C; antioxidants}\nThe three branches of government | The branches are {legislative; executive; judicial}'),
    P('When you answer, separate the items however you like: commas, line breaks, "and", or nothing. Every item counts the same: missing one of three is 33% off, and the "Missing:" line names it. Semicolons separate items, so one item can still contain a comma.'),
    H4('Lists with a minimum'),
    P('Put a number and a colon right after the opening brace to ask for at least that many:'),
    EX('Name three healthy things about apples | {3: fiber; vitamin C; antioxidants; potassium; water}'),
    P('Naming 4 or all 5 costs nothing. Naming only 2 counts the missing one as an error. Once you\'ve reached the minimum, a wrong extra guess costs nothing either; it\'s just crossed out. A large number like ', C('{1945: …}'), ' is treated as text, not a minimum.'),
    H4('Lists inside lists'),
    EX('Two fruits and their benefits | {Apples: {fiber; vitamin C}; Oranges: {vitamin C; potassium}}'),
    P('Order is free at every level, but each sub-item has to be under its own parent: "fiber" written under Oranges doesn\'t count. Each fruit is half the answer, and within a fruit the name and each benefit share that half equally, so missing one of Apples\' two benefits costs about 17%. The "Missing:" line shows where the gap is, like "Apples → vitamin C". Minimums work at any level.'),
    H4('Poems'),
    P('Switch Add to Poems, give the poem a title (the poet is optional) and paste the text. Line breaks and stanza gaps are kept; keep a blank line between stanzas. Poems are added one at a time and practiced by writing out the whole thing.'),
    H4('Limits'),
    P('A prompt or answer can be up to 2,000 characters, and a poem up to 20,000. One deck holds roughly a megabyte of text, which is several thousand facts; the site warns you before a deck fills up.'),
  ];
  if (id === 'decks') return [
    H4('Folders'),
    P('Press New folder to make one, at the top level or inside another folder, as deep as you like. Press a folder\'s name to open or close it. Press Options next to a folder to share it, make a folder inside it, rename it, move it into another folder, or delete it. Deleting a folder never deletes decks: everything inside moves up one level.'),
    H4('Moving decks'),
    P('On a deck\'s page, pick a folder next to "Folder". To move several at once, press Select, tick the decks, then choose "Move to…".'),
    H4('Sharing'),
    P('Every deck and folder has a "Share with friends" switch. Private always wins: friends see a deck only if the deck and every folder above it are shared. Turning a folder private hides everything in it; turning it back on brings back whatever was shared before.'),
    P(B('Friends can edit it too'), ' (on a shared deck) lets friends add, change and delete items. Only the owner can rename it, delete it, change its sharing or its allowed mistakes.'),
    H4("Friends' decks"),
    P('Shared decks appear under each friend\'s name, inside their shared folders. You can file a friend\'s deck into one of your own folders from its page or with Select; that only changes your view, and it moves up to My decks. Choosing "Top level" puts it back under your friend.'),
    S.isAdmin ? P('As the admin you see every deck and folder, private ones included, grouped by owner, and you can manage them.') : null,
    H4('Inside a deck'),
    P('Items are listed with the ones most likely to come up for you first. Each has Edit and Delete; a deleted item can be brought back with Undo for a few seconds. Select lets you delete or move several items to another deck at once, and your progress moves with them. Copy puts the whole deck on your clipboard as text.'),
    P('Pills on each item: ', B('new'), ' (never written), ', B('missed last time'), ', ', B('due'), ', or ', B('mastered'), '. See Studying for what those mean.'),
  ].filter(Boolean);
  if (id === 'study') return [
    H4('Which items come up'),
    P('Every item gets a weight:'),
    h('div', { class: 'formula', text: 'weight = (days since you last wrote it + 1) ÷ (times you got it right + 1)' }),
    UL('Never written: counts as at least 30 days (more if it was added longer ago).',
      'Missed last time: counts as at least 14 days.',
      'Only right answers raise the bottom number; misses don\'t.'),
    P('The draw picks without repeats. Each item gets a random key based on its weight (the weighted method by Efraimidis and Spirakis: key = r^(1/weight) for a random r between 0 and 1) and the highest keys are drawn. An item with twice the weight is much more likely to come up, but nothing is guaranteed.'),
    H4('Due, mastered, streak'),
    UL([B('Due'), ': never written, missed last time, or it\'s been at least its spacing since you last wrote it. The spacing is 1 day after your first right answer, then 2, 4, 8, 16, 32, up to 60 days.'],
      [B('Mastered'), ': right at least 3 times, including the last time.'],
      [B('Streak'), ': days in a row with at least one recorded answer. Today counts as soon as you answer something.']),
    H4('Missed items'),
    P('Anything you miss comes back once at the end of the same set. That retry is practice only and isn\'t recorded. At the end of a set you can practice all your misses again.'),
    H4('How typed answers are checked'),
    UL('Capitals, accents and punctuation never count against you. Capital mistakes are marked with a double underline: one color for "should be uppercase", another for "should be lowercase".',
      'Answers of 1–2 words are checked letter by letter: % off = letters wrong ÷ letters in the answer. Adding, removing or changing a letter, or swapping two neighbors, each count as one.',
      'Longer answers and poems are checked word by word, in order: % off = (the larger of missing words and extra words, plus ½ for each typo) ÷ words in the answer.',
      'A word counts as a typo (half credit) when it\'s 4 letters or longer and off by at most 1 letter per 5.',
      'Lists: every item counts the same, and an item\'s own words and each of its sub-items share its part. In list answers, extra words don\'t count against you, and words like "and" between items are ignored. Lists with a minimum count your best items up to the minimum.'),
    P('It counts as right when % off is at most the allowed mistakes: the deck\'s standard, or the number you pick for the set. You can always overrule it with "Count it as right" or "Count it as missed".'),
    H4('On paper'),
    P('Facts: write it, reveal it, then mark Got it or Missed it. Poems: count the lines you missed; % off = lines missed ÷ lines in the poem.'),
    H4('Shortcuts'),
    P('Space reveals, Enter checks or goes on, S skips, H gives a poem hint, U undoes the last answer. On paper, ← or 1 is Missed it and → or 2 is Got it. When typing a poem, Ctrl/⌘ + Enter checks it.'),
    H4('Weight explorer'),
    h('div', { class: 'explorer', id: 'explorer' }),
  ];
  if (id === 'friends') return [
    H4('Rank by'),
    UL([B('This week'), ': answers recorded in the last 7 days, today included.'], [B('Streak'), ': days in a row with at least one answer.'], [B('Mastered'), ': items mastered (right at least 3 times, including the last).']),
    P('The big number on each card is the one you\'re ranking by. People with the same number share a rank.'),
    H4('On each card'),
    UL('Streak, answers this week, and % right: the share of this week\'s answers that counted as right.',
      'The strip shows the last 14 days, oldest on the left; darker squares mean more answers that day.',
      'Mastered "x of y": items mastered out of everything that person can study (their own decks and friends\' shared decks).',
      '"Shared decks": that person\'s progress in each shared deck they\'ve studied.'),
    H4('Updates and privacy'),
    P('Numbers update live, a few seconds after someone answers; Undo takes an answer back out. Totals include private decks, but private decks are never named. Nobody can see what you typed or which items you missed.'),
  ];
  if (id === 'settings') return [
    H4('Theme'),
    P('Open Theme, pick a color, then choose Light or Dark and an accent set. Classic can also match your device\'s setting. "Customize this theme" copies it into a custom theme where you choose the background, text, accent, answer ink and margin line yourself. If a color would be hard to read, it\'s adjusted a little and a note tells you which. Your theme is saved to your account.'),
    H4('Answering'),
    P('Sets start as "Type it" unless you pick "On paper" here or on the Study page. The choice is saved to your account.'),
    H4('Bug reports'),
    P('Describe what went wrong; the page you were on, your device and the version number are added for you. Everyone can see all reports so nobody files the same one twice. Statuses: New, Looking into it, Fixed, Won\'t fix. You can withdraw your own report while it\'s still New.'),
    S.isAdmin ? P('As the admin you can change a report\'s status, add a note everyone sees, and copy all open reports as text to paste into a chat.') : null,
    H4('Backup and updates'),
    P('"Download my backup" saves a file with your decks, folders, progress and settings. When a new version of the site is out, a bar at the top offers to reload.'),
  ].filter(Boolean);
  if (id === 'people') return [
    P('Add a person with their name and email. "Email them a link" sends a message to set their own password (it may land in spam); "I\'ll set a temporary one" lets you hand them a password.'),
    P('Someone who signs in without an account can press Request access; requests show up here to approve or dismiss.'),
    P('"Account on" turns sign-in on or off; their decks and progress are kept. Rename changes the name everyone sees, everywhere. "Send password reset" emails them a link.'),
  ];
  return [];
}
function helpPanel(id, inSettings) {
  const d = h('details', { class: 'help-panel', 'data-help': id },
    h('summary', null, inSettings ? HELP_TITLES[id] : 'How this works'),
    h('div', { class: 'help-body' }, ...helpContent(id)));
  if (id === 'study') d.addEventListener('toggle', () => { if (d.open) renderExplorer(d.querySelector('.explorer')); });
  return d;
}

// ----- weight explorer: what each item's weight is for you right now, and its chance of coming up
function weightParts(it, pr, now) {
  const n = pr ? Math.max(0, Number(pr.n) || 0) : 0;
  const t = pr ? Number(pr.t) || 0 : 0;
  let days, why = '';
  if (!t) { const since = (now - (Number(it.c) || now)) / DAY; days = Math.max(NEW_DAYS, since); why = since < NEW_DAYS ? 'new: counts as 30' : 'new'; }
  else {
    const since = Math.max(0, (now - t) / DAY);
    days = lastMissed(pr) ? Math.max(since, MISS_DAYS) : since;
    if (lastMissed(pr) && since < MISS_DAYS) why = 'missed: counts as 14';
  }
  return { n, days, why, weight: (days + 1) / (n + 1), t };
}
function renderExplorer(box) {
  if (!box) return;
  const decks = [...S.decks.values()].filter(d => category(d) !== 'other' && itemsOf(d).length).sort((a, b) => a.name.localeCompare(b.name));
  if (!decks.length) { put(box, h('p', { class: 'help', text: 'Once you have a deck with something in it, you can see its weights here.' })); return; }
  const sel = h('select', { id: 'exDeck', 'aria-label': 'Deck' }, ...decks.map(d => h('option', { value: d.id, text: d.name + (d.ownerId !== myUid() ? ` (${ownerLabel(d)})` : '') })));
  if (S.exDeck && decks.some(d => d.id === S.exDeck)) sel.value = S.exDeck;
  const size = h('input', { type: 'number', id: 'exSize', min: '1', max: '200', inputmode: 'numeric' });
  const out = h('div', { class: 'stack-sm' });
  const run = () => {
    const d = S.decks.get(sel.value); if (!d) return;
    S.exDeck = d.id;
    const items = itemsOf(d).map(([iid, it]) => ({ deckId: d.id, itemId: iid, deck: d, it }));
    const k = clampInt(size.value, 1, Math.min(200, items.length), Math.min(items.length, S.study.count[d.kind] || 10));
    size.value = k;
    const now = Date.now();
    const rows = items.map(x => ({ x, ...weightParts(x.it, progOf(d.id, x.itemId), now) }));
    const hits = new Map(rows.map(r => [r.x.itemId, 0]));
    const RUNS = 2000;
    for (let i = 0; i < RUNS; i++) for (const p of draw(items, k)) hits.set(p.itemId, hits.get(p.itemId) + 1);
    rows.sort((a, b) => b.weight - a.weight);
    const top = rows[0];
    const fmt = (v) => (Math.round(v * 100) / 100).toLocaleString();
    put(out,
      h('p', { class: 'help' }, 'Top item worked out: (', B(fmt(top.days)), ' days + 1) ÷ (', B(String(top.n)), ' right + 1) = ', B(fmt(top.weight)),
        `. Chances are for drawing ${k} from this deck alone, estimated by running the draw ${RUNS.toLocaleString()} times; in a bigger pool each item's chance is smaller.`),
      h('div', { class: 'tablewrap' }, h('table', { class: 'pv' },
        h('thead', null, h('tr', null, ...['Item', 'Last written', 'Right', 'Last time', 'Days used', 'Weight', 'Chance'].map(t => h('th', { text: t })))),
        h('tbody', null, ...rows.slice(0, 150).map(r => {
          const pr = progOf(d.id, r.x.itemId);
          return h('tr', null,
            h('td', { text: d.kind === 'poems' ? r.x.it.title : r.x.it.p }),
            h('td', { class: 'mono', text: r.t ? ago(r.t, now) : 'never' }),
            h('td', { class: 'mono', text: String(r.n) }),
            h('td', { text: !pr || !Number(pr.t) ? '—' : lastMissed(pr) ? 'missed' : 'right' }),
            h('td', { class: 'mono', text: fmt(r.days) + (r.why ? ` (${r.why})` : '') }),
            h('td', { class: 'mono', text: fmt(r.weight) }),
            h('td', { class: 'mono', text: Math.round(hits.get(r.x.itemId) / RUNS * 100) + '%' }));
        })))),
      rows.length > 150 ? h('p', { class: 'help', text: `Showing the 150 heaviest of ${rows.length}.` }) : null);
  };
  sel.addEventListener('change', run);
  size.addEventListener('change', run);
  put(box,
    h('p', { class: 'help', text: 'Pick a deck to see every item\'s weight for you right now and how likely it is to come up.' }),
    h('div', { class: 'row' }, h('label', { class: 'label', for: 'exDeck', style: 'margin:0', text: 'Deck' }), sel,
      h('label', { class: 'label', for: 'exSize', style: 'margin:0', text: 'Set of' }), size),
    out);
  run();
}

// ---------------------------------------------------------------- versions
// index.html and app.js carry the same version number. If they disagree, the browser mixed a cached
// old file with a new one: load a fresh copy of the page once, and if that doesn't help, explain.
function freshUrl(v) { return location.pathname + '?v=' + encodeURIComponent(v) + '-' + Date.now().toString(36) + location.hash; }
function pageVersionOk() {
  const meta = document.querySelector('meta[name="app-version"]');
  const pageV = meta ? meta.content : 'old';
  if (pageV === APP_VERSION) return true;
  let tried = false;
  try { tried = sessionStorage.getItem('rbh.vfix') === APP_VERSION; sessionStorage.setItem('rbh.vfix', APP_VERSION); } catch (e) { tried = true; }
  if (!tried) { location.replace(freshUrl(APP_VERSION)); return false; }
  document.body.textContent = '';
  const box = document.createElement('div');
  box.style.cssText = 'max-width:30rem;margin:4rem auto;padding:0 1rem;font:16px/1.5 system-ui,sans-serif';
  box.textContent = 'Recall by Hand is updating. Wait a minute, then reload this page.';
  document.body.append(box);
  return false;
}
let updateShown = false;
function showUpdateBar(v) {
  if (updateShown) return;
  updateShown = true;
  let bar = $('updateBar');
  if (!bar) { bar = h('div', { id: 'updateBar', class: 'update-bar', role: 'status' }); document.body.prepend(bar); }
  put(bar, h('span', { text: 'A new version of Recall by Hand is ready.' }),
    h('button', { type: 'button', class: 'btn primary', onclick: () => location.replace(freshUrl(v)) }, 'Reload'));
  bar.hidden = false;
}
async function checkForUpdate() {
  try {
    const r = await fetch('version.json?t=' + Date.now(), { cache: 'no-store' });
    if (!r.ok) return;
    const v = String((await r.json()).version || '');
    if (v && v !== APP_VERSION) showUpdateBar(v);
  } catch (e) { /* offline or no version.json yet */ }
}

// ---------------------------------------------------------------- events
function wireEvents() {
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
}

if (pageVersionOk()) {
  wireEvents();
  try { S.themeSaved = JSON.parse(localStorage.getItem('rbh.theme') || 'null'); } catch (e) { S.themeSaved = null; }
  applyTheme(S.themeSaved || { id: 'classic' });
  boot();
  setTimeout(checkForUpdate, 4000);
  setInterval(checkForUpdate, 15 * 60 * 1000);
  document.addEventListener('visibilitychange', () => { if (document.visibilityState === 'visible') checkForUpdate(); });
}
