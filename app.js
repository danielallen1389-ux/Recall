// Recall by Hand: draw a weighted set of facts or poems to write out by hand.
import { firebaseConfig } from './firebase-config.js';
import { initializeApp, getApps } from 'https://www.gstatic.com/firebasejs/12.19.0/firebase-app.js';
import {
  getAuth, onAuthStateChanged, signInWithEmailAndPassword, createUserWithEmailAndPassword,
  signOut, sendPasswordResetEmail, setPersistence, inMemoryPersistence
} from 'https://www.gstatic.com/firebasejs/12.19.0/firebase-auth.js';
import {
  initializeFirestore, persistentLocalCache, persistentMultipleTabManager,
  doc, collection, query, where, onSnapshot, setDoc, updateDoc, deleteDoc, deleteField, serverTimestamp
} from 'https://www.gstatic.com/firebasejs/12.19.0/firebase-firestore.js';

const DAY = 864e5;
const NEW_DAYS = 30;            // never-written items count as at least this many days overdue
const MAX_DECK_BYTES = 900000;  // Firestore documents top out at 1 MiB
const MAX_LIST = 300;
const MAX_FIELD = 2000;
const MAX_POEM = 20000;
const $ = (id) => document.getElementById(id);
const enc = new TextEncoder();

let app, auth, db;

// ---------------------------------------------------------------- state
const S = {
  phase: 'loading',             // loading | config | setup | signin | inactive | app
  metaLoaded: false, authLoaded: false,
  adminUid: null, adminName: '',
  fbUser: null, me: null, meLoaded: false, myRequest: null,
  isAdmin: false, listenersFor: null, settingUp: false, authShown: null,
  decks: new Map(), deckParts: {}, decksLoaded: false, pendingDecks: new Map(),
  progress: {}, people: new Map(), requests: new Map(),
  view: 'study',
  study: { kind: 'facts', sel: { facts: new Set(), poems: new Set() }, count: { facts: 10, poems: 1 } },
  session: null,
  dv: { open: null, q: '', editing: null, confirmItem: false, renaming: false, confirmDeck: false, creating: false, expanded: new Set() },
  add: { kind: 'facts', deckId: null, chosen: false },
  pp: { renaming: null },
};
let userUnsubs = [];
let dataUnsubs = null;

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
function spanDays(days) {
  if (days < 1) return 'under a day';
  const d = Math.floor(days);
  if (d < 60) return plural(d, 'day');
  if (d < 730) return plural(Math.round(d / 30.4), 'month');
  return (d / 365).toFixed(1) + ' years';
}
function cleanPoem(text) {
  return String(text || '').replace(/\r\n?/g, '\n').split('\n').map(l => l.replace(/\s+$/, '')).join('\n').replace(/\n{3,}/g, '\n\n').trim();
}
const poemLines = (t) => String(t || '').split('\n').filter(l => l.trim()).length;
const poemFirstLine = (t) => (String(t || '').split('\n').find(l => l.trim()) || '').trim();

let toastTimer = 0;
function toast(msg) {
  const t = $('toast');
  t.textContent = msg; t.hidden = false;
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => { t.hidden = true; }, 4500);
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
async function save(p, okMsg) {
  try { await p; if (okMsg) toast(okMsg); return true; }
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

// ---------------------------------------------------------------- prefs (per person, per device)
function loadPrefs() {
  try {
    const p = JSON.parse(localStorage.getItem('rbh.prefs.' + myUid()) || '{}');
    if (p.kind === 'facts' || p.kind === 'poems') S.study.kind = p.kind;
    if (p.count) { S.study.count.facts = clampInt(p.count.facts, 1, 200, 10); S.study.count.poems = clampInt(p.count.poems, 1, 50, 1); }
    if (p.sel) for (const k of ['facts', 'poems']) if (Array.isArray(p.sel[k])) S.study.sel[k] = new Set(p.sel[k].filter(x => typeof x === 'string'));
  } catch (e) { /* storage unavailable */ }
}
function savePrefs() {
  try {
    localStorage.setItem('rbh.prefs.' + myUid(), JSON.stringify({
      kind: S.study.kind, count: S.study.count,
      sel: { facts: [...S.study.sel.facts], poems: [...S.study.sel.poems] },
    }));
  } catch (e) { /* ignore */ }
}

// ---------------------------------------------------------------- decks and items
function normDeck(id, v) {
  return {
    id,
    name: String(v.name || 'Untitled deck'),
    kind: v.kind === 'poems' ? 'poems' : 'facts',
    scope: v.scope === 'universal' ? 'universal' : 'personal',
    visibility: v.visibility === 'shared' ? 'shared' : 'private',
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
  if (d.scope === 'universal') return 'universal';
  if (d.ownerId === myUid()) return 'mine';
  if (d.visibility === 'shared') return 'shared';
  return 'other';
}
const canEditUniversal = () => S.isAdmin || !!(S.me && S.me.canEditUniversal === true);
function canWrite(d) {
  if (d.scope === 'universal') return canEditUniversal();
  return S.isAdmin || d.ownerId === myUid();
}
function ownerLabel(d) {
  if (d.ownerId === myUid()) return 'you';
  const p = S.people.get(d.ownerId);
  return (p && p.name) || d.ownerName || 'someone';
}
function sortDecks(list) { return list.sort((a, b) => a.name.localeCompare(b.name, undefined, { sensitivity: 'base' })); }
function studyDecks(kind) {
  return sortDecks([...S.decks.values()].filter(d => d.kind === kind && category(d) !== 'other'));
}
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
function weightOf(it, pr, now) {
  const n = pr ? Math.max(0, Number(pr.n) || 0) : 0;
  const t = pr ? Number(pr.t) || 0 : 0;
  const days = t ? Math.max(0, (now - t) / DAY) : Math.max(NEW_DAYS, (now - (Number(it.c) || now)) / DAY);
  return (days + 1) / (n + 1);
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

async function createDeck({ name, kind, scope, visibility, items }) {
  const ref = doc(collection(db, 'decks'));
  await setDoc(ref, {
    name: name.slice(0, 80), kind, scope,
    visibility: scope === 'universal' ? 'shared' : (visibility === 'shared' ? 'shared' : 'private'),
    ownerId: myUid(), ownerName: myName().slice(0, 60),
    items: items || {}, createdAt: serverTimestamp(), updatedAt: serverTimestamp(),
  });
  // Show the new deck right away, even before the live listener catches up.
  if (!S.decks.has(ref.id)) {
    const d = normDeck(ref.id, { name, kind, scope, visibility: scope === 'universal' ? 'shared' : visibility, ownerId: myUid(), ownerName: myName(), items: items || {} });
    S.pendingDecks.set(ref.id, d);
    S.decks.set(ref.id, d);
  }
  return ref.id;
}
function addItems(deckId, items) {
  const patch = { updatedAt: serverTimestamp() };
  for (const [id, it] of Object.entries(items)) patch['items.' + id] = it;
  return updateDoc(doc(db, 'decks', deckId), patch);
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
  const expected = S.isAdmin ? 1 : 3;
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
    dataUnsubs.push(onSnapshot(query(decks, where('scope', '==', 'universal')), part('uni'), onErr));
    dataUnsubs.push(onSnapshot(query(decks, where('ownerId', '==', uid)), part('mine'), onErr));
    dataUnsubs.push(onSnapshot(query(decks, where('visibility', '==', 'shared')), part('shared'), onErr));
  }
  dataUnsubs.push(onSnapshot(doc(db, 'progress', uid), (s) => {
    S.progress = (s.exists() && s.data().p) || {};
    refresh();
  }, onErr));
  if (S.isAdmin) {
    dataUnsubs.push(onSnapshot(collection(db, 'users'), (snap) => {
      const m = new Map(); snap.forEach(d => m.set(d.id, d.data())); S.people = m; refresh();
    }, onErr));
    dataUnsubs.push(onSnapshot(collection(db, 'requests'), (snap) => {
      const m = new Map(); snap.forEach(d => m.set(d.id, d.data())); S.requests = m; refresh();
    }, onErr));
  }
}
function stopData() {
  if (dataUnsubs) dataUnsubs.forEach(u => u());
  dataUnsubs = null;
  S.decks = new Map(); S.deckParts = {}; S.decksLoaded = false; S.pendingDecks = new Map(); S.progress = {}; S.people = new Map(); S.requests = new Map();
}
function teardown() {
  userUnsubs.forEach(u => u()); userUnsubs = [];
  stopData();
  S.listenersFor = null; S.me = null; S.meLoaded = false; S.myRequest = null; S.isAdmin = false;
  S.session = null; S.view = 'study'; S.authShown = null;
  S.dv = { open: null, q: '', editing: null, confirmItem: false, renaming: false, confirmDeck: false, creating: false, expanded: new Set() };
  S.add = { kind: 'facts', deckId: null, chosen: false };
  S.pp = { renaming: null };
  S.study = { kind: 'facts', sel: { facts: new Set(), poems: new Set() }, count: { facts: 10, poems: 1 } };
  mounted.study = mounted.add = mounted.people = mounted.account = false;
}

function refresh() { if (S.phase === 'app') renderApp(); }

// ---------------------------------------------------------------- top-level render
function render() {
  const authPhase = ['config', 'setup', 'signin', 'inactive'].includes(S.phase);
  $('screen-loading').hidden = S.phase !== 'loading';
  $('screen-auth').hidden = !authPhase;
  $('screen-main').hidden = S.phase !== 'app';
  if (S.phase !== 'app') document.title = 'Recall by Hand';
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
function field(label, input) { return h('div', { class: 'field' }, h('label', { class: 'label', for: input.id, text: label }), input); }

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
      await setDoc(doc(db, 'users', user.uid), { name: n, email: user.email || '', active: true, canEditUniversal: true, createdAt: serverTimestamp() });
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
    h('p', { text: 'This first account runs the site: it creates everyone else\'s accounts, decides who can edit universal decks, and can see every deck.' }),
    authForm(submit, ...kids, btn, status),
    S.fbUser ? h('button', { type: 'button', class: 'linkbtn quiet', onclick: () => signOut(auth) }, 'Sign out') : null
  );
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
  put($('authBox'), 
    h('h1', { text: 'Sign in' }),
    h('p', { id: 'signinNote', text: signinNote() }),
    authForm(submit, field('Email', email), field('Password', pw), btn, status),
    h('div', null, h('button', { type: 'button', class: 'linkbtn', onclick: forgot }, 'Forgot your password?'))
  );
}
function signinNote() {
  return S.adminName ? `Accounts are made by ${S.adminName}. Ask them if you need one.` : 'Accounts are made by the admin. Ask them if you need one.';
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
  S.view = view;
  if (view === 'decks') { S.dv.editing = null; S.dv.renaming = false; S.dv.creating = false; }
  if (view === 'account') mounted.account = false;
  renderApp();
  window.scrollTo({ top: 0 });
}
function renderTop() {
  $('peopleTab').hidden = !S.isAdmin;
  const n = S.isAdmin && S.requests.size ? ` (${S.requests.size})` : '';
  $('peopleTab').textContent = 'People' + n;
  for (const b of document.querySelectorAll('.tab')) b.setAttribute('aria-selected', b.dataset.view === S.view ? 'true' : 'false');
  const who = $('whoBtn');
  who.textContent = myName() + (S.isAdmin ? ' · admin' : '');
  if (S.view === 'account') who.setAttribute('aria-current', 'page'); else who.removeAttribute('aria-current');
}
function renderApp() {
  if (S.view === 'people' && !S.isAdmin) S.view = 'study';
  renderTop();
  for (const v of ['study', 'decks', 'add', 'people', 'account']) $('view-' + v).hidden = S.view !== v;
  if (S.view === 'study') renderStudy();
  else if (S.view === 'decks') renderDecks();
  else if (S.view === 'add') renderAdd();
  else if (S.view === 'people') renderPeople();
  else if (S.view === 'account') renderAccount();
}

// ---------------------------------------------------------------- study
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
      h('div', { style: 'flex:1 1 18rem;min-width:0' }, h('h1', { text: 'Draw a set to write out' }), h('p', { class: 'lede', id: 'studyLede' })),
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
      h('dl', { class: 'stats', id: 'poolStats' }),
      h('div', { id: 'likelyWrap' }, h('span', { class: 'label', text: 'Most likely to come up' }), h('ul', { class: 'likely', id: 'likely' })),
      h('div', null, h('button', { type: 'button', class: 'btn primary big', id: 'startBtn', onclick: startSession }, 'Draw')),
      h('details', { class: 'how' },
        h('summary', { text: 'How picking works' }),
        h('div', { class: 'formula', text: 'weight = (days since you last wrote it + 1) ÷ (times written + 1)' }),
        h('p', { text: 'Each item gets a weight and the draw picks without repeats, so heavier items are more likely but nothing is guaranteed. Something you haven\'t touched in two months outweighs something you wrote yesterday, and something you\'ve written ten times weighs less than something you\'ve written once.' }),
        h('p', { text: 'Items you\'ve never written count as at least 30 days overdue, so new additions come up early. Skipping doesn\'t count as studying. Your progress is your own: friends studying the same universal deck keep separate counts.' }))
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
  $('studyLede').textContent = kind === 'poems'
    ? "Pick how many poems to write out in full. The ones you haven't written lately come up first."
    : "Facts you haven't written in a while, or have written fewer times, are more likely to come up.";
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

  const groups = [['universal', 'Universal'], ['mine', 'Mine'], ['shared', 'Shared by friends']];
  const box = $('chipGroups');
  const toggle = (id) => { if (sel.has(id)) sel.delete(id); else sel.add(id); savePrefs(); renderSetup(); };
  withFocus(box, () => {
    put(box, 
      h('div', { class: 'chips' }, chip(kind === 'poems' ? 'All poems' : 'All facts', all.length, sel.size === 0, () => { sel.clear(); savePrefs(); renderSetup(); }, 'pool', 'all')),
      ...groups.map(([cat, label]) => {
        const ds = decks.filter(d => category(d) === cat);
        if (!ds.length) return null;
        return h('div', { class: 'chip-group' }, h('h3', { text: label }),
          h('div', { class: 'chips' }, ...ds.map(d => chip(d.name, itemsOf(d).length, sel.has(d.id), () => toggle(d.id), '', d.id, cat === 'shared' ? ownerLabel(d) : null))));
      })
    );
  });

  const items = pool(kind, sel);
  const now = Date.now();
  $('countLabel').textContent = kind === 'poems' ? 'How many poems' : 'How many facts';
  const input = $('countInput');
  input.max = kind === 'poems' ? '50' : '200';
  if (document.activeElement !== input) input.value = curCount();
  const presets = kind === 'poems' ? [1, 2, 3, 5] : [5, 10, 20, 40];
  put($('presets'), ...presets.map(n => h('button', { type: 'button', class: 'preset', 'aria-pressed': n === curCount() ? 'true' : 'false', onclick: () => setCount(n) }, String(n))));

  let never = 0, gap = 0, recent = 0;
  for (const x of items) {
    const pr = progOf(x.deckId, x.itemId);
    const t = pr ? Number(pr.t) || 0 : 0;
    if (!t) never++; else { gap = Math.max(gap, (now - t) / DAY); if (now - t < DAY) recent++; }
  }
  const allNew = never === items.length;
  put($('poolStats'), 
    h('div', null, h('dt', { text: 'In this pool' }), h('dd', { text: items.length.toLocaleString() })),
    h('div', null, h('dt', { text: 'Never written out' }), h('dd', { text: never.toLocaleString() })),
    h('div', null, h('dt', { text: allNew ? 'Written in last 24 h' : 'Longest gap' }), h('dd', { text: allNew ? String(recent) : spanDays(gap) }))
  );

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

function startSession() {
  const kind = S.study.kind;
  const items = pool(kind, S.study.sel[kind]);
  if (!items.length) return;
  const picked = shuffle(draw(items, Math.min(curCount(), items.length))).map(x => ({ deckId: x.deckId, itemId: x.itemId }));
  S.session = { kind, items: picked, i: 0, revealed: false, firstLine: false, finished: false, done: [], skipped: 0 };
  renderStudy();
  window.scrollTo({ top: 0 });
  $('revealBtn').focus({ preventScroll: true });
}
function currentItem() {
  const s = S.session;
  while (s && s.i < s.items.length) {
    const ref = s.items[s.i];
    const d = S.decks.get(ref.deckId);
    const it = d && d.items[ref.itemId];
    if (it && typeof it === 'object') return { ref, d, it };
    s.i++; s.revealed = false; s.firstLine = false;   // deleted mid-set
  }
  return null;
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
  $('sessProgress').textContent = `${s.i + 1} / ${s.items.length}`;
  $('sessBar').style.width = `${Math.round(s.i / s.items.length * 100)}%`;
  $('cardDeck').textContent = d.name;
  $('cardMeta').textContent = n ? `written ${n}× · last ${ago(Number(pr.t), now)}` : 'first time';
  $('cardPrompt').textContent = poem ? it.title : it.p;
  const by = $('cardByline');
  by.hidden = !poem;
  if (poem) by.textContent = [it.author ? 'by ' + it.author : '', plural(poemLines(it.text), 'line')].filter(Boolean).join(' · ');
  $('cardHint').textContent = poem ? 'Write the whole poem from memory, then reveal it to check.' : 'Write the answer on paper, then reveal it.';
  $('cardHint').hidden = s.revealed;
  const fl = $('cardFirstLine');
  fl.textContent = poem ? poemFirstLine(it.text) : '';
  fl.hidden = !(poem && s.firstLine && !s.revealed);
  $('firstLineBtn').hidden = !(poem && !s.revealed && !s.firstLine);
  const ans = $('cardAnswer');
  const wasHidden = ans.hidden;
  ans.textContent = poem ? it.text : it.a;
  ans.className = 'answer hand' + (poem ? ' poem' : '');
  ans.hidden = !s.revealed;
  if (s.revealed && wasHidden) { void ans.offsetWidth; ans.classList.add('show'); }
  $('revealBtn').hidden = s.revealed;
  $('revealBtn').textContent = poem ? 'Reveal the poem' : 'Reveal answer';
  $('nextBtn').hidden = !s.revealed;
  $('nextBtn').textContent = s.i + 1 >= s.items.length ? 'Written, finish set' : (poem ? 'Written, next poem' : 'Written, next fact');
}
function reveal() {
  const s = S.session; if (!s || s.finished || s.revealed) return;
  s.revealed = true; renderCard();
  $('nextBtn').focus({ preventScroll: true });
}
function recordAndNext() {
  const s = S.session; if (!s || s.finished || !s.revealed) return;
  const cur = currentItem(); if (!cur) return;
  const key = progKey(cur.ref.deckId, cur.ref.itemId);
  const pr = S.progress[key];
  const n = (pr ? Number(pr.n) || 0 : 0) + 1;
  save(setDoc(doc(db, 'progress', myUid()), { p: { [key]: { n, t: Date.now() } }, updatedAt: serverTimestamp() }, { merge: true }));
  s.done.push(cur.ref);
  advance();
}
function skip() { const s = S.session; if (!s || s.finished) return; s.skipped++; advance(); }
function advance() {
  const s = S.session;
  s.i++; s.revealed = false; s.firstLine = false;
  if (s.i >= s.items.length) s.finished = true;
  renderStudy();
  if (!s.finished) $('revealBtn').focus({ preventScroll: true });
  else { const a = $('againBtn'); if (a) a.focus({ preventScroll: true }); }
}
function endSet() {
  const s = S.session; if (!s) return;
  if (!s.done.length) { S.session = null; renderStudy(); return; }
  s.finished = true; renderStudy();
}
function renderDone() {
  const s = S.session;
  const poem = s.kind === 'poems';
  const n = s.done.length;
  const noun = poem ? 'poem' : 'fact';
  const parts = [`You wrote out ${plural(n, noun)}`];
  if (s.skipped) parts.push(`skipped ${s.skipped}`);
  const left = s.items.length - n - s.skipped;
  if (left > 0) parts.push(`left ${left} for next time`);
  const rows = s.done.map(ref => {
    const d = S.decks.get(ref.deckId); const it = d && d.items[ref.itemId];
    if (!it) return null;
    return poem
      ? h('li', null, h('span', { class: 'dp hand', text: it.title }), h('span', { class: 'da', text: [it.author, plural(poemLines(it.text), 'line')].filter(Boolean).join(' · ') }))
      : h('li', null, h('span', { class: 'dp hand', text: it.p }), h('span', { class: 'da hand', text: it.a }));
  }).filter(Boolean);
  put($('study-done'), 
    h('div', null, h('h1', { text: n ? 'Set finished' : 'Nothing recorded' }), h('p', { class: 'lede', text: parts.join(', ') + '.' })),
    rows.length ? h('ul', { class: 'done-list' }, ...rows) : null,
    h('div', { class: 'row' },
      h('button', { type: 'button', class: 'btn primary big', id: 'againBtn', onclick: () => { S.session = null; startSession(); } }, 'Draw another set'),
      h('button', { type: 'button', class: 'btn ghost big', onclick: () => { S.session = null; renderStudy(); } }, 'Change decks or count'))
  );
}

// ---------------------------------------------------------------- decks
function deckPills(d) {
  const pills = [h('span', { class: 'pill kind', text: d.kind === 'poems' ? 'Poems' : 'Facts' })];
  if (d.scope === 'universal') pills.push(h('span', { class: 'pill uni', text: 'Universal' }));
  else pills.push(h('span', { class: 'pill ' + (d.visibility === 'shared' ? 'shared' : 'private'), text: d.visibility === 'shared' ? 'Shared' : 'Private' }));
  return pills;
}
function deckRow(d, showOwner) {
  const count = itemsOf(d).length;
  return h('li', { class: 'deck-row' },
    h('div', { style: 'min-width:0' },
      h('button', { type: 'button', class: 'dn', onclick: () => openDeck(d.id) }, d.name),
      h('div', { class: 'dm' }, ...deckPills(d), showOwner ? h('span', { text: 'by ' + ownerLabel(d) }) : null)),
    h('span', { class: 'dc', text: plural(count, d.kind === 'poems' ? 'poem' : 'fact') }));
}
function openDeck(id) {
  Object.assign(S.dv, { open: id, q: '', editing: null, confirmItem: false, renaming: false, confirmDeck: false, expanded: new Set() });
  renderDecks(true);
  window.scrollTo({ top: 0 });
}
function renderDecks(force) {
  const root = $('view-decks');
  if (!force && (S.dv.editing || S.dv.renaming || S.dv.creating)) return;   // keep forms the person is typing in
  if (!S.decksLoaded) { put(root, h('div', { class: 'block-note' }, h('p', { text: 'Loading your decks…' }))); return; }
  if (S.dv.open && S.decks.has(S.dv.open)) return renderDeckDetail(root);
  S.dv.open = null;

  const all = sortDecks([...S.decks.values()]);
  const sec = (title, list, empty, showOwner) => h('div', { class: 'deck-section' }, h('h3', { text: title }),
    list.length ? h('ul', { class: 'deck-list' }, ...list.map(d => deckRow(d, showOwner))) : h('p', { class: 'empty-line', text: empty }));
  const sections = [
    sec('Universal decks', all.filter(d => d.scope === 'universal'), canEditUniversal() ? 'No universal decks yet. Make one with New deck.' : 'No universal decks yet.', true),
    sec('My decks', all.filter(d => category(d) === 'mine'), 'You have no decks of your own yet.', false),
  ];
  if (S.isAdmin) {
    const others = all.filter(d => d.scope === 'personal' && d.ownerId !== myUid());
    const byOwner = new Map();
    for (const d of others) { if (!byOwner.has(d.ownerId)) byOwner.set(d.ownerId, []); byOwner.get(d.ownerId).push(d); }
    const groups = [...byOwner.entries()].sort((a, b) => ownerLabel(a[1][0]).localeCompare(ownerLabel(b[1][0])));
    sections.push(h('div', { class: 'deck-section' }, h('h3', { text: "Everyone else's decks" }),
      groups.length ? h('div', null, ...groups.map(([, ds]) => h('div', { class: 'owner-group' },
        h('span', { class: 'owner-name', text: ownerLabel(ds[0]) }),
        h('ul', { class: 'deck-list' }, ...ds.map(d => deckRow(d, false))))))
        : h('p', { class: 'empty-line', text: 'Nobody else has made a deck yet.' })));
  } else {
    sections.push(sec('Shared by friends', all.filter(d => category(d) === 'shared'), 'When friends share one of their decks, it shows up here.', true));
  }

  put(root, 
    h('div', { class: 'row', style: 'align-items:flex-start' },
      h('div', { style: 'flex:1 1 18rem;min-width:0' }, h('h1', { text: 'Decks' }),
        h('p', { class: 'lede', text: S.isAdmin ? 'Universal decks everyone studies, your own, and every deck your friends have made.' : 'Universal decks everyone studies, your own, and the ones friends share.' })),
      h('button', { type: 'button', class: 'btn primary', onclick: () => { S.dv.creating = true; renderDecks(true); const n = $('ndName'); if (n) n.focus(); } }, 'New deck')),
    S.dv.creating ? newDeckBox() : null,
    ...sections
  );
}

function newDeckBox() {
  const name = h('input', { type: 'text', id: 'ndName', maxlength: '80', placeholder: 'e.g. Poems we love', autocomplete: 'off' });
  let kind = 'facts', scope = canEditUniversal() ? 'universal' : 'personal';
  const share = h('input', { type: 'checkbox', id: 'ndShare' });
  const shareRow = h('label', { class: 'check', for: 'ndShare' }, share, h('span', { text: 'Let friends see and study it (they can\'t change it)' }));
  const status = h('p', { class: 'status', role: 'status' });
  const radio = (group, value, label, checked, on) => {
    const id = `nd-${group}-${value}`;
    const r = h('input', { type: 'radio', name: 'nd-' + group, id, value, checked });
    r.addEventListener('change', () => on(value));
    return h('label', { class: 'check', for: id }, r, h('span', { text: label }));
  };
  const sync = () => { shareRow.hidden = scope !== 'personal'; };
  const close = () => { S.dv.creating = false; renderDecks(true); };
  const create = async () => {
    const n = name.value.trim();
    if (!n) { status.className = 'status err'; status.textContent = 'Give the deck a name.'; name.focus(); return; }
    status.className = 'status'; status.textContent = 'Creating…';
    try {
      const id = await createDeck({ name: n, kind, scope, visibility: share.checked ? 'shared' : 'private' });
      S.dv.creating = false;
      S.add = { kind, deckId: id, chosen: true };
      toast(`Created ${n}. Add to it here.`);
      go('add');
    } catch (e) { status.className = 'status err'; status.textContent = dataError(e); }
  };
  const box = h('div', { class: 'panel-box' },
    h('h2', { text: 'New deck' }),
    field('Name', name),
    h('div', { class: 'field' }, h('span', { class: 'label', text: 'Holds' }),
      h('div', { class: 'radios' }, radio('kind', 'facts', 'Facts (prompt and answer)', true, v => { kind = v; }), radio('kind', 'poems', 'Poems (written out whole)', false, v => { kind = v; }))),
    h('div', { class: 'field' }, h('span', { class: 'label', text: 'Who it\'s for' }),
      h('div', { class: 'radios' },
        canEditUniversal() ? radio('scope', 'universal', 'Universal: everyone studies it', true, v => { scope = v; sync(); }) : null,
        radio('scope', 'personal', 'Just me', !canEditUniversal(), v => { scope = v; sync(); }))),
    shareRow,
    h('div', { class: 'row' }, h('button', { type: 'button', class: 'btn primary', onclick: create }, 'Create deck'), h('button', { type: 'button', class: 'btn ghost', onclick: close }, 'Cancel')),
    status);
  name.addEventListener('keydown', (e) => { if (e.key === 'Enter') { e.preventDefault(); create(); } });
  sync();
  return box;
}

function renderDeckDetail(root) {
  const d = S.decks.get(S.dv.open);
  const dv = S.dv;
  const write = canWrite(d);
  const poem = d.kind === 'poems';
  const now = Date.now();
  const items = itemsOf(d);
  const neverN = items.filter(([iid]) => !progOf(d.id, iid)).length;

  // header
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
      h('span', { text: `Delete ${d.name} and its ${plural(items.length, poem ? 'poem' : 'fact')}${d.scope === 'universal' ? ' for everyone' : ''}?` }),
      h('button', { type: 'button', class: 'btn danger', onclick: async () => {
        dv.confirmDeck = false; dv.open = null;
        await save(deleteDoc(doc(db, 'decks', d.id)), `Deleted ${d.name}.`);
        renderDecks(true);
      } }, 'Delete deck'),
      h('button', { type: 'button', class: 'btn ghost', onclick: () => { dv.confirmDeck = false; renderDecks(true); } }, 'Keep it'));
  } else {
    const shareToggle = d.scope === 'personal' && write
      ? (() => {
          const cb = h('input', { type: 'checkbox', id: 'deckShare', checked: d.visibility === 'shared' });
          cb.addEventListener('change', () => save(updateDoc(doc(db, 'decks', d.id), { visibility: cb.checked ? 'shared' : 'private', updatedAt: serverTimestamp() }),
            cb.checked ? 'Friends can now see and study this deck.' : 'This deck is private again.'));
          return h('label', { class: 'check', for: 'deckShare' }, cb, h('span', { text: 'Let friends see and study it' }));
        })()
      : null;
    actions = h('div', { class: 'stack-sm', style: 'justify-items:start' },
      h('div', { class: 'row' },
        category(d) !== 'other' ? h('button', { type: 'button', class: 'btn primary', onclick: () => { S.study.kind = d.kind; S.study.sel[d.kind] = new Set([d.id]); savePrefs(); S.session = null; go('study'); } }, 'Study this deck') : null,
        write ? h('button', { type: 'button', class: 'btn ghost', onclick: () => { S.add = { kind: d.kind, deckId: d.id, chosen: true }; go('add'); } }, poem ? 'Add a poem' : 'Add facts') : null),
      shareToggle,
      write ? h('div', { class: 'row' },
        h('button', { type: 'button', class: 'linkbtn', onclick: () => { dv.renaming = true; renderDecks(true); } }, 'Rename'),
        h('button', { type: 'button', class: 'linkbtn warn', onclick: () => { dv.confirmDeck = true; renderDecks(true); } }, 'Delete deck')) : null);
  }

  const head = h('div', { class: 'deck-head' },
    h('div', { class: 'title' },
      h('h1', { text: d.name }),
      h('div', { class: 'meta' }, ...deckPills(d),
        h('span', { text: d.ownerId === myUid() ? 'yours' : 'by ' + ownerLabel(d) }),
        h('span', { text: `· ${plural(items.length, poem ? 'poem' : 'fact')} · ${neverN} you haven't written yet` })),
      !write ? h('p', { class: 'help', text: d.scope === 'universal' ? 'Only people with permission can change universal decks.' : 'You can study this deck, but only its owner can change it.' }) : null),
    actions);

  // list
  const q = norm(dv.q);
  let rows = items.map(([iid, it]) => ({ iid, it, pr: progOf(d.id, iid) }));
  if (q) rows = rows.filter(r => poem
    ? (norm(r.it.title).includes(q) || norm(r.it.author).includes(q) || norm(r.it.text).includes(q))
    : (norm(r.it.p).includes(q) || norm(r.it.a).includes(q)));
  rows.forEach(r => { r.w = weightOf(r.it, r.pr, now); });
  rows.sort((a, b) => b.w - a.w);
  const maxW = rows.length ? rows[0].w : 1;
  const shown = rows.slice(0, MAX_LIST);

  const search = h('input', { type: 'search', id: 'deckSearch', placeholder: poem ? 'Search titles, poets and lines' : 'Search prompts and answers', 'aria-label': 'Search this deck', autocomplete: 'off', value: dv.q });
  let st = 0;
  search.addEventListener('input', () => { clearTimeout(st); st = setTimeout(() => { dv.q = search.value; dv.editing = null; renderDecks(true); const s2 = $('deckSearch'); if (s2) { s2.focus(); s2.setSelectionRange(s2.value.length, s2.value.length); } }, 150); });
  const fallback = h('textarea', { readonly: true, hidden: true, 'aria-label': 'Deck as text', class: 'data' });
  const copyBtn = h('button', { type: 'button', class: 'btn ghost', onclick: () => {
    const text = poem
      ? items.map(([, it]) => `${it.title}${it.author ? ' — ' + it.author : ''}\n\n${it.text}`).join('\n\n---\n\n')
      : items.map(([, it]) => `${it.p} | ${String(it.a).replace(/\r?\n/g, ' ')}`).join('\n');
    copyText(text, fallback, `Copied ${plural(items.length, poem ? 'poem' : 'fact')}.`);
  } }, 'Copy as text');

  put(root, 
    h('div', null, h('button', { type: 'button', class: 'linkbtn quiet', onclick: () => { dv.open = null; renderDecks(true); } }, '← All decks')),
    head,
    items.length ? h('div', { class: 'tools' }, search, copyBtn) : null,
    fallback,
    h('p', { class: 'list-note', text: rows.length
      ? `${plural(rows.length, poem ? 'poem' : 'fact')}${q ? ' match' : ''}, most likely to come up for you first${rows.length > shown.length ? `. Showing the first ${MAX_LIST}; search to narrow.` : '.'}`
      : (q ? 'Nothing matches that search.' : (poem ? 'No poems in this deck yet.' : 'No facts in this deck yet.')) }),
    shown.length ? h('ul', { class: 'items' }, ...shown.map(r => itemRow(d, r, maxW, now, write))) : null
  );
}

function itemRow(d, r, maxW, now, write) {
  const dv = S.dv;
  const poem = d.kind === 'poems';
  if (dv.editing === r.iid) return itemEditRow(d, r);
  const n = r.pr ? Number(r.pr.n) || 0 : 0;
  const open = dv.expanded.has(r.iid);
  const side = h('div', { class: 'item-side' },
    n ? h('span', { class: 'mono', text: `${n}× · ${ago(Number(r.pr.t), now)}` }) : h('span', { class: 'pill new', text: 'new' }),
    h('span', { class: 'bar', title: 'How likely it is to come up for you', 'aria-hidden': 'true' }, h('i', { style: `width:${Math.max(4, Math.round(r.w / maxW * 100))}%` })),
    h('div', { class: 'row', style: 'justify-content:flex-end;gap:.75rem' },
      poem ? h('button', { type: 'button', class: 'linkbtn', 'aria-expanded': open ? 'true' : 'false', onclick: () => { if (open) dv.expanded.delete(r.iid); else dv.expanded.add(r.iid); renderDecks(true); } }, open ? 'Hide' : 'Read') : null,
      write ? h('button', { type: 'button', class: 'linkbtn', onclick: () => { dv.editing = r.iid; dv.confirmItem = false; renderDecks(true); const f = $('edit1'); if (f) f.focus(); } }, 'Edit') : null));
  const main = poem
    ? h('div', { style: 'min-width:0' }, h('p', { class: 'item-p', text: r.it.title }),
        h('p', { class: 'item-sub', text: [r.it.author ? 'by ' + r.it.author : '', plural(poemLines(r.it.text), 'line')].filter(Boolean).join(' · ') }),
        !open ? h('p', { class: 'item-a hand', text: poemFirstLine(r.it.text) + ' …' }) : null)
    : h('div', { style: 'min-width:0' }, h('p', { class: 'item-p', text: r.it.p }), h('p', { class: 'item-a hand', text: r.it.a }));
  return h('li', { class: 'item' }, main, side, poem && open ? h('pre', { class: 'poem-full', text: r.it.text }) : null);
}

function itemEditRow(d, r) {
  const dv = S.dv;
  const poem = d.kind === 'poems';
  const close = () => { dv.editing = null; dv.confirmItem = false; renderDecks(true); };
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
    await save(updateDoc(doc(db, 'decks', d.id), { ['items.' + r.iid]: next, updatedAt: serverTimestamp() }), 'Saved.');
  };
  const delBtn = h('button', { type: 'button', class: 'btn ghost' }, poem ? 'Delete poem' : 'Delete fact');
  delBtn.addEventListener('click', async () => {
    if (!dv.confirmItem) { dv.confirmItem = true; delBtn.textContent = 'Yes, delete it'; delBtn.className = 'btn danger'; return; }
    close();
    await save(updateDoc(doc(db, 'decks', d.id), { ['items.' + r.iid]: deleteField(), updatedAt: serverTimestamp() }), 'Deleted.');
  });
  const fields = poem
    ? [h('div', { class: 'grid-2' }, field('Title', f1), field('Poet', f2)), field('Poem', f3)]
    : [field('Prompt', f1), field('Answer', f2)];
  return h('li', { class: 'item' }, h('div', { class: 'item-edit' }, ...fields,
    h('div', { class: 'row' },
      h('button', { type: 'button', class: 'btn primary', onclick: doSave }, 'Save'),
      h('button', { type: 'button', class: 'btn ghost', onclick: close }, 'Cancel'),
      h('span', { class: 'spacer' }), delBtn)));
}

// ---------------------------------------------------------------- add
let lastParse = { rows: [], skipped: [] };
function writableDecks(kind) {
  return sortDecks([...S.decks.values()].filter(d => d.kind === kind && (
    (d.scope === 'universal' && canEditUniversal()) || (d.scope === 'personal' && d.ownerId === myUid()))));
}
function mountAdd() {
  mounted.add = true;
  const root = $('view-add');
  const factsBox = h('div', { id: 'addFactsBox', class: 'stack-sm' },
    h('label', { class: 'label', for: 'pasteBox', text: 'Your facts' }),
    h('textarea', { id: 'pasteBox', class: 'data', spellcheck: 'false', placeholder: 'Capital of Australia | Canberra\nNumber of bones in the adult human body | 206\nChemistry | Chemical symbol for potassium | K' }),
    h('p', { class: 'help' }, 'One fact per line, prompt first: ', h('code', { text: 'prompt | answer' }), '. To send lines to other decks of yours in the same paste, start the line with the deck name: ', h('code', { text: 'deck | prompt | answer' }), '. Tab-separated columns from a spreadsheet work too.'),
    h('div', { class: 'preview', id: 'preview', hidden: true }));
  const poemBox = h('div', { id: 'addPoemBox', class: 'stack-sm', hidden: true },
    h('div', { class: 'grid-2' },
      field('Title', h('input', { type: 'text', id: 'poemTitle', maxlength: '200', autocomplete: 'off' })),
      field('Poet (optional)', h('input', { type: 'text', id: 'poemAuthor', maxlength: '200', autocomplete: 'off' }))),
    field('The poem', h('textarea', { id: 'poemText', class: 'poem-input', maxlength: String(MAX_POEM), placeholder: 'Paste or type the poem here. Line breaks and stanza gaps are kept.' })),
    h('p', { class: 'help', id: 'poemInfo' }));
  const scopeRadio = (value, label) => {
    const id = 'adScope-' + value;
    const r = h('input', { type: 'radio', name: 'adScope', id, value });
    r.addEventListener('change', updateAdd);
    return h('label', { class: 'check', for: id, id: 'adScopeWrap-' + value }, r, h('span', { text: label }));
  };
  const share = h('input', { type: 'checkbox', id: 'adShare' });
  const newDeck = h('div', { id: 'addNewDeck', class: 'panel-box', hidden: true },
    field('New deck name', h('input', { type: 'text', id: 'newDeckName', maxlength: '80', autocomplete: 'off', placeholder: 'e.g. Biology terms' })),
    h('div', { class: 'radios', id: 'adScopes' }, scopeRadio('universal', 'Universal: everyone studies it'), scopeRadio('personal', 'Just me')),
    h('label', { class: 'check', for: 'adShare', id: 'adShareWrap' }, share, h('span', { text: 'Let friends see and study it' })));

  put(root, 
    h('div', { class: 'row', style: 'align-items:flex-start' },
      h('div', { style: 'flex:1 1 18rem;min-width:0' }, h('h1', { text: 'Add' }), h('p', { class: 'lede', id: 'addLede' })),
      seg('addKind', [['facts', 'Facts'], ['poems', 'Poems']], S.add.kind, (k) => { S.add.kind = k; S.add.chosen = false; S.add.deckId = null; $('addStatus').textContent = ''; renderAdd(); })),
    h('div', { class: 'field' }, h('label', { class: 'label', for: 'addDeck', text: 'Add to' }), h('select', { id: 'addDeck' })),
    newDeck, factsBox, poemBox,
    h('div', { class: 'row' }, h('button', { type: 'button', class: 'btn primary big', id: 'addBtn', disabled: true }, 'Add'), h('p', { class: 'status', id: 'addStatus', role: 'status' }))
  );
  $('addDeck').addEventListener('change', (e) => { S.add.deckId = e.target.value; S.add.chosen = true; renderAdd(); if (S.add.deckId === '__new') $('newDeckName').focus(); });
  let t = 0;
  const later = () => { clearTimeout(t); t = setTimeout(updateAdd, 120); $('addStatus').textContent = ''; };
  for (const id of ['pasteBox', 'newDeckName', 'poemTitle', 'poemAuthor', 'poemText']) $(id).addEventListener('input', later);
  share.addEventListener('change', updateAdd);
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
    const mine = decks.find(d => d.scope === 'personal');
    val = (mine || decks[0] || { id: '__new' }).id;
  }
  S.add.deckId = val;
  const sel = $('addDeck');
  const groups = [];
  const uni = decks.filter(d => d.scope === 'universal');
  const mine = decks.filter(d => d.scope === 'personal');
  const opt = (d) => h('option', { value: d.id, text: `${d.name} (${itemsOf(d).length})` });
  if (uni.length) groups.push(h('optgroup', { label: 'Universal' }, ...uni.map(opt)));
  if (mine.length) groups.push(h('optgroup', { label: 'My decks' }, ...mine.map(opt)));
  groups.push(h('option', { value: '__new', text: 'New deck…' }));
  put(sel, ...groups);
  sel.value = val;
  const isNew = val === '__new';
  $('addNewDeck').hidden = !isNew;
  $('adScopeWrap-universal').hidden = !canEditUniversal();
  const checked = document.querySelector('input[name="adScope"]:checked');
  if (!checked || (checked.value === 'universal' && !canEditUniversal())) $('adScope-personal').checked = true;
  $('addFactsBox').hidden = kind !== 'facts';
  $('addPoemBox').hidden = kind !== 'poems';
  updateAdd();
}
function newDeckChoice() {
  const sc = document.querySelector('input[name="adScope"]:checked');
  const scope = sc && sc.value === 'universal' && canEditUniversal() ? 'universal' : 'personal';
  return { name: $('newDeckName').value.trim(), scope, visibility: $('adShare').checked ? 'shared' : 'private' };
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
    let existing = null;
    if (!routed && S.add.deckId !== '__new') existing = S.decks.get(S.add.deckId) || null;
    else existing = byName(deck);
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
  $('adShareWrap').hidden = !isNew || newDeckChoice().scope !== 'personal';
  const btn = $('addBtn');
  if (kind === 'poems') {
    const title = $('poemTitle').value.trim();
    const text = cleanPoem($('poemText').value);
    const lines = poemLines(text);
    $('poemInfo').textContent = text ? `${plural(lines, 'line')}${title ? '' : ' · add a title'}` : 'Tip: keep a blank line between stanzas.';
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
    const shown = r.rows.slice(0, 6);
    kids.push(h('div', { class: 'tablewrap' }, h('table', { class: 'pv' },
      h('thead', null, h('tr', null, showDeck ? h('th', { text: 'Deck' }) : null, h('th', { text: 'Prompt' }), h('th', { text: 'Answer' }))),
      h('tbody', null, ...shown.map(row => h('tr', null, showDeck ? h('td', { text: row.deck }) : null, h('td', { text: row.p }), h('td', { text: row.a }))),
        r.rows.length > shown.length ? h('tr', null, h('td', { colspan: showDeck ? '3' : '2', text: `…and ${(r.rows.length - shown.length).toLocaleString()} more` })) : null))));
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
      plans.push({ kind: 'create', name: g.r.deck, scope: fromBox ? choice.scope : 'personal', visibility: fromBox ? choice.visibility : 'private', items, n: g.rows.length, fromBox });
    }
  }
  try {
    let createdFromBox = null;
    for (const p of plans) {
      if (p.kind === 'add') await addItems(p.id, p.items);
      else { const id = await createDeck({ name: p.name, kind: 'facts', scope: p.scope, visibility: p.visibility, items: p.items }); if (p.fromBox) createdFromBox = id; }
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
      const newId = await createDeck({ name: ch.name, kind: 'poems', scope: ch.scope, visibility: ch.visibility, items: { [id]: item } });
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
  const uni = h('input', { type: 'checkbox', id: 'npUni' });
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
      await setDoc(doc(db, 'users', uid), { name: n, email: e, active: true, canEditUniversal: uni.checked, createdAt: serverTimestamp() });
      if (mode === 'link') await sendPasswordResetEmail(auth, e);
      status.className = 'status ok';
      status.textContent = mode === 'link'
        ? `Account made. ${n} will get an email with a link to set their password (it may land in spam).`
        : `Account made. Give ${n} their email and the temporary password; they can change it from their account page.`;
      name.value = ''; email.value = ''; temp.value = ''; uni.checked = false;
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
    h('div', null, h('h1', { text: 'People' }), h('p', { class: 'lede', text: 'Make accounts for your friends and choose what they can do. Everyone can make their own decks; only people you allow can add to or change universal decks.' })),
    h('form', { class: 'panel-box', novalidate: true, onsubmit: (ev) => { ev.preventDefault(); create(); } },
      h('h2', { text: 'Add a person' }),
      h('div', { class: 'grid-2' }, field('Name', name), field('Email', email)),
      h('label', { class: 'check', for: 'npUni' }, uni, h('span', { text: 'Can add to and edit universal decks' })),
      h('div', { class: 'field' }, h('span', { class: 'label', text: 'Password' }),
        h('div', { class: 'radios' }, pwMode('link', 'Email them a link to set their own', true), pwMode('temp', 'I\'ll set a temporary one', false))),
      h('div', { id: 'npTempWrap', hidden: true }, field('Temporary password', temp)),
      h('div', { class: 'row' }, btn), status),
    h('div', { id: 'requestsBox' }),
    h('div', { class: 'deck-section' }, h('h3', { text: 'Accounts' }), h('ul', { class: 'people', id: 'peopleList' }))
  );
}
function renderPeople() {
  if (!S.isAdmin) return;
  if (!mounted.people) mountPeople();
  // requests
  const reqs = [...S.requests.entries()];
  put($('requestsBox'), ...(reqs.length ? [h('div', { class: 'deck-section' }, h('h3', { text: 'Waiting for you to approve' }),
    h('ul', { class: 'people' }, ...reqs.map(([uid, r]) => h('li', { class: 'person' },
      h('div', { style: 'min-width:0' }, h('div', { class: 'pn', text: String(r.name || 'Someone') }), h('div', { class: 'pe', text: String(r.email || '') })),
      h('div', { class: 'row' },
        h('button', { type: 'button', class: 'btn primary', onclick: async () => {
          const ok = await save(setDoc(doc(db, 'users', uid), { name: String(r.name || 'Friend').slice(0, 60), email: String(r.email || ''), active: true, canEditUniversal: false, createdAt: serverTimestamp() }), `${r.name || 'They'} can now sign in and study.`);
          if (ok) save(deleteDoc(doc(db, 'requests', uid)));
        } }, 'Approve'),
        h('button', { type: 'button', class: 'btn ghost', onclick: () => save(deleteDoc(doc(db, 'requests', uid)), 'Request dismissed.') }, 'Dismiss'))))))] : []));

  if (S.pp.renaming) return;   // keep the rename box
  const list = $('peopleList');
  const deckCounts = new Map();
  for (const d of S.decks.values()) if (d.scope === 'personal') {
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
  const deckLine = `${plural(c.all, 'deck')} of their own${c.shared ? `, ${c.shared} shared` : ''}`;
  if (S.pp.renaming === uid) {
    const inp = h('input', { type: 'text', id: 'ppRename', maxlength: '60', value: String(p.name || ''), 'aria-label': 'Name' });
    const done = () => { S.pp.renaming = null; renderPeople(); };
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
  const toggle = (id, label, checked, onChange) => {
    const cb = h('input', { type: 'checkbox', id, checked, 'data-key': id });
    cb.addEventListener('change', () => onChange(cb.checked));
    return h('label', { class: 'check', for: id }, cb, h('span', { text: label }));
  };
  return h('li', { class: 'person' },
    h('div', { style: 'min-width:0' },
      h('div', { class: 'pn' }, h('span', { text: String(p.name || 'Unnamed') }),
        isAdminRow ? h('span', { class: 'pill admin', text: 'Admin' }) : null,
        !isAdminRow && p.active !== true ? h('span', { class: 'pill off', text: 'Turned off' }) : null,
        !isAdminRow && p.canEditUniversal ? h('span', { class: 'pill uni', text: 'Edits universal' }) : null),
      h('div', { class: 'pe', text: String(p.email || '') }),
      h('div', { class: 'pd', text: deckLine })),
    h('div', { class: 'row', style: 'justify-content:flex-end' },
      h('button', { type: 'button', class: 'linkbtn', onclick: () => { S.pp.renaming = uid; renderPeople(); } }, 'Rename'),
      p.email ? h('button', { type: 'button', class: 'linkbtn', onclick: async () => {
        try { await sendPasswordResetEmail(auth, p.email); toast(`Sent a password reset link to ${p.email}.`); } catch (e) { toast(authError(e)); }
      } }, 'Send password reset') : null),
    !isAdminRow ? h('div', { class: 'pc' },
      toggle('uni-' + uid, 'Can add to and edit universal decks', p.canEditUniversal === true,
        (v) => save(updateDoc(doc(db, 'users', uid), { canEditUniversal: v }), v ? `${p.name} can now edit universal decks.` : `${p.name} can no longer edit universal decks.`)),
      toggle('act-' + uid, 'Account on', p.active === true,
        (v) => save(updateDoc(doc(db, 'users', uid), { active: v }), v ? `${p.name} can sign in again.` : `${p.name}'s account is turned off. Their decks are kept.`))) : null);
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
    if (ok && S.isAdmin) await save(updateDoc(doc(db, 'meta', 'admin'), { name: v.slice(0, 60) }));
    if (ok) { status.className = 'status ok'; status.textContent = 'Saved. New decks will show this name.'; }
  };
  put($('view-account'), 
    h('div', null, h('h1', { text: 'Your account' }), h('p', { class: 'lede', text: S.fbUser.email || '' })),
    h('form', { class: 'panel-box', novalidate: true, onsubmit: (e) => { e.preventDefault(); saveName(); } },
      field('Your name', name), h('div', { class: 'row' }, h('button', { type: 'submit', class: 'btn primary' }, 'Save name')), status),
    h('div', { class: 'panel-box' },
      h('h2', { text: 'Password' }),
      h('p', { class: 'help', text: 'We\'ll email you a link to set a new password.' }),
      h('div', { class: 'row' }, h('button', { type: 'button', class: 'btn ghost', onclick: async () => {
        try { await sendPasswordResetEmail(auth, S.fbUser.email); toast('Check your email for a link to set a new password.'); } catch (e) { toast(authError(e)); }
      } }, 'Email me a reset link'))),
    h('div', null, h('button', { type: 'button', class: 'btn ghost', onclick: () => signOut(auth) }, 'Sign out'))
  );
}

// ---------------------------------------------------------------- events
for (const b of document.querySelectorAll('.tab')) b.addEventListener('click', () => go(b.dataset.view));
$('whoBtn').addEventListener('click', () => go('account'));
$('revealBtn').addEventListener('click', reveal);
$('nextBtn').addEventListener('click', recordAndNext);
$('skipBtn').addEventListener('click', skip);
$('endBtn').addEventListener('click', endSet);
$('firstLineBtn').addEventListener('click', () => { if (S.session) { S.session.firstLine = true; renderCard(); $('revealBtn').focus({ preventScroll: true }); } });
document.addEventListener('keydown', (e) => {
  if (S.phase !== 'app' || S.view !== 'study' || !S.session || S.session.finished) return;
  const tag = (e.target && e.target.tagName) || '';
  if (/INPUT|TEXTAREA|SELECT/.test(tag) || e.metaKey || e.ctrlKey || e.altKey) return;
  const onOther = tag === 'BUTTON' && e.target.id !== 'revealBtn' && e.target.id !== 'nextBtn';
  if (onOther && (e.key === ' ' || e.key === 'Enter')) return;
  if (e.key === ' ' || e.key === 'Spacebar') { e.preventDefault(); if (!S.session.revealed) reveal(); }
  else if (e.key === 'Enter') { e.preventDefault(); S.session.revealed ? recordAndNext() : reveal(); }
  else if (e.key === 's' || e.key === 'S') { e.preventDefault(); skip(); }
});

boot();
