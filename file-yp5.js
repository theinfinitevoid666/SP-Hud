// ==UserScript==
// @name         Social Poker — Board & Equity HUD
// @namespace    https://github.com/YOURNAME/socialpoker-hud
// @version      1.0.0
// @description  Overlay for socialpoker.gg: shows the flop/turn/river, your hole cards, live win% and outs. Reads the game's own WebSocket stream instead of scraping the 3D canvas.
// @author       you
// @match        https://socialpoker.gg/*
// @match        https://www.socialpoker.gg/*
// @icon         https://socialpoker.gg/favicon.ico
// @run-at       document-start
// @grant        none
// @license      MIT
// @updateURL    https://raw.githubusercontent.com/YOURNAME/socialpoker-hud/main/socialpoker-hud.user.js
// @downloadURL  https://raw.githubusercontent.com/YOURNAME/socialpoker-hud/main/socialpoker-hud.user.js
// ==/UserScript==

(function () {
  'use strict';
  if (window.__SPHUD_INSTALLED__) return;
  window.__SPHUD_INSTALLED__ = true;

  /* ------------------------------------------------------------------ *
   * Config
   * ------------------------------------------------------------------ */
  const CFG = {
    rollouts: 1500,        // monte-carlo iterations (2-3 opponents)
    rolloutsManyOpps: 600, // used when 4+ opponents
    maxOpps: 8,
    debounceMs: 90,
    historyMax: 200
  };
  const LS = { pos: 'sphud.pos', min: 'sphud.min', hands: 'sphud.hands' };

  /* ------------------------------------------------------------------ *
   * Cards: 2-char codes, rank in "23456789TJQKA", suit in "shdc"
   * ------------------------------------------------------------------ */
  const RANKS = '23456789TJQKA';
  const SUITS = 'shdc';
  const GLYPH = { s: '\u2660', h: '\u2665', d: '\u2666', c: '\u2663' };
  const RED = { h: 1, d: 1 };

  // card string -> int (rankIndex * 4 + suitIndex)
  function toInt(code) {
    if (!code || code.length !== 2) return -1;
    const r = RANKS.indexOf(code[0]);
    const s = SUITS.indexOf(code[1]);
    return (r < 0 || s < 0) ? -1 : r * 4 + s;
  }

  function normCard(v) {
    if (v == null) return null;
    if (typeof v === 'string') {
      const s = v.trim().toUpperCase();
      if (s.length === 2 && RANKS.includes(s[0]) && SUITS.includes(s[1].toLowerCase())) {
        return s[0] + s[1].toLowerCase();
      }
      if (s.length === 3 && s.slice(0, 2) === '10' && SUITS.includes(s[2].toLowerCase())) {
        return 'T' + s[2].toLowerCase();
      }
      return null;
    }
    if (typeof v === 'number' && Number.isFinite(v) && v >= 0 && v <= 51) {
      return RANKS[v % 13] + SUITS[Math.floor(v / 13) % 4];
    }
    if (typeof v === 'object') {
      const rawR = v.rank ?? v.r ?? v.value ?? v.face;
      const rawS = v.suit ?? v.s ?? v.suitChar ?? v.suitCode;
      let r = null, su = null;
      if (typeof rawR === 'number' && rawR >= 2 && rawR <= 14) r = RANKS[rawR - 2];
      else if (typeof rawR === 'string') {
        const u = rawR.trim().toUpperCase();
        r = u === '10' ? 'T' : (RANKS.includes(u[0]) ? u[0] : null);
      }
      if (typeof rawS === 'string') {
        const l = rawS.trim().toLowerCase();
        su = SUITS.includes(l[0]) ? l[0] : ({ spade: 's', heart: 'h', diamond: 'd', club: 'c' })[l] ?? null;
      } else if (typeof rawS === 'number' && rawS >= 0 && rawS <= 3) su = SUITS[rawS];
      if (r && su) return r + su;
    }
    return null;
  }

  function parseCards(v) {
    if (!v) return [];
    if (typeof v === 'string') { const c = normCard(v); return c ? [c] : []; }
    if (Array.isArray(v)) return v.map(normCard).filter(Boolean);
    return [];
  }

  /* ------------------------------------------------------------------ *
   * Hand evaluator (5-7 cards) -> comparable integer
   * ------------------------------------------------------------------ */
  const CAT_NAMES = ['High Card', 'Pair', 'Two Pair', 'Three of a Kind', 'Straight',
                     'Flush', 'Full House', 'Four of a Kind', 'Straight Flush'];
  const RANK_COUNT = new Uint8Array(15);

  function straightHigh(mask) {
    for (let hi = 14; hi >= 6; hi--) {
      const need = 0b11111 << (hi - 4);
      if ((mask & need) === need) return hi;
    }
    const wheel = (1 << 14) | (1 << 5) | (1 << 4) | (1 << 3) | (1 << 2);
    return (mask & wheel) === wheel ? 5 : 0;
  }
  function topRanks(mask, n) {
    const out = [];
    for (let r = 14; r >= 2 && out.length < n; r--) if (mask & (1 << r)) out.push(r);
    return out;
  }
  function pack(cat, ks) {
    let s = cat;
    for (let i = 0; i < 5; i++) s = s * 16 + (ks[i] || 0);
    return s;
  }

  function evalCards(cs) {
    RANK_COUNT.fill(0);
    const suitMask = [0, 0, 0, 0];
    const suitCount = [0, 0, 0, 0];
    let rankMask = 0;

    for (let i = 0; i < cs.length; i++) {
      const c = cs[i], r = (c >> 2) + 2, su = c & 3;
      RANK_COUNT[r]++;
      suitCount[su]++;
      suitMask[su] |= 1 << r;
      rankMask |= 1 << r;
    }

    let quad = 0, t1 = 0, t2 = 0, p1 = 0, p2 = 0, p3 = 0;
    const singles = [];
    for (let r = 14; r >= 2; r--) {
      const n = RANK_COUNT[r];
      if (n === 4) { if (!quad) quad = r; }
      else if (n === 3) { if (!t1) t1 = r; else if (!t2) t2 = r; }
      else if (n === 2) { if (!p1) p1 = r; else if (!p2) p2 = r; else if (!p3) p3 = r; }
      else if (n === 1) singles.push(r);
    }

    const st = straightHigh(rankMask);
    let best;
    if (quad) best = pack(7, [quad, Math.max(singles[0] || 0, p1 || 0, t1 || 0)]);
    else if (t1 && (t2 || p1)) best = pack(6, [t1, t2 || p1]);
    else if (st) best = pack(4, [st]);
    else if (t1) best = pack(3, [t1, singles[0] || 0, singles[1] || 0]);
    else if (p1 && p2) best = pack(2, [p1, p2, Math.max(singles[0] || 0, p3 || 0)]);
    else if (p1) best = pack(1, [p1, singles[0] || 0, singles[1] || 0, singles[2] || 0]);
    else best = pack(0, singles.slice(0, 5));

    // a flush can beat everything except a full house / quads -> take the max
    for (let su = 0; su < 4; su++) {
      if (suitCount[su] < 5) continue;
      const sf = straightHigh(suitMask[su]);
      const fs = sf ? pack(8, [sf]) : pack(5, topRanks(suitMask[su], 5));
      if (fs > best) best = fs;
    }
    return best;
  }

  const catOf = (score) => Math.floor(score / 1048576);

  function bestLabel(cs) {
    if (cs.length < 5) return '\u2014';
    const s = evalCards(cs);
    const cat = catOf(s);
    if (cat === 8 && Math.floor(s / 65536) % 16 === 14) return 'Royal Flush';
    return CAT_NAMES[cat];
  }

  /* ------------------------------------------------------------------ *
   * Equity + outs
   * ------------------------------------------------------------------ */
  function equity(hero, board, oppCount, dead, rollouts) {
    const used = new Uint8Array(52);
    for (const c of hero) used[c] = 1;
    for (const c of board) used[c] = 1;
    for (const c of dead) if (c >= 0) used[c] = 1;

    const deck = [];
    for (let c = 0; c < 52; c++) if (!used[c]) deck.push(c);

    const needBoard = 5 - board.length;
    const need = needBoard + oppCount * 2;
    if (need > deck.length) return { win: 0, tie: 0 };

    let win = 0, tie = 0;
    for (let it = 0; it < rollouts; it++) {
      for (let i = 0; i < need; i++) {
        const j = i + ((Math.random() * (deck.length - i)) | 0);
        const t = deck[i]; deck[i] = deck[j]; deck[j] = t;
      }
      let p = 0;
      const b = board.slice();
      for (let i = 0; i < needBoard; i++) b.push(deck[p++]);

      const hs = evalCards(hero.concat(b));
      let best = -1;
      for (let o = 0; o < oppCount; o++) {
        const os = evalCards([deck[p++], deck[p++]].concat(b));
        if (os > best) best = os;
      }
      if (hs > best) win++;
      else if (hs === best) tie++;
    }
    return { win: win / rollouts, tie: tie / rollouts };
  }

  function countOuts(hero, board, dead) {
    const used = new Uint8Array(52);
    for (const c of hero) used[c] = 1;
    for (const c of board) used[c] = 1;
    for (const c of dead) if (c >= 0) used[c] = 1;

    const baseCat = catOf(evalCards(hero.concat(board)));
    let outs = 0, unseen = 0;
    for (let c = 0; c < 52; c++) {
      if (used[c]) continue;
      unseen++;
      if (catOf(evalCards(hero.concat(board, c))) > baseCat) outs++;
    }
    return { outs, unseen, pct: unseen ? outs / unseen : 0 };
  }

  /* ------------------------------------------------------------------ *
   * Game state
   * ------------------------------------------------------------------ */
  const S = {
    handId: null, board: [], hero: [], revealed: [], pot: 0,
    players: [], street: 'preflop', lastType: '', msgCount: 0, debug: false, eq: null
  };

  function streetOf(n) { return n >= 5 ? 'river' : n === 4 ? 'turn' : n === 3 ? 'flop' : 'preflop'; }

  function countOpponents() {
    const inHand = S.players.filter(p =>
      p.inHand && p.status !== 'folded' && p.status !== 'sitting-out' && !p.isSittingOut);
    return Math.max(1, Math.min(CFG.maxOpps, inHand.length - 1));
  }

  function ingest(msg) {
    const t = typeof msg.type === 'string' ? msg.type : '';
    S.lastType = t; S.msgCount++;

    const src = (msg.state && typeof msg.state === 'object') ? msg.state : msg;

    // new hand -> wipe
    if (typeof src.handId === 'string' && src.handId && src.handId !== S.handId) {
      closeHand();
      S.handId = src.handId; S.board = []; S.hero = []; S.revealed = []; S.pot = 0; S.eq = null;
    }

    // hero hole cards
    if (t === 'YOUR_CARDS') S.hero = parseCards(msg.cards);
    if (!S.hero.length) {
      const c = parseCards(msg.myCards ?? src.myCards ?? src.yourCards ?? src.holeCards);
      if (c.length) S.hero = c;
    }

    // board
    const boardSrc = msg.communityCards ?? src.communityCards ?? msg.presentation?.finalBoard;
    if (Array.isArray(boardSrc)) {
      const b = parseCards(boardSrc);
      if (b.length >= S.board.length) S.board = b;
    }
    S.street = streetOf(S.board.length);

    // pot
    const pot = msg.pot ?? src.pot;
    if (typeof pot === 'number' && pot >= 0) S.pot = pot;

    // players + any face-up cards
    const players = msg.players ?? src.players;
    if (Array.isArray(players) && players.length) {
      S.players = players.map(p => ({
        userId: p.userId, username: p.username, seat: p.seat, stack: p.stack,
        status: p.status, inHand: p.inHand !== false, isSittingOut: !!p.isSittingOut
      }));
      const rv = [];
      for (const p of players) {
        const c = parseCards(p.revealedCards ?? p.holeCards);
        if (c.length === 2) rv.push({ username: p.username || '?', cards: c });
      }
      if (rv.length) S.revealed = rv;
    }

    // showdown payload
    const results = msg.showdown?.results;
    if (Array.isArray(results)) {
      const rv = [];
      for (const r of results) {
        const c = parseCards(r.revealedCards ?? r.holeCards ?? r.cards);
        if (c.length === 2) rv.push({ username: r.username || '?', cards: c });
      }
      if (rv.length) S.revealed = rv;
    }

    if (t === 'HAND_COMPLETE') closeHand();

    render(); scheduleMath();
  }

  function closeHand() {
    if (!S.handId) return;
    if (!S.hero.length && !S.board.length) return;
    const log = readLog();
    log.push({
      ts: Date.now(), handId: S.handId, hero: S.hero.slice(), board: S.board.slice(),
      street: S.street, pot: S.pot, win: S.eq ? +S.eq.win.toFixed(4) : null,
      revealed: S.revealed.map(r => ({ u: r.username, c: r.cards }))
    });
    while (log.length > CFG.historyMax) log.shift();
    try { localStorage.setItem(LS.hands, JSON.stringify(log)); } catch (e) {}
  }

  function readLog() {
    try { return JSON.parse(localStorage.getItem(LS.hands) || '[]'); } catch (e) { return []; }
  }

  /* ------------------------------------------------------------------ *
   * WebSocket hook
   * ------------------------------------------------------------------ */
  const NativeWS = window.WebSocket;
  const recent = [];

  function onRaw(text) {
    if (!text || text[0] !== '{') return; // the client also sends a bare "ping"
    let msg;
    try { msg = JSON.parse(text); } catch (e) { return; }
    if (!msg || typeof msg !== 'object') return;
    if (S.debug) { recent.push(msg.type || '?'); if (recent.length > 6) recent.shift(); }
    try { ingest(msg); } catch (e) { console.warn('[SPHUD] ingest', e); }
  }

  if (NativeWS) {
    function HookedWS(url, protocols) {
      const ws = protocols === undefined ? new NativeWS(url) : new NativeWS(url, protocols);
      try {
        ws.addEventListener('message', (ev) => {
          const d = ev.data;
          if (typeof d === 'string') onRaw(d);
          else if (d instanceof ArrayBuffer) { try { onRaw(new TextDecoder().decode(d)); } catch (e) {} }
        });
      } catch (e) {}
      return ws;
    }
    HookedWS.prototype = NativeWS.prototype;
    HookedWS.CONNECTING = 0; HookedWS.OPEN = 1; HookedWS.CLOSING = 2; HookedWS.CLOSED = 3;
    window.WebSocket = HookedWS;
  }

  /* ------------------------------------------------------------------ *
   * UI
   * ------------------------------------------------------------------ */
  const CSS = `
    :host { all: initial; }
    * { box-sizing: border-box; font-family: ui-monospace, SFMono-Regular, Menlo, monospace; }
    .panel { position: fixed; left: 16px; bottom: 16px; width: 272px;
      background: linear-gradient(180deg, rgba(28,22,44,.95), rgba(14,11,24,.97));
      border: 1px solid rgba(231,203,135,.35); border-radius: 12px; color: #efe7d6;
      box-shadow: 0 18px 50px -20px #000; backdrop-filter: blur(10px);
      pointer-events: auto; user-select: none; overflow: hidden; }
    .hdr { display:flex; align-items:center; gap:8px; padding:8px 10px; cursor: grab;
      border-bottom:1px solid rgba(231,203,135,.18); background: rgba(231,203,135,.06); }
    .title { font-size: 11px; letter-spacing:.14em; font-weight:700; color:#e7cb87; }
    .street { margin-left:auto; font-size:10px; text-transform:uppercase; letter-spacing:.1em; color:#9a8f7c; }
    .dot { width:7px;height:7px;border-radius:50%;background:#e7cb87; box-shadow:0 0 8px #e7cb87; }
    .body { padding:10px; display:flex; flex-direction:column; gap:9px; }
    .panel.min .body { display:none; }
    .row { display:flex; gap:5px; min-height:42px; }
    .card { width:30px;height:42px;border-radius:5px;background:#f7f3e8;color:#1a1a2e;
      display:flex;flex-direction:column;align-items:center;justify-content:center;
      line-height:1;font-weight:700;font-size:15px; box-shadow: inset 0 0 0 1px rgba(0,0,0,.15); }
    .card .s { font-size:14px; }
    .card.red { color:#c0392b; }
    .card.empty { background: rgba(255,255,255,.05); box-shadow: inset 0 0 0 1px rgba(231,203,135,.22); }
    .board .card { width:34px;height:48px;font-size:16px; }
    .grid { display:grid; grid-template-columns: repeat(3, 1fr); gap:6px; }
    .stat { background: rgba(255,255,255,.04); border:1px solid rgba(231,203,135,.14);
      border-radius:7px; padding:5px 6px; overflow:hidden; }
    .stat label { display:block; font-size:9px; letter-spacing:.1em; color:#9a8f7c; }
    .stat b { font-size:13px; }
    .stat b.good { color:#7ee08a; }
    .stat b.bad { color:#ff8f8f; }
    .rev { font-size:11px; color:#cbbf9f; display:flex; flex-direction:column; gap:3px; }
    .rev .line { display:flex; gap:5px; align-items:center; }
    .rev .mini { width:17px;height:23px;font-size:10px;border-radius:3px;background:#f7f3e8;
      color:#1a1a2e;display:inline-flex;align-items:center;justify-content:center;font-weight:700; }
    .rev .mini.red { color:#c0392b; }
    .foot { display:flex; align-items:center; gap:6px; font-size:10px; color:#9a8f7c; }
    .btn { background: rgba(231,203,135,.12); color:#e7cb87; border:1px solid rgba(231,203,135,.3);
      border-radius:6px; font-size:10px; padding:3px 6px; cursor:pointer; font-family:inherit; }
    .btn:hover { background: rgba(231,203,135,.22); }
    .small { margin-left:auto; font-size:9px; }
    .status { white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }
  `;

  const HTML = `
    <div class="panel" id="panel">
      <div class="hdr" id="hdr">
        <span class="dot"></span><span class="title">FLOP HUD</span>
        <span class="street" id="street">preflop</span>
        <button class="btn" id="min">\u2013</button>
      </div>
      <div class="body">
        <div class="row board" id="board"></div>
        <div class="row" id="hero"></div>
        <div class="grid">
          <div class="stat"><label>WIN</label><b id="win">\u2014</b></div>
          <div class="stat"><label>OUTS</label><b id="outs">\u2014</b></div>
          <div class="stat"><label>MADE</label><b id="made">\u2014</b></div>
          <div class="stat"><label>POT</label><b id="pot">\u2014</b></div>
          <div class="stat"><label>OPP</label><b id="opp">\u2014</b></div>
          <div class="stat"><label>STREET</label><b id="street2">\u2014</b></div>
        </div>
        <div class="rev" id="rev"></div>
        <div class="foot">
          <span class="status" id="status">waiting for a hand\u2026</span>
          <button class="btn small" id="export">export log</button>
        </div>
      </div>
    </div>`;

  const host = document.createElement('div');
  host.style.cssText = 'position:fixed;inset:0;pointer-events:none;z-index:2147483000;';
  (document.documentElement || document.body).appendChild(host);
  const root = host.attachShadow({ mode: 'open' });
  root.innerHTML = `<style>${CSS}</style>${HTML}`;

  const $ = (id) => root.getElementById(id);
  const panel = $('panel');

  // restore prefs
  try {
    if (localStorage.getItem(LS.min) === '1') panel.classList.add('min');
    const pos = JSON.parse(localStorage.getItem(LS.pos) || 'null');
    if (pos) { panel.style.left = pos.left; panel.style.top = pos.top; panel.style.bottom = 'auto'; }
  } catch (e) {}

  function cardEl(code, mini) {
    const el = document.createElement('span');
    el.className = 'card' + (RED[code[1]] ? ' red' : '');
    if (mini) { el.className = 'mini' + (RED[code[1]] ? ' red' : ''); }
    el.textContent = (code[0] === 'T' ? '10' : code[0]) + GLYPH[code[1]];
    return el;
  }
  function emptyEl() { const e = document.createElement('span'); e.className = 'card empty'; return e; }
  const fmt = (n) => n >= 1e6 ? (n / 1e6).toFixed(1) + 'M' : n >= 1e3 ? (n / 1e3).toFixed(1) + 'K' : String(n);

  function render() {
    $('street').textContent = S.street;
    $('street2').textContent = S.street;

    const board = $('board'); board.textContent = '';
    for (let i = 0; i < 5; i++) board.appendChild(S.board[i] ? cardEl(S.board[i]) : emptyEl());

    const hero = $('hero'); hero.textContent = '';
    for (let i = 0; i < 2; i++) hero.appendChild(S.hero[i] ? cardEl(S.hero[i]) : emptyEl());

    $('pot').textContent = S.pot ? fmt(S.pot) : '\u2014';

    const rev = $('rev'); rev.textContent = '';
    for (const r of S.revealed) {
      const line = document.createElement('div');
      line.className = 'line';
      const name = document.createElement('span');
      name.textContent = r.username.slice(0, 12);
      line.appendChild(name);
      for (const c of r.cards) line.appendChild(cardEl(c, true));
      rev.appendChild(line);
    }

    $('status').textContent = S.debug
      ? `msg ${S.msgCount} \u00b7 ${recent.join(' ')}`
      : S.handId ? `hand \u00b7 ${S.street} \u00b7 hero ${S.hero.length}/2` : 'waiting for a hand\u2026';
  }

  function setStat(id, txt, cls) {
    const el = $(id);
    el.textContent = txt;
    el.className = cls || '';
  }

  /* ------------------------------------------------------------------ *
   * Maths (debounced, main thread)
   * ------------------------------------------------------------------ */
  let mathTimer = null;
  function scheduleMath() {
    if (mathTimer) clearTimeout(mathTimer);
    mathTimer = setTimeout(runMath, CFG.debounceMs);
  }

  function runMath() {
    mathTimer = null;
    if (S.hero.length !== 2) { setStat('win', '\u2014'); setStat('outs', '\u2014'); setStat('made', '\u2014'); return; }

    const hero = S.hero.map(toInt), board = S.board.map(toInt);
    if (hero.some(c => c < 0) || board.some(c => c < 0)) return;
    const dead = S.revealed.flatMap(r => r.cards.map(toInt)).filter(c => c >= 0);
    const opp = countOpponents();

    setStat('opp', String(opp));
    setStat('made', bestLabel(hero.concat(board)));

    const ro = opp >= 4 ? CFG.rolloutsManyOpps : CFG.rollouts;
    const eq = equity(hero, board, opp, dead, ro);
    S.eq = eq;
    setStat('win', (eq.win * 100).toFixed(1) + '%' + (eq.tie > 0.005 ? ` \u00b7 tie ${(eq.tie * 100).toFixed(1)}%` : ''),
            eq.win >= 0.5 ? 'good' : 'bad');

    if (board.length >= 3 && board.length < 5) {
      const o = countOuts(hero, board, dead);
      setStat('outs', `${o.outs} \u00b7 ${(o.pct * 100).toFixed(0)}%`, o.outs > 0 ? 'good' : '');
    } else {
      setStat('outs', '\u2014');
    }
  }

  /* ------------------------------------------------------------------ *
   * Interaction
   * ------------------------------------------------------------------ */
  $('min').addEventListener('click', () => {
    panel.classList.toggle('min');
    try { localStorage.setItem(LS.min, panel.classList.contains('min') ? '1' : '0'); } catch (e) {}
  });

  $('export').addEventListener('click', () => {
    const blob = new Blob([JSON.stringify(readLog(), null, 2)], { type: 'application/json' });
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = `socialpoker-hands-${new Date().toISOString().slice(0, 10)}.json`;
    a.click();
    setTimeout(() => URL.revokeObjectURL(a.href), 5000);
  });

  (function draggable() {
    const hdr = $('hdr');
    let dx = 0, dy = 0, dragging = false;
    hdr.addEventListener('pointerdown', (e) => {
      dragging = true;
      const r = panel.getBoundingClientRect();
      dx = e.clientX - r.left; dy = e.clientY - r.top;
      hdr.setPointerCapture(e.pointerId);
      hdr.style.cursor = 'grabbing';
    });
    hdr.addEventListener('pointermove', (e) => {
      if (!dragging) return;
      panel.style.left = (e.clientX - dx) + 'px';
      panel.style.top = (e.clientY - dy) + 'px';
      panel.style.bottom = 'auto';
    });
    hdr.addEventListener('pointerup', () => {
      dragging = false;
      hdr.style.cursor = 'grab';
      try {
        localStorage.setItem(LS.pos, JSON.stringify({ left: panel.style.left, top: panel.style.top }));
      } catch (e) {}
    });
  })();

  window.addEventListener('keydown', (e) => {
    if (!e.altKey) return;
    if (e.key.toLowerCase() === 'h') { $('min').click(); e.preventDefault(); }
    if (e.key.toLowerCase() === 'd') { S.debug = !S.debug; render(); e.preventDefault(); }
  });

  // tiny API for console poking
  window.__sphud = { state: S, equity, evalCards, bestLabel };

  render();
})();