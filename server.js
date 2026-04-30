/**
 * DAX Oracle Server v2 — Node.js met ingebouwde v13 Engine
 * ========================================================
 * Webhook receiver + candle store + LIVE signaal-engine.
 * Engine draait server-side: geen laptop nodig, ~2sec latency.
 *
 * Endpoints:
 *   POST /webhook          — Pine Script candle ontvangst + engine tick
 *   POST /import_history   — CSV bulk import
 *   GET  /candles?n=       — candle history ophalen
 *   GET  /predictions      — alle predictions
 *   GET  /state            — huidige engine state (params, actieve trade, etc.)
 *   POST /params           — engine parameters instellen
 *   POST /clear            — data wissen
 *   GET  /                 — health check
 *   GET  /trackrecord      — alle gesloten trades
 *   POST /trackrecord/clear — wis trackrecord
 */

const express = require('express');
const cors = require('cors');
const fs = require('fs');
const path = require('path');
const http = require('http');
const https = require('https');

const app = express();
app.use(cors());
app.use(express.json({ limit: '50mb' }));
app.use(express.urlencoded({ extended: true, limit: '50mb' }));

// ─── CONFIG ──────────────────────────────────────────
const PORT = process.env.PORT || 8889;
const WEBHOOK_SECRET = process.env.WEBHOOK_SECRET || 'DAXsecret2024';
const NTFY_TOPIC = process.env.NTFY_TOPIC || 'mathieu-dax-oracle';
const TICK_SIZE = parseFloat(process.env.TICK_SIZE || '0.5');
const PT_VALUE = parseFloat(process.env.PT_VALUE || '25');
const CURRENCY = process.env.CURRENCY || '€';
const INSTRUMENT = process.env.INSTRUMENT || 'DAX';
const MAX_HISTORY = 100000;

const DATA_DIR = process.env.DATA_DIR || '/tmp';
const CANDLES_FILE = path.join(DATA_DIR, `${INSTRUMENT.toLowerCase()}_candles.json`);
const STATE_FILE = path.join(DATA_DIR, `${INSTRUMENT.toLowerCase()}_state.json`);
const TRACK_FILE = path.join(DATA_DIR, `${INSTRUMENT.toLowerCase()}_trackrecord.json`);

// ─── STATE ───────────────────────────────────────────
let candleHistory = [];
let tfData = { '1':{}, '5':{}, '15':{}, '30':{}, '60':{} };
let predictions = [];
let trackRecord = [];
let activePending = null;
let activeTrade = null;
let lastSignalIdx = -999;
let signalCount = 0;

// Engine parameters (stelbaar via API)
let engineParams = {
  tf: 5, sl: 1.0, tp: 1.5, atrMax: 45, maxBars: 19,
  minScore: 4, htfOn: true, dirMode: 'both',
  cooldown: 15, contracts: 1, commission: 3.60,
  skipHours: [], skipScores: [],
};

// ═══════════════════════════════════════════════════════
// HELPERS
// ═══════════════════════════════════════════════════════

function r2(v) { return Math.round(v * 100) / 100; }
function snapTick(v) { return Math.round(v / TICK_SIZE) * TICK_SIZE; }
function snapStopBull(v) { return Math.floor(v / TICK_SIZE) * TICK_SIZE; }
function snapStopBear(v) { return Math.ceil(v / TICK_SIZE) * TICK_SIZE; }
function snapTgtBull(v) { return Math.floor(v / TICK_SIZE) * TICK_SIZE; }
function snapTgtBear(v) { return Math.ceil(v / TICK_SIZE) * TICK_SIZE; }

function calcRollingHTF(candles, endIdx, period) {
  const startIdx = endIdx - period + 1;
  if (startIdx < 0 || endIdx >= candles.length) return null;
  const first = candles[startIdx];
  let h = first.h, l = first.l, vol = 0;
  for (let i = startIdx; i <= endIdx; i++) {
    if (candles[i].h > h) h = candles[i].h;
    if (candles[i].l < l) l = candles[i].l;
    vol += candles[i].v || 0;
  }
  return { t: candles[endIdx].t, o: first.o, h, l, c: candles[endIdx].c, v: vol };
}

function emaUpdate(prev, val, period) {
  if (prev == null) return val;
  const k = 2 / (period + 1);
  return val * k + prev * (1 - k);
}

function utcToLocalHour(utcStr) {
  if (!utcStr || utcStr.length < 16) return -1;
  const d = new Date(utcStr.replace(' ', 'T') + ':00Z');
  return isNaN(d) ? parseInt(utcStr.slice(11, 13)) : d.getHours();
}

function nowIso() {
  const d = new Date();
  return d.toISOString().slice(0, 16).replace('T', ' ');
}

function normalize(data) {
  const out = {};
  // Extract tf_data if present
  const tfRaw = {};
  for (const [k, v] of Object.entries(data)) {
    const kl = k.toLowerCase();
    if (['open', 'o'].includes(kl)) out.o = parseFloat(v);
    else if (['high', 'h'].includes(kl)) out.h = parseFloat(v);
    else if (['low', 'l'].includes(kl)) out.l = parseFloat(v);
    else if (['close', 'c'].includes(kl)) out.c = parseFloat(v);
    else if (['volume', 'v', 'vol'].includes(kl)) out.v = parseFloat(v) || 0;
    else if (kl.startsWith('tf_')) {
      const tfKey = kl.replace('tf_', '').replace('_', '');
      try { tfRaw[tfKey] = typeof v === 'string' ? JSON.parse(v) : v; } catch(e){}
    }
  }
  out._tf_data = tfRaw;
  return out;
}

// ═══════════════════════════════════════════════════════
// v13 SIGNAL ENGINE
// ═══════════════════════════════════════════════════════

function detectSignal(candles, params) {
  const tf = params.tf, atrMax = params.atrMax, htfOn = params.htfOn, dirMode = params.dirMode;
  const N = candles.length;
  if (N < tf * 60) return null;

  // Build rolling HTF + indicators
  const rollingHTF = new Array(N).fill(null);
  for (let i = tf - 1; i < N; i++) rollingHTF[i] = calcRollingHTF(candles, i, tf);

  const atrs = new Array(N).fill(0);
  const e8 = new Array(N).fill(null), e21 = new Array(N).fill(null), e50 = new Array(N).fill(null);
  const rsis = new Array(N).fill(50), vwaps = new Array(N).fill(null);
  let avgGain = 0, avgLoss = 0, rsiInited = false, cumPV = 0, cumV = 0, prevDay = null;

  for (let i = tf - 1; i < N; i++) {
    const htf = rollingHTF[i]; if (!htf) continue;
    const tr = htf.h - htf.l;
    atrs[i] = i === tf - 1 ? tr : (atrs[i - 1] * 13 + tr) / 14;
    e8[i] = emaUpdate(e8[i - 1], htf.c, 8);
    e21[i] = emaUpdate(e21[i - 1], htf.c, 21);
    e50[i] = emaUpdate(e50[i - 1], htf.c, 50);
    if (i > tf - 1) {
      const prev = rollingHTF[i - 1];
      if (prev) {
        const ch = htf.c - prev.c;
        const g = ch > 0 ? ch : 0, l = ch < 0 ? -ch : 0;
        if (!rsiInited) { avgGain = g; avgLoss = l; rsiInited = true; }
        else { avgGain = (avgGain * 13 + g) / 14; avgLoss = (avgLoss * 13 + l) / 14; }
        rsis[i] = avgLoss === 0 ? 100 : (100 - 100 / (1 + avgGain / avgLoss));
      }
    }
    const day = htf.t.slice(0, 10);
    if (prevDay !== day) { cumPV = 0; cumV = 0; prevDay = day; }
    const tp = (htf.h + htf.l + htf.c) / 3, vol = htf.v || 1;
    cumPV += tp * vol; cumV += vol;
    vwaps[i] = cumV > 0 ? cumPV / cumV : tp;
  }

  // Signal detection at last candle
  const ri = N - 1;
  const htf = rollingHTF[ri - 1], atr = atrs[ri - 1];
  if (!htf || !atr || atr <= 0 || atr > atrMax) return null;
  const prev1 = rollingHTF[ri - 2], prev2 = rollingHTF[ri - 3], prev3 = rollingHTF[ri - 4];
  if (!prev1 || !prev2) return null;

  const ema8 = e8[ri - 1], ema21v = e21[ri - 1], ema50v = e50[ri - 1];
  const rsi = rsis[ri - 1], vwap = vwaps[ri - 1];
  if (ema8 == null || ema21v == null || vwap == null) return null;

  const lookback = Math.max(tf, ri - 15 * tf);
  const htfBull = htfOn ? (ema21v > (e21[lookback] || ema21v)) : true;
  const htfBear = htfOn ? (ema21v < (e21[lookback] || ema21v)) : true;

  let swH = htf.h, swL = htf.l;
  for (let j = ri - 10; j < ri - 1; j++) { const r = rollingHTF[j]; if (r) { if (r.h > swH) swH = r.h; if (r.l < swL) swL = r.l; } }

  let bS = 0, rS = 0, bSetup = 'none', rSetup = 'none';

  // 1. EMA alignment
  if (ema8 > ema21v && ema21v > (ema50v || ema21v)) bS += 3; else if (ema8 > ema21v) bS += 1;
  if (ema8 < ema21v && ema21v < (ema50v || ema21v)) rS += 3; else if (ema8 < ema21v) rS += 1;

  // 2. VWAP
  if (htf.c > vwap && prev1.c <= vwap) bS += 2; else if (htf.c > vwap) bS += 1;
  if (htf.c < vwap && prev1.c >= vwap) rS += 2; else if (htf.c < vwap) rS += 1;

  // 3. RSI
  if (rsi < 35) bS += 2; else if (rsi < 45) bS += 1;
  if (rsi > 65) rS += 2; else if (rsi > 55) rS += 1;

  // 4. Liquidity sweep
  const bSweep = htf.l < prev1.l && htf.l < prev2.l && htf.c > prev1.l && htf.c > htf.o;
  const rSweep = htf.h > prev1.h && htf.h > prev2.h && htf.c < prev1.h && htf.c < htf.o;
  if (bSweep) { bS += 4; bSetup = 'liquidity_sweep'; }
  if (rSweep) { rS += 4; rSetup = 'liquidity_sweep'; }

  // 5. Order block retest
  const refOB = prev3 || prev2;
  const bOB = prev2.c > prev2.o && (prev2.c - prev2.o) > atr * 0.5;
  if (bOB && htf.l <= refOB.h && htf.l >= refOB.l && htf.c > htf.o && ema8 > ema21v) {
    bS += 3; if (bSetup === 'none') bSetup = 'ob_retest';
  }
  const rOB = prev2.c < prev2.o && (prev2.o - prev2.c) > atr * 0.5;
  if (rOB && htf.h >= refOB.l && htf.h <= refOB.h && htf.c < htf.o && ema8 < ema21v) {
    rS += 3; if (rSetup === 'none') rSetup = 'ob_retest';
  }

  // 6. FVG fill
  if (htf.l > prev2.h && htf.c >= prev2.h && htf.c <= htf.h && ema8 > ema21v) { bS += 2; if (bSetup === 'none') bSetup = 'fvg_fill'; }
  if (htf.h < prev2.l && htf.c <= prev2.l && htf.c >= htf.l && ema8 < ema21v) { rS += 2; if (rSetup === 'none') rSetup = 'fvg_fill'; }

  // 7. Break of structure
  if (htf.c > swH && htf.c > htf.o && (htf.c - htf.o) > atr * 0.3) { bS += 2; if (bSetup === 'none') bSetup = 'bos'; }
  if (htf.c < swL && htf.c < htf.o && (htf.o - htf.c) > atr * 0.3) { rS += 2; if (rSetup === 'none') rSetup = 'bos'; }

  // 8. Volume spike
  let avgV = 0, avgN = 0;
  for (let j = Math.max(tf, ri - 10); j < ri; j++) { if (rollingHTF[j]) { avgV += rollingHTF[j].v; avgN++; } }
  avgV = avgN > 0 ? avgV / avgN : htf.v;
  if (htf.v > avgV * 1.3) { if (htf.c > htf.o) bS += 1; else rS += 1; }

  // HTF penalty
  if (!htfBull) bS = Math.max(0, bS - 3);
  if (!htfBear) rS = Math.max(0, rS - 3);

  let dir = null, score = 0, setup = 'none';
  if (dirMode !== 'short' && bS > rS) { dir = 'bull'; score = bS; setup = bSetup; }
  else if (dirMode !== 'long' && rS > bS) { dir = 'bear'; score = rS; setup = rSetup; }
  if (!dir || score < params.minScore) return null;

  // Skip filters
  const sigHour = utcToLocalHour(candles[ri - 1].t);
  if (params.skipHours.includes(sigHour)) return null;
  if (params.skipScores.includes(score)) return null;

  const slSize = params.sl * atr, tpSize = slSize * params.tp;
  const entry = snapTick(htf.c);
  let stop, tgt;
  if (dir === 'bull') { stop = snapStopBull(entry - slSize); tgt = snapTgtBull(entry + tpSize); }
  else { stop = snapStopBear(entry + slSize); tgt = snapTgtBear(entry - tpSize); }

  return { dir, score, setup, entry, stop, tgt, rr: params.tp, atr: r2(atr), signalTime: candles[ri - 1].t };
}

// ═══════════════════════════════════════════════════════
// ENGINE TICK — draait bij elke nieuwe candle
// ═══════════════════════════════════════════════════════

function engineTick() {
  const N = candleHistory.length;
  if (N < engineParams.tf * 10) return;

  const rc = candleHistory[N - 1]; // laatste candle
  const ri = N - 1;
  const commPts = engineParams.commission / PT_VALUE;
  const pendingTimeout = 3 * engineParams.tf;

  // 1. Active trade: check exit
  if (activeTrade) {
    let exit = null;
    if (activeTrade.dir === 'bull') {
      if (rc.l <= activeTrade.stop) exit = { outcome: 'LOSS', price: activeTrade.stop };
      else if (rc.h >= activeTrade.tgt) exit = { outcome: 'WIN', price: activeTrade.tgt };
    } else {
      if (rc.h >= activeTrade.stop) exit = { outcome: 'LOSS', price: activeTrade.stop };
      else if (rc.l <= activeTrade.tgt) exit = { outcome: 'WIN', price: activeTrade.tgt };
    }
    activeTrade.barsOpen = (activeTrade.barsOpen || 0) + 1;
    if (!exit && activeTrade.barsOpen >= engineParams.maxBars * engineParams.tf) {
      exit = { outcome: 'EXPIRED', price: rc.c };
    }
    if (exit) {
      const gross = activeTrade.dir === 'bull' ? exit.price - activeTrade.entry : activeTrade.entry - exit.price;
      const netPnl = r2((gross - commPts) * (activeTrade.contracts || 1));
      const p = predictions.find(x => x.id === activeTrade.id);
      if (p) { p.outcome = exit.outcome; p.exitTime = rc.t; p.exitPrice = exit.price; p.pnlPt = netPnl; p.pnlCur = r2(netPnl * PT_VALUE); }
      lastSignalIdx = ri;

      // Track record
      logTrackRecord(p || activeTrade, exit);

      // Push notification
      sendPush(`${exit.outcome} ${activeTrade.dir === 'bull' ? '▲' : '▼'} ${netPnl > 0 ? '+' : ''}${netPnl}pt (${CURRENCY}${r2(netPnl * PT_VALUE)})`, exit.outcome === 'WIN' ? '✅' : '❌');

      activeTrade = null;
      saveEngineState();
    }
    return;
  }

  // 2. Pending: check fill
  if (activePending) {
    let filled = false;
    if (activePending.dir === 'bull' && rc.h >= activePending.entry) filled = true;
    if (activePending.dir === 'bear' && rc.l <= activePending.entry) filled = true;
    activePending.barsWaiting = (activePending.barsWaiting || 0) + 1;

    if (filled) {
      activeTrade = { ...activePending, entryTime: rc.t, barsOpen: 0 };
      const p = predictions.find(x => x.id === activePending.id);
      if (p) { p.outcome = 'open'; p.entryTime = rc.t; }

      // Same-bar exit check
      let ds = false, dt = false;
      if (activePending.dir === 'bull') { if (rc.l <= activePending.stop) ds = true; else if (rc.h >= activePending.tgt) dt = true; }
      else { if (rc.h >= activePending.stop) ds = true; else if (rc.l <= activePending.tgt) dt = true; }

      if (ds || dt) {
        const ep = ds ? activeTrade.stop : activeTrade.tgt;
        const gross = activeTrade.dir === 'bull' ? ep - activeTrade.entry : activeTrade.entry - ep;
        const netPnl = r2((gross - commPts) * (activeTrade.contracts || 1));
        const p2 = predictions.find(x => x.id === activeTrade.id);
        if (p2) { p2.outcome = ds ? 'LOSS' : 'WIN'; p2.exitTime = rc.t; p2.exitPrice = ep; p2.pnlPt = netPnl; p2.pnlCur = r2(netPnl * PT_VALUE); }
        logTrackRecord(p2 || activeTrade, { outcome: ds ? 'LOSS' : 'WIN', price: ep });
        sendPush(`${ds ? 'LOSS' : 'WIN'} ${activeTrade.dir === 'bull' ? '▲' : '▼'} ${netPnl > 0 ? '+' : ''}${netPnl}pt`, ds ? '❌' : '✅');
        lastSignalIdx = ri;
        activeTrade = null;
      }
      activePending = null;
      saveEngineState();
    } else if (activePending.barsWaiting >= pendingTimeout) {
      const p = predictions.find(x => x.id === activePending.id);
      if (p) { p.outcome = 'expired'; }
      lastSignalIdx = ri;
      activePending = null;
      saveEngineState();
    }
    return;
  }

  // 3. Cooldown check
  if (ri - lastSignalIdx < engineParams.cooldown) return;

  // 4. Detect new signal
  const sig = detectSignal(candleHistory, engineParams);
  if (!sig) return;

  // Create pending
  lastSignalIdx = ri;
  signalCount++;
  activePending = {
    id: signalCount,
    ...sig,
    barsWaiting: 0,
    contracts: engineParams.contracts,
    status: 'pending',
    created_at: nowIso()
  };
  predictions.push({ ...activePending, outcome: 'pending' });

  console.log(`★ SIGNAAL #${signalCount} ${sig.dir.toUpperCase()} sc=${sig.score} ${sig.setup} entry=${sig.entry} TP=${sig.tgt} SL=${sig.stop}`);

  // Push notification
  const dir = sig.dir === 'bull' ? '▲ LONG' : '▼ SHORT';
  sendPush(`${dir} sc=${sig.score} ${sig.setup}\nEntry: ${sig.entry}\nTP: ${sig.tgt} | SL: ${sig.stop}`, '🔔');

  saveEngineState();
}

// ═══════════════════════════════════════════════════════
// NTFY.SH PUSH NOTIFICATIONS
// ═══════════════════════════════════════════════════════

function sendPush(msg, emoji) {
  if (!NTFY_TOPIC) return;
  const data = `${emoji || '📊'} ${INSTRUMENT}\n${msg}`;
  const req = https.request({
    hostname: 'ntfy.sh',
    port: 443,
    path: `/${NTFY_TOPIC}`,
    method: 'POST',
    headers: { 'Content-Type': 'text/plain' }
  }, (res) => {
    if (res.statusCode !== 200) console.log(`ntfy: HTTP ${res.statusCode}`);
  });
  req.on('error', (e) => console.log(`ntfy error: ${e.message}`));
  req.write(data);
  req.end();
}

// ═══════════════════════════════════════════════════════
// TRACK RECORD
// ═══════════════════════════════════════════════════════

function logTrackRecord(trade, exit) {
  trackRecord.push({
    dir: trade.dir, setup: trade.setup || '', score: trade.score || 0,
    entry: trade.entry, tgt: trade.tgt, stp: trade.stop || trade.stp,
    outcome: exit.outcome, pnlPt: trade.pnlPt || 0, pnlCur: trade.pnlCur || 0,
    signalTime: trade.signalTime, entryTime: trade.entryTime, exitTime: trade.exitTime || candleHistory[candleHistory.length - 1]?.t,
    params: { ...engineParams },
    logged: new Date().toISOString()
  });
  saveTrackRecord();
}

// ═══════════════════════════════════════════════════════
// PERSISTENCE
// ═══════════════════════════════════════════════════════

function saveCandles() {
  try {
    fs.writeFileSync(CANDLES_FILE, JSON.stringify({ candles: candleHistory.slice(-MAX_HISTORY), tfData }));
  } catch (e) { console.log(`⚠ saveCandles: ${e.message}`); }
}

function loadCandles() {
  try {
    if (fs.existsSync(CANDLES_FILE)) {
      const data = JSON.parse(fs.readFileSync(CANDLES_FILE, 'utf8'));
      candleHistory = data.candles || [];
      tfData = data.tfData || tfData;
      console.log(`📂 Loaded ${candleHistory.length} candles`);
    }
  } catch (e) { console.log(`⚠ loadCandles: ${e.message}`); }
}

function saveEngineState() {
  try {
    fs.writeFileSync(STATE_FILE, JSON.stringify({
      predictions: predictions.slice(-5000),
      activePending, activeTrade, lastSignalIdx, signalCount, engineParams
    }));
  } catch (e) { console.log(`⚠ saveState: ${e.message}`); }
}

function loadEngineState() {
  try {
    if (fs.existsSync(STATE_FILE)) {
      const data = JSON.parse(fs.readFileSync(STATE_FILE, 'utf8'));
      predictions = data.predictions || [];
      activePending = data.activePending;
      activeTrade = data.activeTrade;
      lastSignalIdx = data.lastSignalIdx ?? -999;
      signalCount = data.signalCount ?? predictions.length;
      if (data.engineParams) engineParams = { ...engineParams, ...data.engineParams };
      console.log(`📂 Loaded engine state: ${predictions.length} predictions, signalCount=${signalCount}`);
    }
  } catch (e) { console.log(`⚠ loadState: ${e.message}`); }
}

function saveTrackRecord() {
  try { fs.writeFileSync(TRACK_FILE, JSON.stringify(trackRecord.slice(-5000))); }
  catch (e) { console.log(`⚠ saveTrackRecord: ${e.message}`); }
}

function loadTrackRecord() {
  try {
    if (fs.existsSync(TRACK_FILE)) {
      trackRecord = JSON.parse(fs.readFileSync(TRACK_FILE, 'utf8'));
      console.log(`📂 Loaded ${trackRecord.length} track record entries`);
    }
  } catch (e) { console.log(`⚠ loadTrackRecord: ${e.message}`); }
}

// ═══════════════════════════════════════════════════════
// AUTH
// ═══════════════════════════════════════════════════════

function checkAuth(req) {
  const sec = req.headers['x-secret'] || req.query.secret || req.body?.secret;
  return sec === WEBHOOK_SECRET;
}

// ═══════════════════════════════════════════════════════
// ROUTES
// ═══════════════════════════════════════════════════════

// Health check
app.get('/', (req, res) => {
  const last = candleHistory.length > 0 ? candleHistory[candleHistory.length - 1] : null;
  res.json({
    status: 'ok', instrument: INSTRUMENT, engine: 'v13-server',
    candles: candleHistory.length,
    predictions: predictions.length,
    lastCandle: last ? last.t || last.bucket : null,
    activeTrade: activeTrade ? `${activeTrade.dir} #${activeTrade.id} @ ${activeTrade.entry}` : null,
    activePending: activePending ? `${activePending.dir} #${activePending.id} @ ${activePending.entry}` : null,
    params: engineParams,
    uptime: process.uptime()
  });
});

// Webhook: candle + engine tick
app.post('/webhook', (req, res) => {
  if (!checkAuth(req)) return res.status(401).json({ error: 'Unauthorized' });
  try {
    const data = req.body;
    let barTimeMs = null;
    if (data.bt) { try { barTimeMs = parseInt(data.bt); } catch (e) {} delete data.bt; }

    const norm = normalize(data);
    const tfRaw = norm._tf_data || {};
    delete norm._tf_data;
    for (const [tf, c] of Object.entries(tfRaw)) { if (c) tfData[tf] = c; }

    const now = new Date();
    norm.received_at = now.toISOString();

    let bucket;
    if (barTimeMs) {
      const barDt = new Date(barTimeMs);
      bucket = barDt.toISOString().slice(0, 16).replace('T', ' ');
      norm.bar_time = barDt.toISOString();
    } else {
      bucket = now.toISOString().slice(0, 16).replace('T', ' ');
    }
    norm.bucket = bucket;
    norm.t = bucket; // for engine compatibility

    // Dedup
    let existingIdx = null;
    for (let i = candleHistory.length - 1; i >= Math.max(0, candleHistory.length - 10); i--) {
      if (candleHistory[i].bucket === bucket) { existingIdx = i; break; }
    }

    if (existingIdx !== null) {
      candleHistory[existingIdx] = norm;
    } else {
      candleHistory.push(norm);
      candleHistory.sort((a, b) => (a.bucket || '').localeCompare(b.bucket || ''));
      if (candleHistory.length > MAX_HISTORY) candleHistory = candleHistory.slice(-MAX_HISTORY);
    }

    // Save periodically
    if (candleHistory.length % 5 === 0) saveCandles();

    // ★ RUN ENGINE TICK
    engineTick();

    console.log(`[${bucket}] C=${norm.c} | ${existingIdx !== null ? 'UPD' : 'NEW'} | candles=${candleHistory.length} | trade=${activeTrade ? 'OPEN' : (activePending ? 'PEND' : 'FREE')}`);
    res.json({ status: 'ok', candles: candleHistory.length, bucket, engine: activeTrade ? 'trade_open' : (activePending ? 'pending' : 'scanning') });
  } catch (e) {
    console.error(`✗ webhook: ${e.message}`);
    res.status(500).json({ error: e.message });
  }
});

// Import history
app.post('/import_history', (req, res) => {
  if (!checkAuth(req)) return res.status(401).json({ error: 'Unauthorized' });
  try {
    const candles = req.body.candles || [];
    let added = 0;
    const existingBuckets = new Set(candleHistory.map(c => c.bucket || c.t));
    for (const c of candles) {
      const bucket = c.bucket || c.t;
      if (!existingBuckets.has(bucket)) {
        c.bucket = bucket; c.t = bucket;
        candleHistory.push(c);
        existingBuckets.add(bucket);
        added++;
      }
    }
    candleHistory.sort((a, b) => (a.bucket || '').localeCompare(b.bucket || ''));
    if (candleHistory.length > MAX_HISTORY) candleHistory = candleHistory.slice(-MAX_HISTORY);
    saveCandles();
    console.log(`Import: +${added} candles (total ${candleHistory.length})`);
    res.json({ status: 'ok', added, total: candleHistory.length });
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

// Get candles
app.get('/candles', (req, res) => {
  const n = Math.min(parseInt(req.query.n || '500'), MAX_HISTORY);
  const seen = new Set();
  const deduped = [];
  for (let i = candleHistory.length - 1; i >= Math.max(0, candleHistory.length - n); i--) {
    const b = candleHistory[i].bucket || candleHistory[i].t;
    if (!seen.has(b)) { seen.add(b); deduped.unshift(candleHistory[i]); }
  }
  res.json(deduped);
});

// Get latest
app.get('/latest', (req, res) => {
  const last = candleHistory[candleHistory.length - 1] || {};
  res.json({ latest: last, candles: candleHistory.length, tf_data: tfData });
});

// Get predictions
app.get('/predictions', (req, res) => {
  res.json(predictions.slice(-500));
});

// Get engine state
app.get('/state', (req, res) => {
  res.json({
    params: engineParams,
    activeTrade, activePending,
    lastSignalIdx, signalCount,
    candles: candleHistory.length,
    predictions: predictions.length,
    lastCandle: candleHistory.length > 0 ? candleHistory[candleHistory.length - 1].t : null
  });
});

// Set engine parameters
app.post('/params', (req, res) => {
  if (!checkAuth(req)) return res.status(401).json({ error: 'Unauthorized' });
  const p = req.body;
  if (p.tf) engineParams.tf = parseFloat(p.tf);
  if (p.sl) engineParams.sl = parseFloat(p.sl);
  if (p.tp) engineParams.tp = parseFloat(p.tp);
  if (p.atrMax) engineParams.atrMax = parseFloat(p.atrMax);
  if (p.maxBars) engineParams.maxBars = parseInt(p.maxBars);
  if (p.minScore) engineParams.minScore = parseInt(p.minScore);
  if (p.htfOn !== undefined) engineParams.htfOn = p.htfOn === true || p.htfOn === 'true';
  if (p.dirMode) engineParams.dirMode = p.dirMode;
  if (p.cooldown) engineParams.cooldown = parseInt(p.cooldown);
  if (p.contracts) engineParams.contracts = parseInt(p.contracts);
  if (p.commission) engineParams.commission = parseFloat(p.commission);
  if (p.skipHours) engineParams.skipHours = Array.isArray(p.skipHours) ? p.skipHours : [];
  if (p.skipScores) engineParams.skipScores = Array.isArray(p.skipScores) ? p.skipScores : [];
  saveEngineState();
  console.log(`Params updated: TF=${engineParams.tf} SL=${engineParams.sl} TP=${engineParams.tp} ATR=${engineParams.atrMax} Bars=${engineParams.maxBars} Score=${engineParams.minScore} HTF=${engineParams.htfOn}`);
  res.json({ status: 'ok', params: engineParams });
});

// Get track record
app.get('/trackrecord', (req, res) => {
  res.json(trackRecord);
});

// Clear track record
app.post('/trackrecord/clear', (req, res) => {
  if (!checkAuth(req)) return res.status(401).json({ error: 'Unauthorized' });
  trackRecord = [];
  saveTrackRecord();
  res.json({ status: 'ok' });
});

// Clear data
app.post('/clear', (req, res) => {
  if (!checkAuth(req)) return res.status(401).json({ error: 'Unauthorized' });
  const keepPreds = req.body?.keep_preds;
  candleHistory = [];
  tfData = { '1': {}, '5': {}, '15': {}, '30': {}, '60': {} };
  if (!keepPreds) {
    predictions = [];
    activePending = null;
    activeTrade = null;
    lastSignalIdx = -999;
    signalCount = 0;
  }
  saveCandles();
  saveEngineState();
  res.json({ status: 'ok' });
});

// ═══════════════════════════════════════════════════════
// START
// ═══════════════════════════════════════════════════════

loadCandles();
loadEngineState();
loadTrackRecord();

app.listen(PORT, () => {
  console.log(`\n${'═'.repeat(60)}`);
  console.log(`  ${INSTRUMENT} Oracle Server v2 — Node.js + v13 Engine`);
  console.log(`  Port: ${PORT}`);
  console.log(`  Tick: ${TICK_SIZE} | Point: ${CURRENCY}${PT_VALUE}`);
  console.log(`  Candles: ${candleHistory.length} | Predictions: ${predictions.length}`);
  console.log(`  Engine: TF=${engineParams.tf} SL=${engineParams.sl} TP=${engineParams.tp}`);
  console.log(`  ntfy: ${NTFY_TOPIC || 'disabled'}`);
  console.log(`  Trade: ${activeTrade ? 'OPEN #' + activeTrade.id : (activePending ? 'PENDING #' + activePending.id : 'FREE')}`);
  console.log(`${'═'.repeat(60)}\n`);
});
