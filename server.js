/**
 * DAX Oracle Server v3 — 4 Engines + Auto Grid Search + Regime
 * =============================================================
 * 4 parallelle engines (OFF/BAL/QUAL/STRICT), elk met:
 *   - Eigen skip hours/scores
 *   - Eigen actieve trade/pending
 *   - Eigen predictions + track record
 *   - Auto regime-wissel per sessie
 *
 * Nachtelijke grid search (00:00) over alle data → beste params per sessie per filter.
 * Push notificaties via ntfy.sh bij signaal + trade close.
 */

const express = require('express');
const cors = require('cors');
const fs = require('fs');
const path = require('path');
const https = require('https');

const app = express();
app.use(cors());
app.use(express.json({ limit: '50mb' }));
app.use(express.urlencoded({ extended: true, limit: '50mb' }));

// ═══════════════════════════════════════════════════════
// CONFIG
// ═══════════════════════════════════════════════════════

const PORT = process.env.PORT || 8889;
const WEBHOOK_SECRET = process.env.WEBHOOK_SECRET || 'DAXsecret2024';
const NTFY_TOPIC = process.env.NTFY_TOPIC || 'mathieu-dax-oracle';
const TICK_SIZE = parseFloat(process.env.TICK_SIZE || '0.5');
const PT_VALUE = parseFloat(process.env.PT_VALUE || '25');
const CURRENCY = process.env.CURRENCY || '€';
const INSTRUMENT = process.env.INSTRUMENT || 'DAX';
const MAX_HISTORY = 100000;
const DATA_DIR = process.env.DATA_DIR || '/tmp';
const GRID_SEARCH_HOUR = 0; // 00:00 UTC = 02:00 Belgisch (zomer)

// ═══════════════════════════════════════════════════════
// FILTER PRESETS
// ═══════════════════════════════════════════════════════

const FILTER_PRESETS = {
  OFF:    { skipScores: [],    skipHours: [],         setupMode: 'all' },
  BAL:    { skipScores: [6],   skipHours: [18,19],    setupMode: 'all' },
  QUAL:   { skipScores: [3,6], skipHours: [16,18,19], setupMode: 'real' },
  STRICT: { skipScores: [3,6], skipHours: [16,18,19], setupMode: 'real' },
};

// ═══════════════════════════════════════════════════════
// SESSIONS (Belgische uren)
// ═══════════════════════════════════════════════════════

const SESSIONS = [
  {id:'asia',      name:'Azië/Pre-EU',  hours:[0,1,2,3,4,5,6,7],   regime:'low_vol_range'},
  {id:'eu_pre',    name:'EU Pre-Open',  hours:[8],                  regime:'vol_spike'},
  {id:'eu_morning',name:'EU Ochtend',   hours:[9,10,11],            regime:'trending'},
  {id:'eu_lunch',  name:'EU Lunch',     hours:[12,13,14],           regime:'range_chop'},
  {id:'us_data',   name:'US Data/Pre',  hours:[15],                 regime:'vol_spike'},
  {id:'us_open',   name:'US Open',      hours:[16],                 regime:'trending'},
  {id:'us_chop',   name:'Late/Chop',    hours:[17,18],              regime:'chop_fade'},
  {id:'us_drift',  name:'US Drift',     hours:[19,20,21],           regime:'low_vol_drift'},
  {id:'overnight', name:'Overnight',    hours:[22,23],              regime:'low_vol_range'},
];

function getSessionForHour(h) {
  return SESSIONS.find(s => s.hours.includes(h)) || SESSIONS[0];
}

// ═══════════════════════════════════════════════════════
// STATE
// ═══════════════════════════════════════════════════════

let candleHistory = [];
let tfData = { '1':{},'5':{},'15':{},'30':{},'60':{} };
let trackRecord = [];
let gridSearchResults = {}; // {filterName: {sessionId: {params, stats}}}
let lastGridSearchTime = null;

// Basis engine params (grid search overschrijft per sessie)
const BASE_PARAMS = {
  tf:5, sl:1.0, tp:1.5, atrMax:45, maxBars:19,
  minScore:4, htfOn:true, dirMode:'both',
  cooldown:15, contracts:1, commission: parseFloat(process.env.COMMISSION || '3.60'),
};

// ═══════════════════════════════════════════════════════
// HELPERS
// ═══════════════════════════════════════════════════════

function r2(v) { return Math.round(v*100)/100; }
function snapTick(v) { return Math.round(v/TICK_SIZE)*TICK_SIZE; }
function snapStopBull(v) { return Math.floor(v/TICK_SIZE)*TICK_SIZE; }
function snapStopBear(v) { return Math.ceil(v/TICK_SIZE)*TICK_SIZE; }
function snapTgtBull(v) { return Math.floor(v/TICK_SIZE)*TICK_SIZE; }
function snapTgtBear(v) { return Math.ceil(v/TICK_SIZE)*TICK_SIZE; }

function calcRollingHTF(candles, endIdx, period) {
  const s = endIdx-period+1;
  if(s<0||endIdx>=candles.length) return null;
  const f=candles[s]; let h=f.h,l=f.l,vol=0;
  for(let i=s;i<=endIdx;i++){if(candles[i].h>h)h=candles[i].h;if(candles[i].l<l)l=candles[i].l;vol+=candles[i].v||0;}
  return {t:candles[endIdx].t, o:f.o, h, l, c:candles[endIdx].c, v:vol};
}

function emaUpdate(prev, val, period) {
  if(prev==null) return val;
  const k=2/(period+1);
  return val*k+prev*(1-k);
}

function utcToLocalHour(utcStr) {
  if(!utcStr||utcStr.length<16) return -1;
  const d=new Date(utcStr.replace(' ','T')+':00Z');
  return isNaN(d)?parseInt(utcStr.slice(11,13)):d.getHours();
}

function nowIso() { return new Date().toISOString().slice(0,16).replace('T',' '); }

function normalize(data) {
  const out={}, tfRaw={};
  for(const [k,v] of Object.entries(data)){
    const kl=k.toLowerCase();
    if(['open','o'].includes(kl)) out.o=parseFloat(v);
    else if(['high','h'].includes(kl)) out.h=parseFloat(v);
    else if(['low','l'].includes(kl)) out.l=parseFloat(v);
    else if(['close','c'].includes(kl)) out.c=parseFloat(v);
    else if(['volume','v','vol'].includes(kl)) out.v=parseFloat(v)||0;
    else if(kl.startsWith('tf_')){try{tfRaw[kl.replace('tf_','').replace('_','')]=typeof v==='string'?JSON.parse(v):v;}catch(e){}}
  }
  out._tf_data=tfRaw; return out;
}

// ═══════════════════════════════════════════════════════
// v13 SIGNAL DETECTION (one-shot op laatste candle)
// ═══════════════════════════════════════════════════════

function detectSignal(candles, params) {
  const tf=params.tf, N=candles.length;
  if(N<tf*60) return null;
  const rollingHTF=new Array(N).fill(null);
  for(let i=tf-1;i<N;i++) rollingHTF[i]=calcRollingHTF(candles,i,tf);
  const atrs=new Array(N).fill(0),e8=new Array(N).fill(null),e21=new Array(N).fill(null),e50=new Array(N).fill(null);
  const rsis=new Array(N).fill(50),vwaps=new Array(N).fill(null);
  let avgG=0,avgL=0,rI=false,cPV=0,cV=0,pD=null;
  for(let i=tf-1;i<N;i++){
    const htf=rollingHTF[i]; if(!htf)continue;
    const tr=htf.h-htf.l; atrs[i]=i===tf-1?tr:(atrs[i-1]*13+tr)/14;
    e8[i]=emaUpdate(e8[i-1],htf.c,8); e21[i]=emaUpdate(e21[i-1],htf.c,21); e50[i]=emaUpdate(e50[i-1],htf.c,50);
    if(i>tf-1){const p=rollingHTF[i-1];if(p){const ch=htf.c-p.c;const g=ch>0?ch:0,l=ch<0?-ch:0;if(!rI){avgG=g;avgL=l;rI=true;}else{avgG=(avgG*13+g)/14;avgL=(avgL*13+l)/14;}rsis[i]=avgL===0?100:(100-100/(1+avgG/avgL));}}
    const day=htf.t.slice(0,10);if(pD!==day){cPV=0;cV=0;pD=day;}
    const tp2=(htf.h+htf.l+htf.c)/3,vol=htf.v||1;cPV+=tp2*vol;cV+=vol;vwaps[i]=cV>0?cPV/cV:tp2;
  }
  const ri=N-1, htf=rollingHTF[ri-1], atr=atrs[ri-1];
  if(!htf||!atr||atr<=0||atr>params.atrMax) return null;
  const p1=rollingHTF[ri-2],p2=rollingHTF[ri-3],p3=rollingHTF[ri-4];
  if(!p1||!p2) return null;
  const em8=e8[ri-1],em21=e21[ri-1],em50=e50[ri-1],rsi=rsis[ri-1],vwap=vwaps[ri-1];
  if(em8==null||em21==null||vwap==null) return null;
  const lb=Math.max(tf,ri-15*tf);
  const hB=params.htfOn?(em21>(e21[lb]||em21)):true, hR=params.htfOn?(em21<(e21[lb]||em21)):true;
  let swH=htf.h,swL=htf.l;
  for(let j=ri-10;j<ri-1;j++){const r=rollingHTF[j];if(r){if(r.h>swH)swH=r.h;if(r.l<swL)swL=r.l;}}
  let bS=0,rS=0,bSt='none',rSt='none';
  if(em8>em21&&em21>(em50||em21))bS+=3;else if(em8>em21)bS+=1;
  if(em8<em21&&em21<(em50||em21))rS+=3;else if(em8<em21)rS+=1;
  if(htf.c>vwap&&p1.c<=vwap)bS+=2;else if(htf.c>vwap)bS+=1;
  if(htf.c<vwap&&p1.c>=vwap)rS+=2;else if(htf.c<vwap)rS+=1;
  if(rsi<35)bS+=2;else if(rsi<45)bS+=1;
  if(rsi>65)rS+=2;else if(rsi>55)rS+=1;
  const bSw=htf.l<p1.l&&htf.l<p2.l&&htf.c>p1.l&&htf.c>htf.o;
  const rSw=htf.h>p1.h&&htf.h>p2.h&&htf.c<p1.h&&htf.c<htf.o;
  if(bSw){bS+=4;bSt='liquidity_sweep';}if(rSw){rS+=4;rSt='liquidity_sweep';}
  const ref=p3||p2;
  if(p2.c>p2.o&&(p2.c-p2.o)>atr*0.5&&htf.l<=ref.h&&htf.l>=ref.l&&htf.c>htf.o&&em8>em21){bS+=3;if(bSt==='none')bSt='ob_retest';}
  if(p2.c<p2.o&&(p2.o-p2.c)>atr*0.5&&htf.h>=ref.l&&htf.h<=ref.h&&htf.c<htf.o&&em8<em21){rS+=3;if(rSt==='none')rSt='ob_retest';}
  if(htf.l>p2.h&&htf.c>=p2.h&&htf.c<=htf.h&&em8>em21){bS+=2;if(bSt==='none')bSt='fvg_fill';}
  if(htf.h<p2.l&&htf.c<=p2.l&&htf.c>=htf.l&&em8<em21){rS+=2;if(rSt==='none')rSt='fvg_fill';}
  if(htf.c>swH&&htf.c>htf.o&&(htf.c-htf.o)>atr*0.3){bS+=2;if(bSt==='none')bSt='bos';}
  if(htf.c<swL&&htf.c<htf.o&&(htf.o-htf.c)>atr*0.3){rS+=2;if(rSt==='none')rSt='bos';}
  let aV=0,aN=0;for(let j=Math.max(tf,ri-10);j<ri;j++){if(rollingHTF[j]){aV+=rollingHTF[j].v;aN++;}}
  aV=aN>0?aV/aN:htf.v;if(htf.v>aV*1.3){if(htf.c>htf.o)bS+=1;else rS+=1;}
  if(!hB)bS=Math.max(0,bS-3);if(!hR)rS=Math.max(0,rS-3);
  let dir=null,score=0,setup='none';
  if(params.dirMode!=='short'&&bS>rS){dir='bull';score=bS;setup=bSt;}
  else if(params.dirMode!=='long'&&rS>bS){dir='bear';score=rS;setup=rSt;}
  if(!dir||score<params.minScore) return null;
  const slSz=params.sl*atr,tpSz=slSz*params.tp,entry=snapTick(htf.c);
  let stop,tgt;
  if(dir==='bull'){stop=snapStopBull(entry-slSz);tgt=snapTgtBull(entry+tpSz);}
  else{stop=snapStopBear(entry+slSz);tgt=snapTgtBear(entry-tpSz);}
  return {dir,score,setup,entry,stop,tgt,rr:params.tp,atr:r2(atr),signalTime:candles[ri-1].t};
}

// ═══════════════════════════════════════════════════════
// GRID SEARCH ENGINE (mini-backtest)
// ═══════════════════════════════════════════════════════

function gridSearchEngine(candles, params, filterPreset) {
  const tf=params.tf, N=candles.length, skipH=filterPreset.skipHours, skipS=filterPreset.skipScores;
  if(N<tf*60) return null;
  const rHTF=new Array(N).fill(null);
  for(let i=tf-1;i<N;i++) rHTF[i]=calcRollingHTF(candles,i,tf);
  const atrs=new Array(N).fill(0),e8=new Array(N).fill(null),e21=new Array(N).fill(null),e50=new Array(N).fill(null);
  const rsis=new Array(N).fill(50),vwaps=new Array(N).fill(null);
  let aG=0,aL=0,rI=false,cPV=0,cV=0,pD=null;
  for(let i=tf-1;i<N;i++){
    const h=rHTF[i];if(!h)continue;const tr=h.h-h.l;atrs[i]=i===tf-1?tr:(atrs[i-1]*13+tr)/14;
    e8[i]=emaUpdate(e8[i-1],h.c,8);e21[i]=emaUpdate(e21[i-1],h.c,21);e50[i]=emaUpdate(e50[i-1],h.c,50);
    if(i>tf-1){const p=rHTF[i-1];if(p){const ch=h.c-p.c;const g=ch>0?ch:0,l=ch<0?-ch:0;if(!rI){aG=g;aL=l;rI=true;}else{aG=(aG*13+g)/14;aL=(aL*13+l)/14;}rsis[i]=aL===0?100:(100-100/(1+aG/aL));}}
    const day=h.t.slice(0,10);if(pD!==day){cPV=0;cV=0;pD=day;}const tp2=(h.h+h.l+h.c)/3,vol=h.v||1;cPV+=tp2*vol;cV+=vol;vwaps[i]=cV>0?cPV/cV:tp2;
  }
  let aT=null,aP=null,lSI=-999;const trades=[];const commPts=params.commission/PT_VALUE;const pTO=3*tf;
  for(let ri=tf;ri<N;ri++){
    const rc=candles[ri];
    if(aT){let ex=null;if(aT.dir==='bull'){if(rc.l<=aT.stop)ex={o:'LOSS',p:aT.stop};else if(rc.h>=aT.tgt)ex={o:'WIN',p:aT.tgt};}else{if(rc.h>=aT.stop)ex={o:'LOSS',p:aT.stop};else if(rc.l<=aT.tgt)ex={o:'WIN',p:aT.tgt};}aT.bars++;if(!ex&&aT.bars>=params.maxBars*tf)ex={o:'EXPIRED',p:rc.c};if(ex){const gr=aT.dir==='bull'?ex.p-aT.entry:aT.entry-ex.p;trades.push({outcome:ex.o,pnlPt:r2(gr-commPts),dir:aT.dir,setup:aT.setup,score:aT.score,entry:aT.entry,tgt:aT.tgt,stp:aT.stop,signalTime:aT.signalTime,entryTime:aT.entryTime,exitTime:rc.t,sigHour:aT.sigHour||0});lSI=ri;aT=null;}continue;}
    if(aP){let filled=false;if(aP.dir==='bull'&&rc.h>=aP.entry)filled=true;if(aP.dir==='bear'&&rc.l<=aP.entry)filled=true;aP.bars++;if(filled){aT={...aP,entryTime:rc.t,bars:0};let ds=false,dt=false;if(aP.dir==='bull'){if(rc.l<=aP.stop)ds=true;else if(rc.h>=aP.tgt)dt=true;}else{if(rc.h>=aP.stop)ds=true;else if(rc.l<=aP.tgt)dt=true;}if(ds||dt){const ep=ds?aT.stop:aT.tgt;const gr=aT.dir==='bull'?ep-aT.entry:aT.entry-ep;trades.push({outcome:ds?'LOSS':'WIN',pnlPt:r2(gr-commPts),dir:aT.dir,setup:aT.setup,score:aT.score,entry:aT.entry,tgt:aT.tgt,stp:aT.stop,signalTime:aT.signalTime,entryTime:rc.t,exitTime:rc.t,sigHour:aT.sigHour||0});lSI=ri;aT=null;}aP=null;}else if(aP.bars>=pTO){lSI=ri;aP=null;}continue;}
    if(ri-lSI<tf) continue;
    const htf=rHTF[ri-1],atr=atrs[ri-1];if(!htf||!atr||atr<=0||atr>params.atrMax)continue;
    const p1=rHTF[ri-2],p2=rHTF[ri-3],p3=rHTF[ri-4];if(!p1||!p2)continue;
    const em8=e8[ri-1],em21=e21[ri-1],em50=e50[ri-1],rsi=rsis[ri-1],vwap=vwaps[ri-1];
    if(em8==null||em21==null||vwap==null)continue;
    const lb=Math.max(tf,ri-15*tf);const hB=params.htfOn?(em21>(e21[lb]||em21)):true,hR=params.htfOn?(em21<(e21[lb]||em21)):true;
    let swH=htf.h,swL=htf.l;for(let j=ri-10;j<ri-1;j++){const r=rHTF[j];if(r){if(r.h>swH)swH=r.h;if(r.l<swL)swL=r.l;}}
    let bS=0,rS=0,bSt='none',rSt='none';
    if(em8>em21&&em21>(em50||em21))bS+=3;else if(em8>em21)bS+=1;if(em8<em21&&em21<(em50||em21))rS+=3;else if(em8<em21)rS+=1;
    if(htf.c>vwap&&p1.c<=vwap)bS+=2;else if(htf.c>vwap)bS+=1;if(htf.c<vwap&&p1.c>=vwap)rS+=2;else if(htf.c<vwap)rS+=1;
    if(rsi<35)bS+=2;else if(rsi<45)bS+=1;if(rsi>65)rS+=2;else if(rsi>55)rS+=1;
    if(htf.l<p1.l&&htf.l<p2.l&&htf.c>p1.l&&htf.c>htf.o){bS+=4;bSt='liquidity_sweep';}
    if(htf.h>p1.h&&htf.h>p2.h&&htf.c<p1.h&&htf.c<htf.o){rS+=4;rSt='liquidity_sweep';}
    const ref=p3||p2;
    if(p2.c>p2.o&&(p2.c-p2.o)>atr*0.5&&htf.l<=ref.h&&htf.l>=ref.l&&htf.c>htf.o&&em8>em21){bS+=3;if(bSt==='none')bSt='ob_retest';}
    if(p2.c<p2.o&&(p2.o-p2.c)>atr*0.5&&htf.h>=ref.l&&htf.h<=ref.h&&htf.c<htf.o&&em8<em21){rS+=3;if(rSt==='none')rSt='ob_retest';}
    if(htf.l>p2.h&&htf.c>=p2.h&&em8>em21){bS+=2;if(bSt==='none')bSt='fvg_fill';}
    if(htf.h<p2.l&&htf.c<=p2.l&&em8<em21){rS+=2;if(rSt==='none')rSt='fvg_fill';}
    if(htf.c>swH&&htf.c>htf.o&&(htf.c-htf.o)>atr*0.3){bS+=2;if(bSt==='none')bSt='bos';}
    if(htf.c<swL&&htf.c<htf.o&&(htf.o-htf.c)>atr*0.3){rS+=2;if(rSt==='none')rSt='bos';}
    let aV=0,aN=0;for(let j=Math.max(tf,ri-10);j<ri;j++){if(rHTF[j]){aV+=rHTF[j].v;aN++;}}aV=aN>0?aV/aN:htf.v;
    if(htf.v>aV*1.3){if(htf.c>htf.o)bS+=1;else rS+=1;}
    if(!hB)bS=Math.max(0,bS-3);if(!hR)rS=Math.max(0,rS-3);
    let dir=null,score=0,setup='none';
    if(params.dirMode!=='short'&&bS>rS){dir='bull';score=bS;setup=bSt;}
    else if(params.dirMode!=='long'&&rS>bS){dir='bear';score=rS;setup=rSt;}
    if(!dir||score<params.minScore)continue;
    const sigH=utcToLocalHour(candles[ri-1].t);
    lSI=ri;const slSz=params.sl*atr,tpSz=slSz*params.tp,ep=snapTick(htf.c);
    let stop,tgt;if(dir==='bull'){stop=snapStopBull(ep-slSz);tgt=snapTgtBull(ep+tpSz);}else{stop=snapStopBear(ep+slSz);tgt=snapTgtBear(ep-tpSz);}
    aP={dir,score,setup,entry:ep,stop,tgt,signalTime:candles[ri-1].t,bars:0,sigHour:sigH};
  }
  // Post-filter
  const ft=trades.filter(t=>!skipH.includes(t.sigHour)&&!skipS.includes(t.score));
  const n=ft.length;if(n===0)return{n:0,wr:0,pnl:0,ev:0,pf:0,dd:0,wins:0,losses:0,trades:ft};
  const wins=ft.filter(t=>t.outcome==='WIN'),losses=ft.filter(t=>t.outcome==='LOSS');
  const pnl=ft.reduce((s,t)=>s+t.pnlPt,0);
  const gW=wins.reduce((s,t)=>s+t.pnlPt,0),gL=Math.abs(losses.reduce((s,t)=>s+t.pnlPt,0));
  let mDD=0,pk=0,cm=0;ft.forEach(t=>{cm+=t.pnlPt;if(cm>pk)pk=cm;const dd=pk-cm;if(dd>mDD)mDD=dd;});
  return{n,wr:wins.length/n,pnl:r2(pnl),ev:r2(pnl/n),pf:gL>0?r2(gW/gL):99,dd:r2(mDD),wins:wins.length,losses:losses.length,trades:ft};
}

// ═══════════════════════════════════════════════════════
// ENGINE INSTANCE (one per filter)
// ═══════════════════════════════════════════════════════

class EngineInstance {
  constructor(filterName, filterPreset) {
    this.filterName = filterName;
    this.filter = filterPreset;
    this.params = { ...BASE_PARAMS };
    this.activeTrade = null;
    this.activePending = null;
    this.lastSignalIdx = -999;
    this.signalCount = 0;
    this.predictions = [];
    this.currentSessionId = null;
    this.pendingSwitch = null;
  }

  tick(candles) {
    const N = candles.length;
    if (N < this.params.tf * 10) return;
    const rc = candles[N-1], ri = N-1;
    const commPts = this.params.commission / PT_VALUE;
    const pTO = 3 * this.params.tf;

    // 1. Active trade exit
    if (this.activeTrade) {
      let ex = null;
      const at = this.activeTrade;
      if (at.dir==='bull') { if(rc.l<=at.stop)ex={o:'LOSS',p:at.stop};else if(rc.h>=at.tgt)ex={o:'WIN',p:at.tgt}; }
      else { if(rc.h>=at.stop)ex={o:'LOSS',p:at.stop};else if(rc.l<=at.tgt)ex={o:'WIN',p:at.tgt}; }
      at.barsOpen = (at.barsOpen||0)+1;
      if (!ex && at.barsOpen >= this.params.maxBars * this.params.tf) ex={o:'EXPIRED',p:rc.c};
      if (ex) {
        const gr = at.dir==='bull' ? ex.p-at.entry : at.entry-ex.p;
        const net = r2((gr-commPts)*(at.contracts||1));
        const p = this.predictions.find(x=>x.id===at.id);
        if(p){p.outcome=ex.o;p.exitTime=rc.t;p.pnlPt=net;p.pnlCur=r2(net*PT_VALUE);}
        this.lastSignalIdx = ri;
        this.logTrack(p||at, ex);
        sendPush(`[${this.filterName}] ${ex.o} ${at.dir==='bull'?'▲':'▼'} ${net>0?'+':''}${net}pt (${CURRENCY}${r2(net*PT_VALUE)})`, ex.o==='WIN'?'✅':'❌');
        this.activeTrade = null;
        this.checkPendingSwitch(candles);
      }
      return;
    }

    // 2. Pending fill
    if (this.activePending) {
      const ap = this.activePending;
      let filled = false;
      if(ap.dir==='bull'&&rc.h>=ap.entry)filled=true;
      if(ap.dir==='bear'&&rc.l<=ap.entry)filled=true;
      ap.barsWaiting = (ap.barsWaiting||0)+1;
      if (filled) {
        this.activeTrade = {...ap, entryTime:rc.t, barsOpen:0};
        const p = this.predictions.find(x=>x.id===ap.id);
        if(p){p.outcome='open';p.entryTime=rc.t;}
        let ds=false,dt=false;
        if(ap.dir==='bull'){if(rc.l<=ap.stop)ds=true;else if(rc.h>=ap.tgt)dt=true;}
        else{if(rc.h>=ap.stop)ds=true;else if(rc.l<=ap.tgt)dt=true;}
        if(ds||dt){
          const ep=ds?this.activeTrade.stop:this.activeTrade.tgt;
          const gr=this.activeTrade.dir==='bull'?ep-this.activeTrade.entry:this.activeTrade.entry-ep;
          const net=r2((gr-commPts)*(this.activeTrade.contracts||1));
          const p2=this.predictions.find(x=>x.id===this.activeTrade.id);
          if(p2){p2.outcome=ds?'LOSS':'WIN';p2.exitTime=rc.t;p2.pnlPt=net;p2.pnlCur=r2(net*PT_VALUE);}
          this.logTrack(p2||this.activeTrade,{outcome:ds?'LOSS':'WIN',price:ep});
          sendPush(`[${this.filterName}] ${ds?'LOSS':'WIN'} ${this.activeTrade.dir==='bull'?'▲':'▼'} ${net>0?'+':''}${net}pt`,ds?'❌':'✅');
          this.lastSignalIdx=ri; this.activeTrade=null; this.checkPendingSwitch(candles);
        }
        this.activePending = null;
      } else if(ap.barsWaiting>=pTO){
        const p=this.predictions.find(x=>x.id===ap.id);
        if(p)p.outcome='expired';
        this.lastSignalIdx=ri; this.activePending=null; this.checkPendingSwitch(candles);
      }
      return;
    }

    // 3. Cooldown
    if(ri-this.lastSignalIdx < this.params.cooldown) return;

    // 4. Detect signal
    const sig = detectSignal(candles, this.params);
    if (!sig) return;

    // Apply filter
    const sigH = utcToLocalHour(sig.signalTime);
    if (this.filter.skipHours.includes(sigH)) return;
    if (this.filter.skipScores.includes(sig.score)) return;
    if (this.filter.setupMode==='real' && sig.setup==='none') return;

    // Create pending
    this.lastSignalIdx = ri;
    this.signalCount++;
    this.activePending = { id:this.signalCount, ...sig, barsWaiting:0, contracts:this.params.contracts, status:'pending' };
    this.predictions.push({...this.activePending, outcome:'pending', filter:this.filterName});
    console.log(`★ [${this.filterName}] #${this.signalCount} ${sig.dir.toUpperCase()} sc=${sig.score} ${sig.setup} entry=${sig.entry}`);
    sendPush(`[${this.filterName}] ${sig.dir==='bull'?'▲ LONG':'▼ SHORT'} sc=${sig.score} ${sig.setup}\nEntry: ${sig.entry}\nTP: ${sig.tgt} | SL: ${sig.stop}`, '🔔');
    
    // Forward to executor (VPS) if configured
    forwardToExecutor({
      instrument: INSTRUMENT === 'DAX' ? 'FDXM' : 'MNQ',  // Default mini contract
      dir: sig.dir, entry: sig.entry, stop: sig.stop, tgt: sig.tgt,
      score: sig.score, setup: sig.setup, filter: this.filterName,
      qty: this.params.contracts || 1
    });
  }

  // Regime: auto-switch params per session
  checkRegime(candles) {
    const h = new Date().getHours();
    const session = getSessionForHour(h);
    if (this.currentSessionId && this.currentSessionId !== session.id) {
      const best = (gridSearchResults[this.filterName]||{})[session.id];
      if (best) {
        if (this.activeTrade || this.activePending) {
          this.pendingSwitch = { params:best.params, sessionName:session.name };
          console.log(`⚠ [${this.filterName}] Sessie→${session.name} maar trade open — uitgesteld`);
        } else {
          this.applyParams(best.params);
          console.log(`🔄 [${this.filterName}] Auto-apply ${session.name}: SL=${best.params.sl} TP=${best.params.tp}`);
        }
      } else {
        console.log(`🕐 [${this.filterName}] Sessie→${session.name} (geen grid data)`);
      }
    }
    this.currentSessionId = session.id;
  }

  checkPendingSwitch(candles) {
    if (!this.pendingSwitch) return;
    if (this.activeTrade || this.activePending) return;
    const sw = this.pendingSwitch;
    this.pendingSwitch = null;
    this.applyParams(sw.params);
    console.log(`🔄 [${this.filterName}] Uitgestelde wissel→${sw.sessionName}: SL=${sw.params.sl} TP=${sw.params.tp}`);
  }

  applyParams(p) {
    if(p.sl) this.params.sl=p.sl;
    if(p.tp) this.params.tp=p.tp;
    if(p.atrMax) this.params.atrMax=p.atrMax;
    if(p.maxBars) this.params.maxBars=p.maxBars;
    if(p.minScore) this.params.minScore=p.minScore;
    if(p.htfOn!==undefined) this.params.htfOn=p.htfOn;
    if(p.dirMode) this.params.dirMode=p.dirMode;
  }

  logTrack(trade, exit) {
    trackRecord.push({
      filter:this.filterName, dir:trade.dir, setup:trade.setup||'', score:trade.score||0,
      entry:trade.entry, tgt:trade.tgt, stp:trade.stop||trade.stp,
      outcome:exit.o||exit.outcome, pnlPt:trade.pnlPt||0, pnlCur:trade.pnlCur||0,
      signalTime:trade.signalTime, entryTime:trade.entryTime,
      exitTime:trade.exitTime||candleHistory[candleHistory.length-1]?.t,
      params:{...this.params}, logged:new Date().toISOString()
    });
  }

  getState() {
    return {
      filter:this.filterName, params:this.params,
      activeTrade:this.activeTrade, activePending:this.activePending,
      lastSignalIdx:this.lastSignalIdx, signalCount:this.signalCount,
      predictions:this.predictions.length,
      currentSession:this.currentSessionId
    };
  }
}

// Create 4 engine instances
const engines = {};
for (const [name, preset] of Object.entries(FILTER_PRESETS)) {
  engines[name] = new EngineInstance(name, preset);
}

// ═══════════════════════════════════════════════════════
// NIGHTLY GRID SEARCH
// ═══════════════════════════════════════════════════════

function runNightlyGridSearch() {
  const N = candleHistory.length;
  if (N < 3000) { console.log('Grid search: niet genoeg candles ('+N+')'); return; }
  console.log(`\n🔍 NACHTELIJKE GRID SEARCH — ${N} candles`);
  const t0 = Date.now();

  const tf = BASE_PARAMS.tf;
  const sls = [0.5,0.6,0.7,0.8,0.9,1.0,1.1,1.2,1.3,1.4,1.5];
  const tps = [1.0,1.1,1.2,1.3,1.4,1.5,1.6,1.7,1.8,1.9,2.0];
  const atrs = [22,26,30,45];
  const bars = [12,15,19,24];
  const scores = [4,5];
  const htfs = [true, false];
  const dirs = ['both'];
  const comm = BASE_PARAMS.commission;

  // Build param combos
  const combos = [];
  for(const sl of sls) for(const tp of tps) for(const atr of atrs) for(const mb of bars)
    for(const ms of scores) for(const htf of htfs) for(const dir of dirs) {
      combos.push({tf,sl,tp,atrMax:atr,maxBars:mb,minScore:ms,htfOn:htf,dirMode:dir,commission:comm,contracts:1,cooldown:tf});
    }

  console.log(`   ${combos.length} parameter-combinaties`);

  // Per session: groepeer candles
  const sessionCandles = {};
  SESSIONS.forEach(s => { sessionCandles[s.id] = []; });
  candleHistory.forEach(c => {
    const h = utcToLocalHour(c.t || c.bucket);
    const s = getSessionForHour(h);
    sessionCandles[s.id].push(c);
  });

  // Per filter + per session: zoek beste params
  for (const [filterName, preset] of Object.entries(FILTER_PRESETS)) {
    gridSearchResults[filterName] = {};

    // Globale grid search (alle candles)
    const globalResults = [];
    for (const p of combos) {
      const res = gridSearchEngine(candleHistory, p, preset);
      if (res && res.n >= 3) {
        const rank = res.ev * Math.sqrt(Math.max(1,res.n)) * (res.wr/0.5);
        globalResults.push({ params:p, stats:res, rank });
      }
    }
    globalResults.sort((a,b) => b.rank - a.rank);

    // Top-20 per sessie testen
    const top20 = globalResults.slice(0, 20);
    for (const session of SESSIONS) {
      const sc = sessionCandles[session.id];
      if (sc.length < tf * 30) continue;
      let best = null;
      for (const r of top20) {
        const res = gridSearchEngine(sc, r.params, preset);
        if (res && res.n >= 2) {
          const rank = res.ev * Math.sqrt(Math.max(1,res.n)) * (res.wr/0.5);
          if (!best || rank > best.rank) best = { params:r.params, stats:res, rank };
        }
      }
      if (best) gridSearchResults[filterName][session.id] = best;
    }

    const sessCount = Object.keys(gridSearchResults[filterName]).length;
    const topGlobal = globalResults[0];
    console.log(`   [${filterName}] ${sessCount} sessies | top: ${topGlobal ? `SL=${topGlobal.params.sl} TP=${topGlobal.params.tp} ${(topGlobal.stats.wr*100).toFixed(0)}%WR EV=${topGlobal.stats.ev}` : 'geen'}`);
  }

  lastGridSearchTime = new Date().toISOString();
  saveState();
  console.log(`✅ Grid search klaar in ${((Date.now()-t0)/1000).toFixed(1)}s\n`);

  // Apply regime for current session
  for (const eng of Object.values(engines)) eng.checkRegime(candleHistory);
}

// Schedule nightly grid search
let lastGridHour = -1;
setInterval(() => {
  const h = new Date().getUTCHours();
  if (h === GRID_SEARCH_HOUR && lastGridHour !== h) {
    lastGridHour = h;
    runNightlyGridSearch();
  }
  if (h !== GRID_SEARCH_HOUR) lastGridHour = -1;

  // Check regime every minute
  for (const eng of Object.values(engines)) eng.checkRegime(candleHistory);
}, 60000);

// ═══════════════════════════════════════════════════════
// PUSH NOTIFICATIONS
// ═══════════════════════════════════════════════════════

function sendPush(msg, emoji) {
  if (!NTFY_TOPIC) return;
  const data = `${emoji||'📊'} ${INSTRUMENT}\n${msg}`;
  const req = https.request({ hostname:'ntfy.sh', port:443, path:`/${NTFY_TOPIC}`, method:'POST',
    headers:{'Content-Type':'text/plain'} }, r => { if(r.statusCode!==200) console.log(`ntfy: ${r.statusCode}`); });
  req.on('error', e => console.log(`ntfy: ${e.message}`));
  req.write(data); req.end();
}

// Forward signaal naar VPS executor (als geconfigureerd)
const EXECUTOR_URL = process.env.EXECUTOR_URL || '';
const EXECUTOR_SECRET = process.env.EXECUTOR_SECRET || '';

function forwardToExecutor(signal) {
  if (!EXECUTOR_URL) return;
  const data = JSON.stringify({...signal, secret: EXECUTOR_SECRET});
  const url = new URL(EXECUTOR_URL + '/webhook/signal');
  const mod = url.protocol === 'https:' ? https : require('http');
  const req = mod.request({
    hostname: url.hostname, port: url.port || (url.protocol === 'https:' ? 443 : 80),
    path: url.pathname, method: 'POST',
    headers: { 'Content-Type': 'application/json', 'x-secret': EXECUTOR_SECRET }
  }, r => {
    let body = '';
    r.on('data', d => body += d);
    r.on('end', () => {
      try {
        const res = JSON.parse(body);
        if (res.error) console.log(`⚠ Executor: ${res.error}`);
        else console.log(`✅ Executor: order geplaatst #${res.parentOrderId||'?'} ${signal.instrument} ${signal.dir}`);
      } catch(e) { console.log(`⚠ Executor response: ${body.slice(0,100)}`); }
    });
  });
  req.on('error', e => console.log(`⚠ Executor fout: ${e.message}`));
  req.write(data);
  req.end();
}

// ═══════════════════════════════════════════════════════
// PERSISTENCE
// ═══════════════════════════════════════════════════════

const FILES = {
  candles: path.join(DATA_DIR, `${INSTRUMENT.toLowerCase()}_candles.json`),
  state: path.join(DATA_DIR, `${INSTRUMENT.toLowerCase()}_state_v3.json`),
  track: path.join(DATA_DIR, `${INSTRUMENT.toLowerCase()}_trackrecord.json`),
};

function saveState() {
  try {
    fs.writeFileSync(FILES.candles, JSON.stringify({ candles:candleHistory.slice(-MAX_HISTORY), tfData }));
    const engStates = {};
    for (const [n,e] of Object.entries(engines)) engStates[n] = {
      params:e.params, activeTrade:e.activeTrade, activePending:e.activePending,
      lastSignalIdx:e.lastSignalIdx, signalCount:e.signalCount,
      predictions:e.predictions.slice(-1000), currentSessionId:e.currentSessionId
    };
    fs.writeFileSync(FILES.state, JSON.stringify({ engines:engStates, gridSearchResults, lastGridSearchTime }));
    fs.writeFileSync(FILES.track, JSON.stringify(trackRecord.slice(-5000)));
  } catch(e) { console.log(`⚠ save: ${e.message}`); }
}

function loadState() {
  try {
    if (fs.existsSync(FILES.candles)) {
      const d = JSON.parse(fs.readFileSync(FILES.candles,'utf8'));
      candleHistory = d.candles||[]; tfData = d.tfData||tfData;
      console.log(`📂 ${candleHistory.length} candles geladen`);
    }
    if (fs.existsSync(FILES.state)) {
      const d = JSON.parse(fs.readFileSync(FILES.state,'utf8'));
      gridSearchResults = d.gridSearchResults||{};
      lastGridSearchTime = d.lastGridSearchTime;
      if (d.engines) {
        for (const [n,s] of Object.entries(d.engines)) {
          if (engines[n]) {
            engines[n].params = {...engines[n].params, ...s.params};
            engines[n].activeTrade=s.activeTrade; engines[n].activePending=s.activePending;
            engines[n].lastSignalIdx=s.lastSignalIdx??-999; engines[n].signalCount=s.signalCount||0;
            engines[n].predictions=s.predictions||[]; engines[n].currentSessionId=s.currentSessionId;
          }
        }
      }
      console.log(`📂 Engine states geladen | Grid search: ${lastGridSearchTime||'nooit'}`);
    }
    if (fs.existsSync(FILES.track)) {
      trackRecord = JSON.parse(fs.readFileSync(FILES.track,'utf8'));
      console.log(`📂 ${trackRecord.length} track record entries`);
    }
  } catch(e) { console.log(`⚠ load: ${e.message}`); }
}

// ═══════════════════════════════════════════════════════
// AUTH
// ═══════════════════════════════════════════════════════

function checkAuth(req) {
  return (req.headers['x-secret']||req.query.secret||req.body?.secret) === WEBHOOK_SECRET;
}

// ═══════════════════════════════════════════════════════
// ROUTES
// ═══════════════════════════════════════════════════════

app.get('/', (req, res) => {
  const last = candleHistory[candleHistory.length-1];
  const engSummary = {};
  for(const [n,e] of Object.entries(engines)){
    const closed = e.predictions.filter(p=>p.outcome==='WIN'||p.outcome==='LOSS');
    const wins = e.predictions.filter(p=>p.outcome==='WIN');
    engSummary[n] = {
      predictions:e.predictions.length, trade:e.activeTrade?`${e.activeTrade.dir}@${e.activeTrade.entry}`:null,
      pending:e.activePending?`${e.activePending.dir}@${e.activePending.entry}`:null,
      params:`SL=${e.params.sl} TP=${e.params.tp} ATR=${e.params.atrMax}`,
      wins:wins.length, losses:closed.length-wins.length
    };
  }
  res.json({ status:'ok', instrument:INSTRUMENT, engine:'v3-4x',
    candles:candleHistory.length, lastCandle:last?.t||null,
    engines:engSummary, lastGridSearch:lastGridSearchTime,
    trackRecord:trackRecord.length, uptime:process.uptime()
  });
});

app.post('/webhook', (req, res) => {
  if(!checkAuth(req)) return res.status(401).json({error:'Unauthorized'});
  try {
    const data=req.body; let btMs=null;
    if(data.bt){try{btMs=parseInt(data.bt);}catch(e){}delete data.bt;}
    const norm=normalize(data); const tfRaw=norm._tf_data||{}; delete norm._tf_data;
    for(const [tf,c] of Object.entries(tfRaw)){if(c)tfData[tf]=c;}
    const now=new Date(); norm.received_at=now.toISOString();
    let bucket; if(btMs){const bd=new Date(btMs);bucket=bd.toISOString().slice(0,16).replace('T',' ');norm.bar_time=bd.toISOString();}
    else{bucket=now.toISOString().slice(0,16).replace('T',' ');}
    norm.bucket=bucket; norm.t=bucket;
    let eIdx=null;
    for(let i=candleHistory.length-1;i>=Math.max(0,candleHistory.length-10);i--){if(candleHistory[i].bucket===bucket){eIdx=i;break;}}
    if(eIdx!==null)candleHistory[eIdx]=norm;
    else{candleHistory.push(norm);candleHistory.sort((a,b)=>(a.bucket||'').localeCompare(b.bucket||''));if(candleHistory.length>MAX_HISTORY)candleHistory=candleHistory.slice(-MAX_HISTORY);}
    if(candleHistory.length%5===0) saveState();

    // ★ RUN ALL 4 ENGINES
    for(const eng of Object.values(engines)) eng.tick(candleHistory);

    const states = Object.entries(engines).map(([n,e])=>`${n}:${e.activeTrade?'TRADE':(e.activePending?'PEND':'FREE')}`).join(' ');
    console.log(`[${bucket}] C=${norm.c} | ${eIdx!==null?'UPD':'NEW'} | n=${candleHistory.length} | ${states}`);
    res.json({status:'ok', candles:candleHistory.length, bucket});
  } catch(e) { console.error(`✗ webhook: ${e.message}`); res.status(500).json({error:e.message}); }
});

app.post('/import_history', (req, res) => {
  if(!checkAuth(req)) return res.status(401).json({error:'Unauthorized'});
  try {
    const candles=req.body.candles||[]; let added=0;
    const existing=new Set(candleHistory.map(c=>c.bucket||c.t));
    for(const c of candles){const b=c.bucket||c.t;if(!existing.has(b)){c.bucket=b;c.t=b;candleHistory.push(c);existing.add(b);added++;}}
    candleHistory.sort((a,b)=>(a.bucket||'').localeCompare(b.bucket||''));
    if(candleHistory.length>MAX_HISTORY) candleHistory=candleHistory.slice(-MAX_HISTORY);
    saveState();
    res.json({status:'ok', added, total:candleHistory.length});
  } catch(e) { res.status(500).json({error:e.message}); }
});

app.get('/candles', (req, res) => {
  const n=Math.min(parseInt(req.query.n||'500'),MAX_HISTORY);
  const seen=new Set(),out=[];
  for(let i=candleHistory.length-1;i>=Math.max(0,candleHistory.length-n);i--){const b=candleHistory[i].bucket||candleHistory[i].t;if(!seen.has(b)){seen.add(b);out.unshift(candleHistory[i]);}}
  res.json(out);
});

app.get('/latest', (req, res) => {
  res.json({latest:candleHistory[candleHistory.length-1]||{}, candles:candleHistory.length, tf_data:tfData});
});

app.get('/predictions', (req, res) => {
  const filter = req.query.filter;
  if(filter && engines[filter]) return res.json(engines[filter].predictions.slice(-500));
  const all = [];
  for(const e of Object.values(engines)) all.push(...e.predictions.slice(-200));
  all.sort((a,b)=>(a.signalTime||'').localeCompare(b.signalTime||''));
  res.json(all);
});

app.get('/state', (req, res) => {
  const engStates = {};
  for(const [n,e] of Object.entries(engines)) engStates[n]=e.getState();
  res.json({ engines:engStates, candles:candleHistory.length,
    lastCandle:candleHistory[candleHistory.length-1]?.t||null,
    lastGridSearch:lastGridSearchTime, gridResults:Object.keys(gridSearchResults).length>0?'available':'none',
    trackRecord:trackRecord.length
  });
});

app.post('/params', (req, res) => {
  if(!checkAuth(req)) return res.status(401).json({error:'Unauthorized'});
  const p=req.body, filter=p.filter;
  if(filter && engines[filter]){
    engines[filter].applyParams(p);
    saveState();
    return res.json({status:'ok', filter, params:engines[filter].params});
  }
  // Apply to all engines
  for(const e of Object.values(engines)) e.applyParams(p);
  saveState();
  res.json({status:'ok', params:Object.fromEntries(Object.entries(engines).map(([n,e])=>[n,e.params]))});
});

app.get('/trackrecord', (req, res) => {
  const filter = req.query.filter;
  if(filter) return res.json(trackRecord.filter(t=>t.filter===filter));
  res.json(trackRecord);
});

app.post('/trackrecord/clear', (req, res) => {
  if(!checkAuth(req)) return res.status(401).json({error:'Unauthorized'});
  trackRecord=[]; saveState(); res.json({status:'ok'});
});

app.post('/gridsearch', (req, res) => {
  if(!checkAuth(req)) return res.status(401).json({error:'Unauthorized'});
  runNightlyGridSearch();
  res.json({status:'ok', lastGridSearch:lastGridSearchTime, results:Object.keys(gridSearchResults)});
});

app.post('/clear', (req, res) => {
  if(!checkAuth(req)) return res.status(401).json({error:'Unauthorized'});
  candleHistory=[]; tfData={'1':{},'5':{},'15':{},'30':{},'60':{}};
  for(const e of Object.values(engines)){e.predictions=[];e.activePending=null;e.activeTrade=null;e.lastSignalIdx=-999;e.signalCount=0;}
  saveState(); res.json({status:'ok'});
});

// ─── Calendar data endpoint ───
app.get('/calendar', (req, res) => {
  const days = {};
  candleHistory.forEach(c => {
    const d = (c.t||c.bucket||'').slice(0,10);
    if(!d) return;
    if(!days[d]) days[d] = { date:d, candles:0, first:c.t, last:c.t };
    days[d].candles++;
    if(c.t < days[d].first) days[d].first = c.t;
    if(c.t > days[d].last) days[d].last = c.t;
  });
  // Add trade counts per day
  trackRecord.forEach(t => {
    const d = (t.exitTime||t.signalTime||t.logged||'').slice(0,10);
    if(days[d]) {
      days[d].trades = (days[d].trades||0)+1;
      days[d].wins = (days[d].wins||0)+(t.outcome==='WIN'?1:0);
      days[d].pnl = r2((days[d].pnl||0)+(t.pnlPt||0));
    }
  });
  res.json({ totalCandles:candleHistory.length, totalDays:Object.keys(days).length,
    firstDate:candleHistory[0]?.t?.slice(0,10)||null,
    lastDate:candleHistory[candleHistory.length-1]?.t?.slice(0,10)||null,
    days:Object.values(days).sort((a,b)=>a.date.localeCompare(b.date))
  });
});

// ═══════════════════════════════════════════════════════
// START
// ═══════════════════════════════════════════════════════

loadState();

app.listen(PORT, () => {
  console.log(`\n${'═'.repeat(60)}`);
  console.log(`  ${INSTRUMENT} Oracle Server v3 — 4 Engines + Grid Search`);
  console.log(`  Port: ${PORT} | Tick: ${TICK_SIZE} | ${CURRENCY}${PT_VALUE}/pt`);
  console.log(`  Candles: ${candleHistory.length} | Track: ${trackRecord.length}`);
  for(const [n,e] of Object.entries(engines)){
    console.log(`  [${n}] SL=${e.params.sl} TP=${e.params.tp} | ${e.activeTrade?'TRADE':'FREE'} | ${e.predictions.length} preds`);
  }
  console.log(`  Grid search: ${lastGridSearchTime||'nooit'} (volgende: ${GRID_SEARCH_HOUR}:00 UTC)`);
  console.log(`  ntfy: ${NTFY_TOPIC}`);
  console.log(`${'═'.repeat(60)}\n`);

  // Run grid search at startup if we have enough data and never ran
  if(!lastGridSearchTime && candleHistory.length > 3000) {
    console.log('📊 Eerste grid search bij startup…');
    setTimeout(runNightlyGridSearch, 2000);
  }
});
