/*
 * Primealogy: The prime family tree
 * Every prime p > 2 is drawn as a child of the largest prime factor of p - 1.
 * The result is a single tree rooted at 2, laid out radially in 3D:
 *   radius = log2(p), angle = a wedge proportional to the number of leaves below,
 *   height and color = generation (steps back to 2), so each generation is a layer.
 * No dependencies. Works as a standalone page or inside an iframe (?embed=1).
 */
(function () {
  'use strict';

  var TAU = Math.PI * 2;
  var GAP = 0.22;                       /* empty wedge at 12 o'clock that holds the ring labels */
  var A0 = -Math.PI / 2 + GAP / 2;
  var A1 = 1.5 * Math.PI - GAP / 2;
  var GROW_SECONDS = 15;                /* one full growth animation */
  var TREE_HEIGHT = 0.6;                /* stack of generation layers, as a share of the canvas width */
  var START_TILT = 1.0, START_SPIN = 0;  /* radians; a tilt of 0 looks straight down the stack */
  var DRAG_SPEED = 0.008;               /* radians per pixel */
  var DIM = 0.22;                       /* opacity of primes outside a root=p filter */
  var FAN_MIN = 3;                      /* fewest children that make a feather worth filling */
  var FAN_FILL = 0.3;                   /* opacity of a filled feather */
  var TREE_MAX = 5000000;               /* largest tree worth drawing; above this, workers count instead */
  var ANIMATE_MAX = 1 << 16;            /* bigger trees appear finished rather than growing */
  var MAX_BOUND = BigInt('1223334444555554444333221');
  var SAFE_MAX = Number.MAX_SAFE_INTEGER;   /* the workers' sieve stops here */
  var SEGMENT = 1 << 22;                /* numbers per worker job */
  var RAMPS = {
    dark:  ['#F2D28A', '#EF9F27', '#ED93B1', '#AFA9EC', '#85B7EB', '#5DCAA5', '#9FE1CB', '#E1F5EE', '#FFFFFF'],
    light: ['#BA7517', '#EF9F27', '#D4537E', '#7F77DD', '#378ADD', '#1D9E75', '#0F6E56', '#04342C', '#000000']
  };

  var $ = function (id) { return document.getElementById(id); };
  var stage = $('stage'), cv = $('tree'), ctx = cv.getContext('2d');
  var ui = {
    play: $('play'), playIcon: $('playIcon'), grow: $('grow'), upto: $('upto'), count: $('count'),
    chainLabel: $('chainLabel'), chain: $('chain'), detail: $('detail'), find: $('find'), q: $('q'), qerr: $('qerr'),
    rootToggle: $('rootToggle'), boundForm: $('boundForm'), bound: $('bound'), bounderr: $('bounderr'),
    runBar: $('runBar'), runStatus: $('runStatus'), stop: $('stop'), stats: $('stats'), legend: $('legend'), theme: $('theme'),
    fillToggle: $('fillToggle'), ringToggle: $('ringToggle'), zin: $('zin'), zout: $('zout'), zreset: $('zreset'), zfull: $('zfull'),
    piToggle: $('piToggle'), waveToggle: $('waveToggle'), gapToggle: $('gapToggle'), zeroRow: $('zeroRow'), zeros: $('zeros'), zeroOut: $('zeroOut'),
    chartWrap: $('chartWrap'), chartKey: $('chartKey'), chart: $('pichart')
  };
  var cctx = ui.chart.getContext('2d');

  var store = {
    get: function (k) { try { return window.localStorage.getItem(k); } catch (e) { return null; } },
    set: function (k, v) { try { window.localStorage.setItem(k, v); } catch (e) { /* storage unavailable */ } }
  };
  var params = new URLSearchParams(window.location.search);
  if (params.get('embed') === '1') document.body.classList.add('embed');
  var reduceMotion = window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches;

  /* ---------- number theory ---------- */

  function isPrime(n) {
    if (n < 2 || n % 1 !== 0) return false;
    if (n % 2 === 0) return n === 2;
    for (var d = 3; d * d <= n; d += 2) if (n % d === 0) return false;
    return true;
  }

  function build(N) {
    var exp = Math.max(2, Math.log2(N));
    var spf = new Uint32Array(N + 1);           /* smallest prime factor sieve */
    var i, j;
    for (i = 2; i <= N; i++) {
      if (spf[i] === 0) for (j = i; j <= N; j += i) if (spf[j] === 0) spf[j] = i;
    }
    var P = [];
    for (i = 2; i <= N; i++) if (spf[i] === i) P.push(i);
    var n = P.length;
    var idx = new Int32Array(N + 1).fill(-1);
    for (i = 0; i < n; i++) idx[P[i]] = i;

    var gpf = function (v) { var g = 1; while (v > 1) { var q = spf[v]; if (q > g) g = q; v /= q; } return g; };
    var par = new Int32Array(n).fill(-1), gen = new Uint8Array(n), kids = [], byGen = [[0]];
    var lg = new Float64Array(n), wt = new Float64Array(n), ang = new Float64Array(n);
    for (i = 0; i < n; i++) kids.push([]);
    lg[0] = 1;
    for (i = 1; i < n; i++) {
      j = idx[gpf(P[i] - 1)];
      par[i] = j; gen[i] = gen[j] + 1; kids[j].push(i); lg[i] = Math.log2(P[i]);
      if (!byGen[gen[i]]) byGen[gen[i]] = [];
      byGen[gen[i]].push(i);
    }
    for (i = n - 1; i >= 0; i--) { if (!kids[i].length) wt[i] = 1; if (i) wt[par[i]] += wt[i]; }
    (function place(k, a0, a1) {
      ang[k] = (a0 + a1) / 2;
      var a = a0, c = kids[k];
      for (var t = 0; t < c.length; t++) { var w = (a1 - a0) * wt[c[t]] / wt[k]; place(c[t], a, a + w); a += w; }
    })(0, A0, A1);

    /* feathers, keyed by the generation of their children; 2 is left out because its
       few spokes would make one polygon as wide as the whole tree */
    var fans = [];
    for (i = 1; i < n; i++) if (kids[i].length >= FAN_MIN) {
      if (!fans[gen[i] + 1]) fans[gen[i] + 1] = [];
      fans[gen[i] + 1].push(i);
    }

    var deep = 0, leaves = 0;
    for (i = 1; i < n; i++) if (gen[i] > gen[deep]) deep = i;
    for (i = 0; i < n; i++) if (!kids[i].length) leaves++;
    var factor = function (v) {
      var out = [];
      while (v > 1) { var q = spf[v], e = 0; while (v % q === 0) { v /= q; e++; } out.push([q, e]); }
      return out;
    };
    return { exp: exp, N: N, P: P, n: n, idx: idx, par: par, gen: gen, kids: kids, byGen: byGen, fans: fans, lg: lg, ang: ang,
             deep: deep, maxGen: gen[deep], leaves: leaves, factor: factor };
  }

  /* ---------- state ---------- */

  var T = null;                                  /* the current tree */
  var WX, WY, WZ, cnt;                          /* world positions, live child counts */
  var SX, SY, SP;                               /* screen position and perspective scale, per frame */
  var E, stride = 0, edgeSegs = 0;              /* each edge as a polyline of world points */
  var W = 0, dpr = 1, cx = 0, cy = 0, unit = 0, layerGap = 0, persp = 1, fit = 1;
  var spin = START_SPIN, tilt = START_TILT;      /* rotation about the stack, and of the stack */
  var cosS = 1, sinS = 0, cosT = 1, sinT = 0, outX = 0, outY = 0, outP = 1;
  var s = 1, tx = 0, ty = 0;                     /* view: screen = world * s + t */
  var L = 1;                                     /* growth front, in log2 units */
  var playing = false, lastTs = 0, sel = -1, shown = 0, shownAt = 0;
  var bound = BigInt(8192);                      /* the visitor's upper limit; T stops at TREE_MAX */
  var near = null;                               /* { v, lo, hi }: a non-prime search and the primes either side */
  var rootP = 0, rootKids = null, marked = null; /* root=p filter: its children, and a per-prime "stay bright" flag */
  var genSel = null;                             /* generations on show as { g: 1 }; null means all */
  var ringsByValue = false;                      /* ring radius follows a generation's largest prime itself, not its log */
  var fillFans = true;                           /* shade the sheet between each parent's children */
  var piChart = false, waves = false, gapView = false, zeroCount = 50;   /* the π(x) chart, Riemann's waves, and π(x) − Li(x) */
  var frameReq = 0;
  var theme = 'dark', col = RAMPS.dark, ink = '#eef1f6', paper = '#0a1424', muted = '#7d8aa1', line = 'rgba(255,255,255,.09)', line2 = 'rgba(255,255,255,.16)';
  var font = 'Outfit, system-ui, sans-serif';

  /* ---------- theme ---------- */

  function cssVar(name, fb) {
    var v = getComputedStyle(document.documentElement).getPropertyValue(name);
    return v && v.trim() ? v.trim() : fb;
  }
  function applyTheme(t) {
    theme = t === 'light' ? 'light' : 'dark';
    document.documentElement.setAttribute('data-theme', theme);
    col = RAMPS[theme];
    ink = cssVar('--ink', ink); paper = cssVar('--bg', paper); muted = cssVar('--muted', muted); line = cssVar('--line', line); line2 = cssVar('--line-2', line2);
    font = getComputedStyle(document.body).fontFamily || font;
    ui.theme.textContent = theme === 'dark' ? 'Switch to light' : 'Switch to dark';
    var meta = document.querySelector('meta[name="theme-color"]');
    if (meta) meta.setAttribute('content', cssVar('--bg', '#0a1424'));
    buildLegend();
    ui.chartKey._t = '';
    schedule();
  }

  function genColor(g) { return col[Math.min(g, col.length) - 1]; }

  function buildLegend() {
    if (!T) return;
    ui.legend.textContent = '';
    for (var g = 1; g <= T.maxGen; g++) {
      var b = document.createElement('button'), sw = document.createElement('i');
      b.type = 'button'; b.dataset.g = g;
      b.setAttribute('aria-label', 'Generation ' + g);
      sw.style.background = genColor(g);
      b.appendChild(sw); b.appendChild(document.createTextNode(String(g)));
      ui.legend.appendChild(b);
    }
    var all = document.createElement('button');
    all.type = 'button'; all.dataset.g = 'all'; all.textContent = 'All';
    all.setAttribute('aria-label', 'All generations');
    ui.legend.appendChild(all);
    /* a smaller tree may not reach every chosen generation */
    if (genSel) { for (g in genSel) if (g > T.maxGen) delete genSel[g]; settleGens(); }
    syncLegend();
  }

  function genHidden(g) { return genSel && !genSel[g]; }
  function genList() { return Object.keys(genSel).map(Number).sort(function (a, b) { return a - b; }); }
  /* none picked, or every one picked, is the same as all */
  function settleGens() { if (genSel) { var c = genList().length; if (!c || c === T.maxGen) genSel = null; } }
  function syncLegend() {
    ui.legend.classList.toggle('filtered', !!genSel);
    Array.prototype.forEach.call(ui.legend.children, function (b) {
      b.setAttribute('aria-pressed', String(b.dataset.g === 'all' ? !genSel : !!(genSel && genSel[b.dataset.g])));
    });
  }
  function parseGens(text) {
    var out = null;
    (text || '').split(',').forEach(function (t) {
      if (/^[1-9]\d?$/.test(t)) { out = out || {}; out[+t] = 1; }
    });
    return out;
  }

  /* ---------- geometry ---------- */

  function layerZ(g) { return (g - T.maxGen / 2) * layerGap; }

  function layout() {
    var w = stage.clientWidth;
    if (!w) return;
    if (W) { tx *= w / W; ty *= w / W; }          /* stay on the same spot when the stage changes size */
    W = w; dpr = Math.min(window.devicePixelRatio || 1, 3);
    cv.width = cv.height = Math.round(W * dpr);
    cx = cy = W / 2;
    var rim = W / 2 - 14;
    unit = rim / T.exp;
    layerGap = T.maxGen ? W * TREE_HEIGHT / T.maxGen : 0;
    persp = W * 2.5;
    var reach = Math.hypot(rim, layerGap * T.maxGen / 2);
    fit = rim / (reach * 1.08);                   /* the whole stack stays in frame at any angle */

    WX = new Float64Array(T.n); WY = new Float64Array(T.n); WZ = new Float64Array(T.n);
    SX = new Float64Array(T.n); SY = new Float64Array(T.n); SP = new Float64Array(T.n);
    for (var i = 0; i < T.n; i++) {
      var r = i ? T.lg[i] * unit : 0;
      WX[i] = r * Math.cos(T.ang[i]); WY[i] = r * Math.sin(T.ang[i]); WZ[i] = layerZ(T.gen[i]);
    }
    edgeSegs = T.n > 20000 ? 5 : T.n > 3000 ? 8 : 12;
    stride = (edgeSegs + 1) * 3;
    E = new Float32Array(T.n * stride);
    for (i = 1; i < T.n; i++) buildEdge(i);
    if (piChart) layoutChart();
    clampView(); schedule();
  }

  function buildEdge(i) {
    var j = T.par[i], r0 = j ? T.lg[j] * unit : 0, r1 = T.lg[i] * unit, a1 = T.ang[i], a0 = j ? T.ang[j] : a1;
    var z0 = WZ[j], z1 = WZ[i], o = i * stride;
    for (var k = 0; k <= edgeSegs; k++) {
      var t = k / edgeSegs, a = a0 + (a1 - a0) * (1 - Math.pow(1 - t, 3)), r = r0 + (r1 - r0) * t;
      E[o++] = r * Math.cos(a); E[o++] = r * Math.sin(a);
      E[o++] = z0 + (z1 - z0) * t * t * (3 - 2 * t);       /* leave and arrive level with each layer */
    }
  }

  function setAngles() { cosS = Math.cos(spin); sinS = Math.sin(spin); cosT = Math.cos(tilt); sinT = Math.sin(tilt); }

  /* world to screen: spin about the stack, tilt the stack, then perspective, fit, and zoom */
  function view(x, y, z) {
    var x1 = x * cosS - y * sinS, y1 = x * sinS + y * cosS;
    var y2 = y1 * cosT - z * sinT, z2 = y1 * sinT + z * cosT;
    outP = persp / (persp - z2) * fit;
    outX = (cx + x1 * outP) * s + tx; outY = (cy + y2 * outP) * s + ty;
  }

  function addEdge(i) {
    var o = i * stride;
    for (var k = 0; k <= edgeSegs; k++, o += 3) {
      view(E[o], E[o + 1], E[o + 2]);
      if (k) ctx.lineTo(outX, outY); else ctx.moveTo(outX, outY);
    }
  }

  /* a feather's outline: out along the first child's edge, across the tips, back down the
     last child's edge. kids[] is in angle order, so this is the sheet the edges already span. */
  function addFan(j, m) {
    var c = T.kids[j], n = 0, t, k, o;
    while (n < c.length && c[n] < m) n++;
    if (n < FAN_MIN) return false;
    addEdge(c[0]);
    for (t = 1; t < n; t++) ctx.lineTo(SX[c[t]], SY[c[t]]);
    for (k = edgeSegs - 1, o = c[n - 1] * stride + k * 3; k >= 0; k--, o -= 3) {
      view(E[o], E[o + 1], E[o + 2]);
      ctx.lineTo(outX, outY);
    }
    ctx.closePath();
    return true;
  }

  function addCircle(r, z) {
    var steps = 72;
    for (var k = 0; k <= steps; k++) {
      var a = A0 + (A1 - A0) * k / steps;
      view(r * Math.cos(a), r * Math.sin(a), z);
      if (k) ctx.lineTo(outX, outY); else ctx.moveTo(outX, outY);
    }
  }

  function upto(v) {
    var lo = 0, hi = T.n;
    while (lo < hi) { var m = (lo + hi) >> 1; if (T.lg[m] <= v + 1e-9) lo = m + 1; else hi = m; }
    return lo;
  }
  function isBig(i) { return T.gen[i] < 2 && T.P[i] < 100; }
  function radius(i) {
    if (!i) return 9;
    if (isBig(i)) return T.P[i] < 10 ? 8 : 9.5;
    var base = T.exp >= 18 ? 0.6 : T.exp >= 16 ? 0.8 : T.exp >= 14 ? 1 : 1.15, k = T.exp >= 18 ? 0.18 : T.exp >= 16 ? 0.45 : 0.62;
    return base + k * Math.sqrt(cnt[i]);
  }

  /* ---------- drawing ---------- */

  /* farther layers fade, which is most of what makes the stack read as depth */
  function fog(g) {
    var half = layerGap * T.maxGen / 2;
    return half ? 0.7 + 0.3 * (layerZ(g) * cosT) / half : 1;
  }

  function dotSize(i) { return radius(i) * Math.sqrt(s) * SP[i] / fit; }

  function drawRings(m) {
    var step = T.exp <= 13 ? 3 : 4, base = layerZ(0), k, g;
    ctx.lineWidth = 1; ctx.font = '11px ' + font; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    for (k = 2; k <= T.exp; k++) {
      ctx.beginPath(); addCircle(k * unit, base);
      ctx.strokeStyle = k % step ? line : line2; ctx.stroke();
      if (k > 3 && k % step === 0) {
        view(0, -k * unit, base);
        ctx.fillStyle = muted; ctx.fillText(Math.pow(2, k).toLocaleString('en-US'), outX, outY);
      }
    }
    /* the rim of each generation's layer, once it has a prime in it */
    for (g = 1; g <= T.maxGen; g++) {
      if (genHidden(g)) continue;
      var list = T.byGen[g], top = 0;
      for (k = 0; k < list.length && list[k] < m; k++) top = Math.max(top, T.lg[list[k]]);
      if (!top) continue;
      /* lists run in rising order, so the prime before k is the largest so far; a prime at the limit reaches the rim */
      ctx.beginPath(); addCircle(ringsByValue ? T.exp * unit * T.P[list[k - 1]] / T.N : top * unit, layerZ(g));
      ctx.strokeStyle = genColor(g); ctx.globalAlpha = (ringsByValue ? 0.8 : 0.28) * fog(g); ctx.stroke();
      ctx.globalAlpha = 1;
    }
  }

  function drawLayer(g, m) {
    var list = T.byGen[g], f = fog(g), big = T.exp >= 16, width = (big ? 0.5 : 0.7) * Math.pow(s, 0.3), i, k, r;
    var c = genColor(g);

    if (fillFans && T.fans[g]) {
      ctx.fillStyle = c; ctx.globalAlpha = (marked ? DIM * 0.5 : FAN_FILL) * f;
      for (k = 0; k < T.fans[g].length; k++) {
        ctx.beginPath();
        if (addFan(T.fans[g][k], m)) ctx.fill();
      }
    }

    ctx.beginPath();
    for (k = 0; k < list.length && (i = list[k]) < m; k++) if (!(marked && marked[i])) addEdge(i);
    ctx.strokeStyle = c; ctx.lineWidth = width;
    ctx.globalAlpha = (marked ? DIM * 0.5 : big ? 0.45 : 0.55) * f;
    ctx.stroke();

    ctx.beginPath();
    for (k = 0; k < list.length && (i = list[k]) < m; k++) if (!isBig(i) && !(marked && marked[i])) {
      r = dotSize(i); ctx.moveTo(SX[i] + r, SY[i]); ctx.arc(SX[i], SY[i], r, 0, TAU);
    }
    ctx.fillStyle = c; ctx.globalAlpha = (marked ? DIM : 1) * f; ctx.fill();
    ctx.globalAlpha = 1;

    if (!marked) return;
    for (k = 0; k < list.length && (i = list[k]) < m; k++) if (marked[i]) {
      ctx.beginPath(); addEdge(i); ctx.lineWidth = width * 2; ctx.strokeStyle = c; ctx.stroke();
      if (isBig(i)) continue;
      r = dotSize(i) + 1;
      ctx.beginPath(); ctx.arc(SX[i], SY[i], r, 0, TAU); ctx.fillStyle = c; ctx.fill();
      ctx.beginPath(); ctx.arc(SX[i], SY[i], r + 2.5, 0, TAU); ctx.strokeStyle = ink; ctx.lineWidth = 1.2; ctx.stroke();
    }
  }

  function draw(ts) {
    if (!W) return;
    var m = upto(L), i, k, g;
    setAngles();
    for (i = 0; i < m; i++) { view(WX[i], WY[i], WZ[i]); SX[i] = outX; SY[i] = outY; SP[i] = outP; }

    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, W, W);
    drawRings(m);

    cnt.fill(0);
    for (i = 1; i < m; i++) cnt[T.par[i]]++;
    /* painter's order: the layer farthest from the viewer first */
    for (k = 1; k <= T.maxGen; k++) {
      g = cosT >= 0 ? k : T.maxGen + 1 - k;
      if (!genHidden(g)) drawLayer(g, m);
    }

    if (L < T.exp) {
      ctx.beginPath(); addCircle(L * unit, layerZ(0));
      ctx.strokeStyle = muted; ctx.lineWidth = 1; ctx.stroke();
    }

    /* the line being described */
    if (!playing || ts - shownAt > 130 || shown > m - 1) { shown = m - 1; shownAt = ts; }
    var pair = near !== null && near.hi < m;     /* scrubbed back past the pair: fall through, as with sel */
    var picked = sel >= 0 && sel < m;
    var f = picked ? sel : m >= T.n ? T.deep : shown;
    var listing = marked !== null && !pair && !picked;   /* the filter speaks for the panel; skip the auto line */
    if (pair) { trace(near.lo); trace(near.hi); }
    else if (f > 0 && !listing && (picked || !genSel)) trace(f);   /* the automatic line would cross hidden generations */

    /* labelled discs for 2, 3, 5, 17 */
    for (i = 0; i < Math.min(m, 8); i++) if (isBig(i) && !(i && genHidden(T.gen[i]))) {
      ctx.beginPath(); ctx.arc(SX[i], SY[i], dotSize(i), 0, TAU);
      ctx.fillStyle = i ? col[0] : ink;
      ctx.globalAlpha = marked && i && !marked[i] ? DIM : 1; ctx.fill();
      ctx.globalAlpha = 1;
      var scale = Math.sqrt(s) * SP[i] / fit;
      ctx.font = '500 ' + ((i ? 11 : 12) * scale) + 'px ' + font;
      ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
      ctx.fillStyle = paper; ctx.fillText(String(T.P[i]), SX[i], SY[i] + 0.5 * scale);
    }

    put(ui.chainLabel, listing ? 'Hanging directly from ' + rootP : 'Line of descent');
    if (pair) { drawTags(near.lo, near.hi); describeNear(); }
    else if (listing) describeRoot(m);
    else describe(f, picked, m);
    put(ui.upto, 'up to ' + fmt(Math.min(T.N, Math.floor(Math.pow(2, L) + 1e-6))));
    put(ui.count, fmt(m) + (m === 1 ? ' prime' : ' primes'));
    drawChart(ts);
  }

  /* one line of descent, from prime f back to 2 */
  function trace(f) {
    var k;
    ctx.beginPath();
    for (k = f; k > 0; k = T.par[k]) addEdge(k);
    ctx.strokeStyle = ink; ctx.lineWidth = 1.7; ctx.lineJoin = 'round'; ctx.stroke();
    for (k = f; k > 0; k = T.par[k]) {
      ctx.beginPath(); ctx.arc(SX[k], SY[k], dotSize(k) + (k === f ? 3 : 1.3), 0, TAU);
      ctx.lineWidth = k === f ? 1.7 : 1.2; ctx.stroke();
    }
  }

  /* value tags on the two highlighted primes, which can sit far apart on the tree */
  function drawTags(a, b) {
    var H = 20, GAP_PX = 10, placed = null;
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.font = '500 12px ' + font; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    [a, b].forEach(function (i) {
      var sx = SX[i], sy = SY[i];
      if (sx < 0 || sy < 0 || sx > W || sy > W) return;
      var label = fmt(T.P[i]), w = ctx.measureText(label).width + 12;
      var len = Math.hypot(sx - W / 2, sy - W / 2) || 1, ux = (sx - W / 2) / len, uy = (sy - W / 2) / len;
      var bx = sx + ux * (w / 2 + GAP_PX), by = sy + uy * (H / 2 + GAP_PX);
      /* no room outside the rim: sit on the inner side rather than cover the dot */
      if (bx < w / 2 + 2 || bx > W - w / 2 - 2 || by < H / 2 + 2 || by > W - H / 2 - 2) {
        bx = sx - ux * (w / 2 + GAP_PX); by = sy - uy * (H / 2 + GAP_PX);
      }
      if (placed && Math.abs(bx - placed.x) < (w + placed.w) / 2 + 2 && Math.abs(by - placed.y) < H + 2) {
        by = placed.y + (by >= placed.y && placed.y + H + 2 <= W - H / 2 ? 1 : -1) * (H + 2);
      }
      ctx.beginPath();
      if (ctx.roundRect) ctx.roundRect(bx - w / 2, by - H / 2, w, H, 6); else ctx.rect(bx - w / 2, by - H / 2, w, H);
      ctx.fillStyle = paper; ctx.fill();
      ctx.strokeStyle = ink; ctx.lineWidth = 1; ctx.stroke();
      ctx.fillStyle = ink; ctx.fillText(label, bx, by + 0.5);
      placed = { x: bx, y: by, w: w };
    });
  }

  function put(el, text) { if (el._t !== text) { el._t = text; el.textContent = text; } }
  function sup(e) { var d = '⁰¹²³⁴⁵⁶⁷⁸⁹'; return e === 1 ? '' : String(e).split('').map(function (c) { return d[+c]; }).join(''); }
  function fmt(n) { return n.toLocaleString('en-US'); }

  function describe(f, picked, m) {
    var ch = [];
    for (var k = f; k >= 0; k = T.par[k]) ch.push(T.P[k]);
    put(ui.chain, ch.reverse().join(' → '));
    if (f > 0) {
      var p = T.P[f], fac = T.factor(p - 1).map(function (x) { return x[0] + sup(x[1]); }).join(' × ');
      var lead = picked ? 'Selected' : m >= T.n ? 'Deepest line' : 'Newest prime';
      var kids = T.kids[f].length;
      var text = lead + ' · generation ' + T.gen[f] + '\n' + p + ' − 1 = ' + fac +
        (playing ? '' : '\n' + (kids ? kids + (kids === 1 ? ' child' : ' children') : 'No children') + ' up to ' + fmt(T.N));
      setDetail(text);
    } else {
      var t0 = 'The root · every prime traces back to 2' + (playing ? '' : '\n' + T.kids[0].length + ' children: ' + T.kids[0].map(function (c) { return T.P[c]; }).join(', '));
      setDetail(t0);
    }
  }

  function describeNear() {
    var line = function (i) {
      var ch = [];
      for (var k = i; k >= 0; k = T.par[k]) ch.push(T.P[k]);
      return ch.reverse().join(' → ');
    };
    var eq = function (i) {
      return T.P[i] + ' − 1 = ' + T.factor(T.P[i] - 1).map(function (x) { return x[0] + sup(x[1]); }).join(' × ') +
        ' · generation ' + T.gen[i];
    };
    put(ui.chain, line(near.lo) + '\n' + line(near.hi));
    setDetail('Closest to ' + fmt(near.v) + ' · ' + (near.v - T.P[near.lo]) + ' below, ' + (T.P[near.hi] - near.v) + ' above\n' +
      eq(near.lo) + '\n' + eq(near.hi));
  }

  function describeRoot(m) {
    var LIST_MAX = 12;
    var found = rootKids.filter(function (i) { return i < m; }).map(function (i) { return T.P[i]; });
    put(ui.chain, found.length ? found.slice(0, LIST_MAX).join(', ') + (found.length > LIST_MAX ? ', …' : '') : m >= T.n ? 'None' : 'None yet');
    setDetail(fmt(found.length) + ' of ' + fmt(T.n) + ' primes up to ' + fmt(T.N) +
      (rootP === 2 ? '\nFermat primes: p − 1 is a power of 2' : ''));
  }

  function setDetail(text) {
    if (ui.detail._t === text) return;
    ui.detail._t = text; ui.detail.textContent = '';
    text.split('\n').forEach(function (t) { var d = document.createElement('div'); d.textContent = t; ui.detail.appendChild(d); });
  }

  /* ---------- π(x), Li(x) and Riemann's waves ---------- */

  /* li(x) = ∫₀ˣ dt / ln t (principal value), by Ramanujan's series */
  function li(x) {
    var L = Math.log(x), s = 0, term = 1, inner = 0;
    for (var n = 1; n < 200; n++) {
      term *= L / n;
      if (n % 2) inner += 1 / n;
      var d = (n % 2 ? 1 : -1) * term / Math.pow(2, n - 1) * inner;
      s += d;
      if (Math.abs(d) < 1e-16 * Math.abs(s)) break;
    }
    return 0.5772156649015329 + Math.log(L) + Math.sqrt(x) * s;
  }
  var LI2 = li(2);
  function Li(x) { return li(x) - LI2; }     /* the offset form, ∫₂ˣ dt / ln t */

  /* Riemann's R(x) = Σ μ(n)/n · li(x^(1/n)), summed as Gram's series, which needs ζ(k) */
  var ZETA = [];
  (function () {
    for (var k = 2; k < 130; k++) {
      var z = 0, n;
      for (n = 1; n <= 60; n++) z += Math.pow(n, -k);
      ZETA[k] = z + Math.pow(60, 1 - k) / (k - 1) - 0.5 * Math.pow(60, -k);
    }
  })();
  function riemannR(x) {
    var L = Math.log(x), s = 1, t = 1;
    for (var k = 1; k < 128; k++) {
      t *= L / k;
      var d = t / (k * ZETA[k + 1]);
      s += d;
      if (d < 1e-16 * s) break;
    }
    return s;
  }
  var MU = [0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1, 0, -1, 0, -1, 0, 1, 1, -1, 0, 0, 1, 0, 0, -1, -1, -1, 0, 1, 1, 1, 0, -1, 1, 1, 0, -1, -1, -1, 0, 0, 1, -1, 0, 0, 0, 1, 0, -1, 0, 1, 0, 1, 1, -1, 0, -1, 1, 0, 0];

  /* Heights of the zeta zeros ½ + iγ. The first ten are exact to 9 places; the rest come from the
     Riemann–Siegel formula, found as sign changes of Z(t), good to about 0.001 */
  var ZERO_MAX = 200, zetaZeros = null;
  function rsTheta(t) { return t / 2 * Math.log(t / TAU) - t / 2 - Math.PI / 8 + 1 / (48 * t) + 7 / (5760 * t * t * t); }
  function rsZ(t) {
    var a = Math.sqrt(t / TAU), N = Math.floor(a), p = a - N, th = rsTheta(t), s = 0;
    for (var n = 1; n <= N; n++) s += Math.cos(th - t * Math.log(n)) / Math.sqrt(n);
    var c = Math.cos(TAU * p);
    if (Math.abs(c) < 1e-9) { p += 1e-9; c = Math.cos(TAU * p); }
    return 2 * s + (N % 2 ? 1 : -1) * Math.pow(a, -0.5) * Math.cos(TAU * (p * p - p - 1 / 16)) / c;
  }
  function getZeros() {
    if (zetaZeros) return zetaZeros;
    var out = [14.134725142, 21.022039639, 25.010857580, 30.424876126, 32.935061588,
               37.586178159, 40.918719012, 43.327073281, 48.005150881, 49.773832478];
    var t = 50.5, h = 0.02, z0 = rsZ(t);
    while (out.length < ZERO_MAX) {
      var t1 = t + h, z1 = rsZ(t1);
      if ((z0 < 0) !== (z1 < 0)) {
        var lo = t, hi = t1, zl = z0;
        for (var i = 0; i < 40; i++) { var m = (lo + hi) / 2, zm = rsZ(m); if ((zm < 0) === (zl < 0)) { lo = m; zl = zm; } else hi = m; }
        out.push((lo + hi) / 2);
      }
      t = t1; z0 = z1;
    }
    return (zetaZeros = out);
  }

  /* one zero and its mirror image together: 2·Re Li(x^ρ) with ρ = ½ + iγ and u = ln x,
     from the asymptotic series e^z/z · Σ k!/z^k, which is sharp here because |z| > 9 */
  function wavePair(u, g) {
    var a = u / 2, b = g * u, e = Math.exp(a), cr = e * Math.cos(b), ci = e * Math.sin(b);
    var d = a * a + b * b, ir = a / d, ii = -b / d;
    var sr = 1, si = 0, tr = 1, ti = 0;
    for (var k = 1; k < 40; k++) {
      var nr = (tr * ir - ti * ii) * k, ni = (tr * ii + ti * ir) * k;
      if (nr * nr + ni * ni > tr * tr + ti * ti) break;     /* the series has started to diverge */
      tr = nr; ti = ni; sr += tr; si += ti;
      if (tr * tr + ti * ti < 1e-14) break;
    }
    var pr = cr * ir - ci * ii, pi = cr * ii + ci * ir;
    return 2 * (pr * sr - pi * si);
  }

  /* Riemann's explicit formula for π(x), cut off after the first K zeros:
     π(x) = R(x) − Σ_ρ R(x^ρ) − 1/ln x + arctan(π / ln x)/π */
  function explicitPi(x, K) {
    var L = Math.log(x), v = riemannR(x) - 1 / L + Math.atan(Math.PI / L) / Math.PI, zs = getZeros();
    for (var n = 1; n < MU.length; n++) {
      var u = L / n;
      if (u < Math.LN2) break;                     /* x^(1/n) below 2 adds next to nothing */
      if (!MU[n]) continue;
      var s = 0;
      for (var k = 0; k < K; k++) s += wavePair(u, zs[k]);
      v -= MU[n] / n * s;
    }
    return v;
  }

  function piAt(x) {                                /* primes ≤ x, from the tree's list */
    var lo = 0, hi = T.n;
    while (lo < hi) { var m = (lo + hi) >> 1; if (T.P[m] <= x) lo = m + 1; else hi = m; }
    return lo;
  }

  var CW = 0, CH = 0, chartAt = 0, waveCache = { key: '' };
  var compact = window.Intl && Intl.NumberFormat ? new Intl.NumberFormat('en-US', { notation: 'compact', maximumFractionDigits: 1 }) : null;
  function fmtAxis(v) { return v < 10000 || !compact ? fmt(v) : compact.format(v); }
  function niceStep(span, count) {
    var raw = span / count, p = Math.pow(10, Math.floor(Math.log10(raw))), f = raw / p;
    return (f < 1.5 ? 1 : f < 3.5 ? 2 : f < 7.5 ? 5 : 10) * p;
  }
  function signed(v) { return (v < 0 ? '−' : '') + Math.abs(v).toFixed(1); }
  function waveColor() { return theme === 'dark' ? '#85B7EB' : '#378ADD'; }

  function layoutChart() {
    var w = ui.chart.clientWidth;
    if (!w) return;
    CW = w; CH = Math.round(w * 5 / 12);
    ui.chart.width = Math.round(CW * dpr); ui.chart.height = Math.round(CH * dpr);
    waveCache.key = '';
  }

  function showChart() {
    ui.chartWrap.hidden = !piChart;
    ui.zeroRow.hidden = !waves;
    fsHost.classList.toggle('charted', piChart);
    ui.piToggle.checked = piChart; ui.waveToggle.checked = waves; ui.gapToggle.checked = gapView;
    ui.zeros.value = zeroCount; ui.zeroOut.value = ui.zeroOut.textContent = zeroCount;
    if (piChart) layoutChart();
    schedule();
  }

  /* samples of the explicit formula, reused until the range, zero count or width changes */
  function waveSamples(X, K, cols) {
    var key = X + '|' + K + '|' + cols;
    if (waveCache.key === key) return waveCache;
    var xs = new Float64Array(cols + 1), ys = new Float64Array(cols + 1), top = 0;
    for (var c = 0; c <= cols; c++) {
      var x = 2 + (X - 2) * c / cols, y = explicitPi(x, K);
      xs[c] = x; ys[c] = y; if (y > top) top = y;
    }
    return (waveCache = { key: key, xs: xs, ys: ys, top: top });
  }

  function drawChart(ts) {
    if (!piChart || !CW) return;
    /* the waves cost a few ms per redraw, so while growing they update about ten times a second */
    if (waves && playing && ts - chartAt < 100) return;
    chartAt = ts;
    var X = Math.max(Math.min(T.N, 16), Math.min(T.N, Math.floor(Math.pow(2, L) + 1e-6)));
    var padL = 46, padR = 10, padT = 8, padB = 22, pw = CW - padL - padR, ph = CH - padT - padB;
    var count = piAt(X), smooth = Li(X), w = waves ? waveSamples(X, zeroCount, Math.round(pw * (playing ? 1 : 2))) : null;
    var accent = cssVar('--accent', '#d4a84b'), c = cctx, k, x, y, step, xa, xb;
    var sx = [], sy = [], wy = null, env = [];     /* staircase and waves as points, in the units being shown */
    var val = gapView ? function (x, y) { return y - Li(x); } : function (x, y) { return y; };

    /* the staircase: every step when they fit; otherwise each pixel column spans the counts inside it */
    sx.push(0); sy.push(0);
    if (count <= pw) {
      for (k = 0; k < count; k++) { x = T.P[k]; sx.push(x, x); sy.push(val(x, k), val(x, k + 1)); }
      sx.push(X); sy.push(val(X, count));
    } else {
      for (k = 1, xa = 2; k <= pw; k++, xa = xb) {
        xb = X * k / pw;
        if (gapView) {                         /* the gap's low and high inside the column, from a few samples */
          var gl = Infinity, gh = -Infinity;
          for (var q = 1; q <= 6; q++) { x = xa + (xb - xa) * q / 6; y = piAt(x) - Li(x); if (y < gl) gl = y; if (y > gh) gh = y; }
          sx.push(xb, xb); sy.push(gl, gh);
        }
        else { sx.push(xb); sy.push(piAt(xb)); }
      }
    }
    if (w) { wy = new Float64Array(w.ys.length); for (k = 0; k < wy.length; k++) wy[k] = val(w.xs[k], w.ys[k]); }
    /* Schoenfeld: if the Riemann Hypothesis holds, |π(x) − li(x)| < √x · ln x / 8π from x = 2657 on */
    if (gapView && X > 2657) for (k = 0; k <= pw; k++) { x = 2657 + (X - 2657) * k / pw; if (x >= 2657) env.push(x); }

    var lo = 0, hi = 1, grow = function (v) { if (v < lo) lo = v; if (v > hi) hi = v; };
    sy.forEach(grow); if (wy) wy.forEach(grow);
    if (gapView) { hi = Math.max(hi, 1); lo = Math.min(lo, -1); if (env.length) { grow(Math.sqrt(X) * Math.log(X) / (8 * Math.PI)); grow(-Math.sqrt(X) * Math.log(X) / (8 * Math.PI)); } }
    else grow(smooth);
    var pad = (hi - lo) * 0.06; hi += pad; if (gapView) lo -= pad;
    var px = function (x) { return padL + x / X * pw; }, py = function (y) { return padT + (hi - y) / (hi - lo) * ph; };

    c.setTransform(dpr, 0, 0, dpr, 0, 0);
    c.clearRect(0, 0, CW, CH);
    c.font = '11px ' + font; c.lineWidth = 1;

    /* grid and axes */
    c.fillStyle = muted;
    step = niceStep(X, Math.max(2, Math.floor(pw / 90)));
    c.textAlign = 'center'; c.textBaseline = 'top';
    for (x = step; x <= X; x += step) {
      c.beginPath(); c.moveTo(px(x), padT); c.lineTo(px(x), padT + ph); c.strokeStyle = line; c.stroke();
      c.fillText(fmtAxis(x), px(x), padT + ph + 6);
    }
    step = Math.max(1, niceStep(hi - lo, Math.max(2, Math.floor(ph / 40))));
    c.textAlign = 'right'; c.textBaseline = 'middle';
    for (y = Math.ceil(lo / step) * step; y <= hi; y += step) {
      c.beginPath(); c.moveTo(padL, py(y)); c.lineTo(padL + pw, py(y)); c.strokeStyle = y ? line : line2; c.stroke();
      c.fillText((y < 0 ? '−' : '') + fmtAxis(Math.abs(y)), padL - 8, py(y));
    }

    c.save();
    c.beginPath(); c.rect(padL, padT - 2, pw + 2, ph + 4); c.clip();
    c.lineJoin = 'round';

    /* Li(x): a curve, or in the gap view the zero line itself */
    c.beginPath();
    if (gapView) { c.moveTo(px(2), py(0)); c.lineTo(px(X), py(0)); }
    else for (k = 0; k <= pw; k++) { x = 2 + (X - 2) * k / pw; if (k) c.lineTo(px(x), py(Li(x))); else c.moveTo(px(x), py(0)); }
    c.strokeStyle = accent; c.lineWidth = 1.6; c.setLineDash([5, 4]); c.stroke();

    if (env.length) {
      [1, -1].forEach(function (sign) {
        c.beginPath();
        env.forEach(function (x, i) { var e = sign * Math.sqrt(x) * Math.log(x) / (8 * Math.PI); if (i) c.lineTo(px(x), py(e)); else c.moveTo(px(x), py(e)); });
        c.strokeStyle = muted; c.lineWidth = 1; c.setLineDash([2, 3]); c.stroke();
      });
    }
    c.setLineDash([]);

    /* Riemann's waves go under the staircase, wide enough to show where the two agree. In the gap
       view the true error is a jagged band a few primes tall, so there the waves go on top. */
    var stairs = function () {
      c.beginPath();
      for (k = 0; k < sx.length; k++) { if (k) c.lineTo(px(sx[k]), py(sy[k])); else c.moveTo(px(sx[k]), py(sy[k])); }
      c.strokeStyle = ink; c.lineWidth = 1.2; c.globalAlpha = gapView && wy ? 0.45 : 1; c.stroke(); c.globalAlpha = 1;
    };
    if (gapView) stairs();
    if (wy) {
      c.beginPath();
      for (k = 0; k < wy.length; k++) { if (k) c.lineTo(px(w.xs[k]), py(wy[k])); else c.moveTo(px(w.xs[k]), py(wy[k])); }
      c.strokeStyle = waveColor(); c.lineWidth = gapView ? 1.8 : 2.4; c.stroke();
    }
    if (!gapView) stairs();

    /* the selected prime sits at the top of its own step */
    if (sel > 0 && T.P[sel] <= X) {
      c.beginPath(); c.arc(px(T.P[sel]), py(val(T.P[sel], sel + 1)), 4, 0, TAU);
      c.fillStyle = genColor(T.gen[sel]); c.fill(); c.strokeStyle = ink; c.lineWidth = 1.2; c.stroke();
    }
    c.restore();

    var items = [[ink, '', gapView ? 'π(x) − Li(x) at ' + fmt(X) + ': ' + signed(count - smooth) : 'π(' + fmt(X) + ') = ' + fmt(count)],
                 [accent, 'dash', gapView ? 'Li(x)' : 'Li = ' + fmt(Math.round(smooth))]];
    if (w) items.push([waveColor(), '', zeroCount + (zeroCount === 1 ? ' zero' : ' zeros') + ': ' +
                       (gapView ? signed : function (v) { return v.toFixed(1); })(val(X, w.ys[w.ys.length - 1]))]);
    if (env.length) items.push([muted, 'dot', 'RH bound']);
    var key = items.map(function (it) { return it[2]; }).join('|');
    if (ui.chartKey._t !== key) {
      ui.chartKey._t = key; ui.chartKey.textContent = '';
      items.forEach(function (it) {
        var span = document.createElement('span'), sw = document.createElement('i');
        sw.style.borderColor = it[0]; sw.className = it[1];
        span.appendChild(sw); span.appendChild(document.createTextNode(it[2]));
        ui.chartKey.appendChild(span);
      });
    }
  }

  /* ---------- frame loop ---------- */

  function schedule() { if (!frameReq) frameReq = requestAnimationFrame(tick); }
  function tick(ts) {
    frameReq = 0;
    if (playing) {
      if (!lastTs) lastTs = ts;
      L = Math.min(T.exp, L + Math.min(ts - lastTs, 100) / 1000 * (T.exp - 1) / GROW_SECONDS);
      lastTs = ts;
      ui.grow.value = Math.round((L - 1) / (T.exp - 1) * 1000);
      if (L >= T.exp) { playing = false; setPlayButton(); }
    }
    draw(ts);
    if (playing) schedule();
  }

  function setPlayButton() {
    ui.playIcon.className = playing ? 'icon-pause' : 'icon-play';
    ui.play.setAttribute('aria-label', playing ? 'Pause' : L >= T.exp ? 'Replay' : 'Play');
  }
  function play() { if (L >= T.exp) { L = 1; sel = -1; clearNear(); writeHash(); } playing = true; lastTs = 0; setPlayButton(); schedule(); }
  function pause() { playing = false; setPlayButton(); schedule(); }
  function showAll() { playing = false; L = T.exp; ui.grow.value = 1000; setPlayButton(); schedule(); }

  /* ---------- view: pan and zoom ---------- */

  function clampView() {
    if (s <= 1.0001) { s = 1; tx = 0; ty = 0; }
    else {
      tx = Math.min(0, Math.max(W - W * s, tx));
      ty = Math.min(0, Math.max(W - W * s, ty));
    }
  }
  function zoomAt(px, py, factor) {
    var ns = Math.min(60, Math.max(1, s * factor)), f = ns / s;
    tx = px - (px - tx) * f; ty = py - (py - ty) * f; s = ns;
    clampView(); schedule();
  }
  function resetView() { s = 1; clampView(); schedule(); }
  function resetAngle() { spin = START_SPIN; tilt = START_TILT; resetView(); }

  function local(e) { var b = cv.getBoundingClientRect(); return { x: (e.clientX - b.left) * W / b.width, y: (e.clientY - b.top) * W / b.height }; }

  var pts = new Map(), down = null, moved = false, pinch = null;
  cv.addEventListener('pointerdown', function (e) {
    try { cv.setPointerCapture(e.pointerId); } catch (err) { /* ignore */ }
    var p = local(e); pts.set(e.pointerId, p);
    if (pts.size === 1) { down = p; moved = false; }
    if (pts.size === 2) { moved = true; pinch = pinchState(); }
  });
  function pinchState() {
    var a = Array.from(pts.values());
    return { d: Math.hypot(a[0].x - a[1].x, a[0].y - a[1].y) || 1, x: (a[0].x + a[1].x) / 2, y: (a[0].y + a[1].y) / 2 };
  }
  cv.addEventListener('pointermove', function (e) {
    if (!pts.has(e.pointerId)) return;
    var prev = pts.get(e.pointerId), p = local(e);
    pts.set(e.pointerId, p);
    if (pts.size === 1) {
      if (!moved && Math.hypot(p.x - down.x, p.y - down.y) > 6) moved = true;
      if (moved) {
        cv.classList.add('grab');
        if (e.shiftKey && s > 1) { tx += p.x - prev.x; ty += p.y - prev.y; clampView(); }
        else {
          /* once the stack is upside down, a sideways drag still follows the pointer */
          spin += (Math.cos(tilt) >= 0 ? 1 : -1) * (p.x - prev.x) * DRAG_SPEED;
          tilt += (p.y - prev.y) * DRAG_SPEED;
        }
        schedule();
      }
    } else if (pts.size === 2 && pinch) {
      var now = pinchState();
      tx += now.x - pinch.x; ty += now.y - pinch.y;
      zoomAt(now.x, now.y, now.d / pinch.d);
      pinch = now;
    }
  });
  function endPointer(e, cancelled) {
    if (!pts.has(e.pointerId)) return;
    if (!cancelled && pts.size === 1 && !moved) pick(local(e));
    pts.delete(e.pointerId);
    if (pts.size < 2) pinch = null;
    if (!pts.size) cv.classList.remove('grab');
  }
  cv.addEventListener('pointerup', function (e) { endPointer(e, false); });
  cv.addEventListener('pointercancel', function (e) { endPointer(e, true); });
  cv.addEventListener('wheel', function (e) {
    e.preventDefault();
    var p = local(e), dy = e.deltaMode === 1 ? e.deltaY * 16 : e.deltaY;
    zoomAt(p.x, p.y, Math.exp(-dy * 0.0015));
  }, { passive: false });
  cv.addEventListener('dblclick', function (e) { e.preventDefault(); resetAngle(); });
  ui.zin.addEventListener('click', function () { zoomAt(W / 2, W / 2, 1.6); });
  ui.zout.addEventListener('click', function () { zoomAt(W / 2, W / 2, 1 / 1.6); });
  ui.zreset.addEventListener('click', resetAngle);

  /* full screen holds the transport too, so the growth controls stay in reach */
  var fsHost = stage.parentNode;
  function fsElement() { return document.fullscreenElement || document.webkitFullscreenElement || null; }
  function syncFull() {
    var on = fsElement() === fsHost;
    fsHost.classList.toggle('is-full', on);
    ui.zfull.setAttribute('aria-label', on ? 'Exit full screen' : 'Enter full screen');
    ui.zfull.title = on ? 'Exit full screen' : 'Full screen';
  }
  /* unsupported on iPhone, and blocked in an iframe that doesn't allow it */
  if (!(fsHost.requestFullscreen || fsHost.webkitRequestFullscreen) || (document.fullscreenEnabled || document.webkitFullscreenEnabled) === false) ui.zfull.hidden = true;
  ui.zfull.addEventListener('click', function () {
    if (fsElement()) (document.exitFullscreen || document.webkitExitFullscreen).call(document);
    else (fsHost.requestFullscreen || fsHost.webkitRequestFullscreen).call(fsHost);
  });
  document.addEventListener('fullscreenchange', syncFull);
  document.addEventListener('webkitfullscreenchange', syncFull);

  function pick(p) {
    var m = upto(L), best = -1, bd = 22 * 22;
    for (var i = 0; i < m; i++) {
      if (i && genHidden(T.gen[i])) continue;
      var dx = SX[i] - p.x, dy = SY[i] - p.y, d = dx * dx + dy * dy;
      if (d < bd) { bd = d; best = i; }
    }
    sel = best; clearNear();
    if (playing) pause();
    writeHash(); schedule();
  }

  /* ---------- controls ---------- */

  ui.play.addEventListener('click', function () { if (playing) pause(); else play(); });
  ui.grow.addEventListener('input', function () {
    playing = false; L = 1 + ui.grow.value / 1000 * (T.exp - 1); setPlayButton(); schedule();
  });
  ui.boundForm.addEventListener('submit', function (e) {
    e.preventDefault();
    var raw = ui.bound.value.replace(/[\s,_]/g, '');
    if (!/^\d+$/.test(raw) || BigInt(raw) < BigInt(1)) { sayBound('Enter a positive integer.'); return; }
    var v = BigInt(raw);
    if (v > MAX_BOUND) { sayBound('The limit is ' + MAX_BOUND.toLocaleString('en-US') + '.'); return; }
    if (v === BigInt(1)) { stopRun(); sayBound('There are no primes up to 1.', true); return; }
    sayBound('');
    setBound(v, true);
    if (v > BigInt(TREE_MAX)) startRun();
  });
  ui.stop.addEventListener('click', function () { stopRun(); });
  ui.theme.addEventListener('click', function () { applyTheme(theme === 'dark' ? 'light' : 'dark'); store.set('pft-theme', theme); });
  ui.rootToggle.addEventListener('change', function () {
    rootP = ui.rootToggle.checked ? 2 : 0;
    if (rootP) { sel = -1; clearNear(); }        /* a selection would hide the list in the panel */
    applyRoot(); writeHash(); schedule();
  });
  ui.legend.addEventListener('click', function (e) {
    var b = e.target.closest('button');
    if (!b) return;
    if (b.dataset.g === 'all') genSel = null;
    else {
      genSel = genSel || {};
      if (genSel[b.dataset.g]) delete genSel[b.dataset.g]; else genSel[b.dataset.g] = 1;
      settleGens();
    }
    syncLegend(); writeHash(); schedule();
  });
  ui.ringToggle.addEventListener('change', function () { ringsByValue = ui.ringToggle.checked; writeHash(); schedule(); });
  ui.fillToggle.addEventListener('change', function () { fillFans = ui.fillToggle.checked; writeHash(); schedule(); });
  /* the waves are drawn on the chart, so turning them on brings the chart with them */
  ui.piToggle.addEventListener('change', function () {
    piChart = ui.piToggle.checked; if (!piChart) waves = gapView = false;
    showChart(); writeHash();
  });
  ui.waveToggle.addEventListener('change', function () {
    waves = ui.waveToggle.checked; if (waves) piChart = true;
    showChart(); writeHash();
  });
  ui.gapToggle.addEventListener('change', function () {
    gapView = ui.gapToggle.checked; if (gapView) piChart = true;
    showChart(); writeHash();
  });
  ui.zeros.addEventListener('input', function () {
    zeroCount = +ui.zeros.value; ui.zeroOut.value = ui.zeroOut.textContent = zeroCount;
    writeHash(); schedule();
  });
  ui.q.addEventListener('input', function () { ui.qerr.textContent = ''; });

  ui.find.addEventListener('submit', function (e) {
    e.preventDefault();
    var raw = ui.q.value.replace(/[\s,]/g, '');
    if (!raw) { say('Enter a prime number.'); return; }
    if (!/^\d+$/.test(raw) || +raw < 2) { say('Enter a whole number, 2 or larger.'); return; }
    var v = +raw;
    if (v > TREE_MAX) { say('Search goes up to ' + fmt(TREE_MAX) + '. Try a smaller prime.'); return; }
    if (isPrime(v)) focusPrime(v); else focusNearest(v);
  });

  function say(text, isNote) {
    ui.qerr.textContent = text;
    ui.qerr.classList.toggle('note', !!isNote);
  }

  function clearNear() { near = null; say(''); }

  function fitRange(v) {
    if (v <= T.N) return;
    var b = 2;
    while (b < v) b *= 2;
    setBound(BigInt(Math.min(b, TREE_MAX)), false);
  }

  function focusPrime(v) {
    fitRange(v);
    var i = T.idx[v];
    if (i < 0) return;
    sel = i; clearNear(); showAll(); writeHash();
  }

  /* v is a whole number >= 4 that isn't prime, so a prime exists on both sides */
  function focusNearest(v) {
    var lo = v - 1, hi = v + 1;
    while (!isPrime(lo)) lo--;
    while (!isPrime(hi)) hi++;
    if (hi > TREE_MAX) {                         /* the prime above is past the last tree */
      focusPrime(lo);
      say(fmt(v) + ' isn’t prime. Closest prime here is ' + fmt(lo) + '; the next, ' + fmt(hi) + ', is past this page’s limit.', true);
      return;
    }
    fitRange(hi);
    sel = -1; near = { v: v, lo: T.idx[lo], hi: T.idx[hi] };
    resetView(); showAll(); writeHash();
    say(fmt(v) + ' isn’t prime. Showing the closest primes, ' + fmt(lo) + ' and ' + fmt(hi) + '.', true);
  }

  /* a root outside this tree (not prime, or past the range) leaves every prime lit */
  function applyRoot() {
    var i = rootP >= 2 && rootP % 1 === 0 && rootP <= T.N ? T.idx[rootP] : -1;
    rootKids = i >= 0 ? T.kids[i] : null;
    marked = null;
    if (!rootKids) return;
    marked = new Uint8Array(T.n);
    marked[i] = 1;
    rootKids.forEach(function (k) { marked[k] = 1; });
  }

  function setBound(b, animate) {
    stopRun();
    put(ui.runStatus, '');
    bound = b;
    var N = b > BigInt(TREE_MAX) ? TREE_MAX : Number(b);
    if (!T || T.N !== N) {
      T = build(N);
      cnt = new Uint32Array(T.n);
      applyRoot();
      buildLegend();
    }
    showStats();
    ui.bound.value = fmtBig(b);
    sel = -1; clearNear(); s = 1; layout();
    if (animate && !reduceMotion && N <= ANIMATE_MAX) { L = 1; ui.grow.value = 0; play(); } else showAll();
    writeHash();
  }

  function showStats() {
    var drawn = fmt(T.n) + (T.n === 1 ? ' prime' : ' primes') + ' · ' + fmt(T.leaves) + ' with no children · deepest line ' +
      T.maxGen + (T.maxGen === 1 ? ' step' : ' steps');
    ui.stats.textContent = bound > BigInt(T.N) ? 'The tree stops at ' + fmt(T.N) + ': ' + drawn : drawn;
  }

  function fmtBig(b) { return b.toLocaleString('en-US'); }

  function sayBound(text, isNote) {
    ui.bounderr.textContent = text;
    ui.bounderr.classList.toggle('note', !!isNote);
  }

  /* ---------- counting past the tree, across workers ---------- */

  var run = null;

  function oddPrimesTo(limit) {
    var comp = new Uint8Array(limit + 1), total = 0, i, j;
    for (i = 3; i <= limit; i += 2) {
      if (comp[i]) continue;
      total++;
      for (j = i * i; j <= limit; j += 2 * i) comp[j] = 1;
    }
    var out = new Uint32Array(total), n = 0;
    for (i = 3; i <= limit; i += 2) if (!comp[i]) out[n++] = i;
    return out;
  }

  var referenceLoad = null, runToken = 0;

  /* primes-reference.json: exact counts at fixed points, so a run needn't start at 2.
     If it can't be read, counting still works from the beginning. */
  function loadReference() {
    if (!referenceLoad) {
      referenceLoad = fetch('primes-reference.json')
        .then(function (res) { return res.ok ? res.json() : []; })
        .catch(function () { return []; });
    }
    return referenceLoad;
  }

  function startRun() {
    var token = ++runToken;
    loadReference().then(function (ref) { if (token === runToken) beginRun(ref); });
  }

  function beginRun(ref) {
    var safe = BigInt(SAFE_MAX), start = null, known = null;
    ref.forEach(function (e) {
      var x = BigInt(e.x);
      if (x > bound) return;
      known = e;
      if (x <= safe) start = e;
    });
    var total = Math.max(1, Math.min((navigator.hardwareConcurrency || 2) - 1, 32));
    var target = bound > safe ? SAFE_MAX : Number(bound);
    var from = start ? Number(start.x) + 1 : 3;
    var r = { target: target, next: from, frontier: from, origin: from, start: start, known: known,
              count: start ? Number(start.pi) : 1, last: start ? Number(start.largest) : 2,
              t0: performance.now(), workers: [], done: new Map(), active: 0,
              base: new Uint32Array(0), baseLimit: 0, baseVersion: 0 };
    run = r;
    if (r.next > r.target) { finishRun(); return; }
    try {
      for (var i = 0; i < total; i++) r.workers.push(makeWorker(r));
    } catch (e) {
      stopRun();
      sayBound('This browser can’t run background workers here. Serve the page over http to count past the tree.');
      return;
    }
    r.workers.forEach(dispatch);
    r.timer = setInterval(showRun, 250);
    ui.stop.hidden = false; ui.runBar.hidden = false;
    showRun();
  }

  function makeWorker(r) {
    var w = new Worker('sieve-worker.js');
    w.baseVersion = 0;
    w.onmessage = function (e) {
      if (run !== r) return;
      r.active--;
      r.done.set(e.data.lo, e.data);
      while (r.done.has(r.frontier)) {           /* only trust an unbroken run from the start */
        var d = r.done.get(r.frontier);
        r.done.delete(r.frontier);
        r.count += d.count;
        if (d.last) r.last = d.last;
        r.frontier = d.hi;
      }
      dispatch(w);
      if (!r.active && r.next > r.target) finishRun();
    };
    w.onerror = function () {
      if (run !== r) return;
      stopRun();
      sayBound('A counting worker failed, so the count stopped early.');
    };
    return w;
  }

  function dispatch(w) {
    var r = run;
    if (!r || r.next > r.target) return;
    var lo = r.next, hi = Math.min(lo + SEGMENT, r.target + 1);
    var need = Math.ceil(Math.sqrt(hi)) + 1;
    if (need > r.baseLimit) {                    /* overshoot, so this rarely runs */
      r.baseLimit = Math.max(Math.ceil(need * 1.25), 1 << 16);
      r.base = oddPrimesTo(r.baseLimit);
      r.baseVersion++;
    }
    var job = { lo: lo, hi: hi };
    if (w.baseVersion !== r.baseVersion) { job.base = r.base; w.baseVersion = r.baseVersion; }
    r.next = hi; r.active++;
    w.postMessage(job);
  }

  function runLine(r) {
    return fmt(r.count) + ' primes up to ' + fmt(Math.max(2, r.frontier - 1)) + ' · largest ' + fmt(r.last);
  }

  function knownLine(r) {
    if (!r.known || BigInt(r.known.x) <= BigInt(SAFE_MAX)) return '';
    return '\nPublished: ' + BigInt(r.known.pi).toLocaleString('en-US') + ' primes up to ' + BigInt(r.known.x).toLocaleString('en-US');
  }

  function showRun() {
    var r = run, secs = (performance.now() - r.t0) / 1000, reached = r.frontier - 1, sieved = r.frontier - r.origin;
    var goal = Number(bound), share = reached / goal, left = (goal - reached) / (sieved / secs);
    ui.runBar.value = share;
    var pct = share < 0.0001 ? 'under 0.01%' : (share * 100).toFixed(2) + '%';
    put(ui.runStatus, 'Counting on ' + r.workers.length + (r.workers.length === 1 ? ' worker' : ' workers') + ' · ' + pct +
      (sieved > 0 ? ' · about ' + fmtSpan(left) + ' left' : '') + '\n' + runLine(r) + knownLine(r));
  }

  function fmtSpan(sec) {
    var units = [[3.156e7, 'year'], [86400, 'day'], [3600, 'hour'], [60, 'minute'], [1, 'second']];
    for (var i = 0; i < units.length; i++) if (sec >= units[i][0] || i === units.length - 1) {
      var v = sec / units[i][0];
      var n = v >= 1e15 ? v.toExponential(1) : fmt(Number(v.toPrecision(2)));
      return n + ' ' + units[i][1] + (v >= 1.5 ? 's' : '');
    }
  }

  function endRun() {
    var r = run;
    run = null;
    if (r.timer) clearInterval(r.timer);
    r.workers.forEach(function (w) { w.terminate(); });
    ui.stop.hidden = true; ui.runBar.hidden = true;
    return r;
  }

  function finishRun() {
    var r = endRun(), secs = (performance.now() - r.t0) / 1000;
    var capped = bound > BigInt(SAFE_MAX);
    var how = r.workers.length ? secs.toFixed(1) + ' s on ' + r.workers.length + (r.workers.length === 1 ? ' worker' : ' workers') : 'no sieving needed';
    var from = r.start ? ' · started at ' + fmt(Number(r.start.x)) : '';
    put(ui.runStatus, (capped ? 'Stopped at the 2⁵³ limit. ' : 'Exact count. ') + runLine(r) + ' · ' + how + from + knownLine(r));
  }

  function stopRun() {
    runToken++;                                  /* drop a run still waiting on the reference file */
    if (!run) return;
    var r = endRun();
    put(ui.runStatus, 'Stopped. ' + runLine(r) + knownLine(r));
  }

  function writeHash() {
    var h = 'max=' + bound + (near ? '&p=' + near.v : sel >= 0 ? '&p=' + T.P[sel] : '') + (rootP ? '&root=' + rootP : params.get('root') ? '&root=0' : '') +   /* root=0 outranks a ?root= in the query */
      (ringsByValue ? '&rings=value' : params.get('rings') ? '&rings=log' : '') +
      (genSel ? '&gen=' + genList().join(',') : params.get('gen') ? '&gen=all' : '') +
      (!fillFans ? '&fill=0' : params.get('fill') === '0' ? '&fill=1' : '') +   /* likewise for fill=0 in the query */
      (piChart ? '&pi=1' : params.get('pi') ? '&pi=0' : '') +
      (waves ? '&zeros=' + zeroCount : params.get('zeros') ? '&zeros=0' : '') +
      (gapView ? '&gap=1' : params.get('gap') ? '&gap=0' : '');
    try { window.history.replaceState(null, '', '#' + h); } catch (e) { /* sandboxed */ }
  }

  function parseBound(text) {
    if (!text || !/^\d+$/.test(text)) return null;
    var v = BigInt(text);
    return v >= BigInt(2) && v <= MAX_BOUND ? v : null;
  }

  /* ---------- start ---------- */

  var hp = new URLSearchParams(window.location.hash.replace(/^#/, ''));
  var startN = +(hp.get('n') || params.get('n'));
  var startBound = parseBound(hp.get('max') || params.get('max')) ||
    BigInt(startN >= 2 && startN <= 20 && startN % 1 === 0 ? Math.pow(2, startN) : 8192);
  var startP = +(hp.get('p') || params.get('p') || 0);

  rootP = +(hp.get('root') || params.get('root') || 0);
  fillFans = (hp.get('fill') || params.get('fill')) !== '0';
  genSel = parseGens(hp.get('gen') || params.get('gen'));
  ringsByValue = (hp.get('rings') || params.get('rings')) === 'value';
  var startZeros = +(hp.get('zeros') || params.get('zeros') || 0);
  waves = startZeros >= 1 && startZeros % 1 === 0;
  if (waves) zeroCount = Math.min(startZeros, ZERO_MAX);
  gapView = (hp.get('gap') || params.get('gap')) === '1';
  piChart = waves || gapView || (hp.get('pi') || params.get('pi')) === '1';

  bound = startBound;
  T = build(bound > BigInt(TREE_MAX) ? TREE_MAX : Number(bound)); cnt = new Uint32Array(T.n);
  applyRoot();
  ui.rootToggle.checked = rootP === 2;
  ui.fillToggle.checked = fillFans;
  ui.ringToggle.checked = ringsByValue;
  ui.bound.value = fmtBig(bound);
  showStats();
  /* a link never starts the CPU-heavy count on its own */
  if (bound > BigInt(TREE_MAX)) sayBound('Press Go to count past the tree. It uses most of your CPU until it ends or you stop it.', true);
  applyTheme(params.get('theme') || store.get('pft-theme') ||
    (window.matchMedia && window.matchMedia('(prefers-color-scheme: light)').matches ? 'light' : 'dark'));

  if (window.ResizeObserver) new ResizeObserver(layout).observe(stage);
  else window.addEventListener('resize', layout);
  layout();
  showChart();
  if (document.fonts && document.fonts.ready) document.fonts.ready.then(function () { font = getComputedStyle(document.body).fontFamily || font; ui.chain._t = ''; schedule(); });

  var startOk = startP >= 2 && startP % 1 === 0 && startP <= TREE_MAX;
  if (startOk && isPrime(startP)) focusPrime(startP);
  else if (startOk && startP >= 4) focusNearest(startP);
  else if (reduceMotion) showAll();
  else play();
})();
