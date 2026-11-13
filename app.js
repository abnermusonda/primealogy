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
    lineToggle: $('lineToggle'), planeToggle: $('planeToggle'), planeRow: $('planeRow'), solidToggle: $('solidToggle'), solidRow: $('solidRow'), piToggle: $('piToggle'), waveToggle: $('waveToggle'), gapToggle: $('gapToggle'), zeroRow: $('zeroRow'), zeros: $('zeros'), zeroOut: $('zeroOut'),
    chartWrap: $('chartWrap'), chartKey: $('chartKey'), chart: $('pichart'), psiToggle: $('psiToggle'),
    zetaToggle: $('zetaToggle'), zetaRow: $('zetaRow'), zt: $('zt'), ztOut: $('ztOut'), checkBtn: $('checkBtn'), checkOut: $('checkOut'),
    zetaWrap: $('zetaWrap'), zetaKey: $('zetaKey'), zplane: $('zplane'),
    fdivToggle: $('fdivToggle'), stackToggle: $('stackToggle'), stackRow: $('stackRow'), stackQ: $('stackQ'), sh: $('sh'), shOut: $('shOut'),
    progToggle: $('progToggle'), progLabel: $('progLabel'), stackCheck: $('stackCheck'), stackOut: $('stackOut'), stackWrap: $('stackWrap'), stackKey: $('stackKey'), lstack: $('lstack'),
    curveToggle: $('curveToggle'), curveRow: $('curveRow'), curveM: $('curveM'), curveWrap: $('curveWrap'), curveKey: $('curveKey'), fcurve: $('fcurve')
  };
  var cctx = ui.chart.getContext('2d'), zctx = ui.zplane.getContext('2d'), kctx = ui.lstack.getContext('2d'), fctx = ui.fcurve.getContext('2d');

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

    /* which primes divide a Fermat number: p | F_j exactly when 2^(2^j) ≡ −1 mod p, and j is below the power of 2 in p − 1 */
    var fdiv = new Int8Array(n), fdivList = [];
    for (i = 1; i < n; i++) {
      var pp = P[i], x2 = 2 % pp, left = pp - 1;
      for (j = 0; left % 2 === 0; j++, left /= 2) { if (x2 === pp - 1) { fdiv[i] = j + 1; fdivList.push(i); break; } x2 = x2 * x2 % pp; }
    }
    /* running sums over the primes in order: Σ ln p for ψ(x), and Σ −ln(1 − p⁻²) for the Euler product */
    var lnSum = new Float64Array(n + 1), euler = new Float64Array(n + 1);
    for (i = 0; i < n; i++) { lnSum[i + 1] = lnSum[i] + Math.log(P[i]); euler[i + 1] = euler[i] - Math.log(1 - 1 / (P[i] * P[i])); }
    var deep = 0, leaves = 0;
    for (i = 1; i < n; i++) if (gen[i] > gen[deep]) deep = i;
    for (i = 0; i < n; i++) if (!kids[i].length) leaves++;
    var factor = function (v) {
      var out = [];
      while (v > 1) { var q = spf[v], e = 0; while (v % q === 0) { v /= q; e++; } out.push([q, e]); }
      return out;
    };
    return { exp: exp, N: N, P: P, n: n, idx: idx, par: par, gen: gen, kids: kids, byGen: byGen, fans: fans, lg: lg, ang: ang,
             deep: deep, maxGen: gen[deep], leaves: leaves, factor: factor, lnSum: lnSum, euler: euler, fdiv: fdiv, fdivList: fdivList };
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
  var rootP = 0, marked = null;                  /* root=p filter, and a per-prime "stay bright" flag */
  var genSel = null;                             /* generations on show as { g: 1 }; null means all */
  var ringsByValue = false;                      /* ring radius follows a generation's largest prime itself, not its log */
  var fillFans = true;                           /* shade the sheet between each parent's children */
  var oneSolid = false;                          /* draw the primes as one solid, their convex hull, in place of everything else */
  var fillPlanes = false;                        /* shade the triangle of every three primes in a row on that line */
  var PLANE_FILL = [0, 0.07, 0.16, 0.3];         /* by how many layers the triangle spans: flat 2D, tilted 3D, three layers */
  var wholeLines = false;                        /* one line through all the primes in ascending order, instead of the edges */
  var fermatOnly = false;                        /* light only the primes that divide a Fermat number */
  var stackOn = false, stackK = 4, stackTop = 40, progOn = false;   /* the L-functions mod 2^stackK, and the chart of primes ≡ 1 mod it */
  var curveOn = false, curveM = 4;               /* Fermat curves x^m + y^m = 1 over finite fields */
  var hl = null;                                 /* what the highlight shows: { list, label, note, item } */
  var psiMode = false;                           /* weigh each prime by ln p: Chebyshev's ψ(x) in place of π(x) */
  var zetaPlane = false, zetaTop = 120;          /* the map of ζ(s) across the strip, up to height zetaTop */
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

  /* ---------- consent: the web fonts are the page's only outside request ---------- */

  var CONSENT_KEY = 'pft-consent-v1', FONTS = 'https://fonts.googleapis.com/css2?family=Outfit:wght@400;500&family=Playfair+Display:wght@500&display=swap';
  var privacy = $('privacy'), fontsLoaded = false;
  var consent = { accepted: store.get(CONSENT_KEY) === 'accepted', decided: store.get(CONSENT_KEY) !== null };

  function loadFonts() {
    if (fontsLoaded) return;
    fontsLoaded = true;
    [['preconnect', 'https://fonts.googleapis.com', false], ['preconnect', 'https://fonts.gstatic.com', true], ['stylesheet', FONTS, false]].forEach(function (l) {
      var el = document.createElement('link');
      el.rel = l[0]; el.href = l[1]; if (l[2]) el.crossOrigin = '';
      if (l[0] === 'stylesheet') el.onload = function () {
        if (document.fonts && document.fonts.ready) document.fonts.ready.then(function () { font = getComputedStyle(document.body).fontFamily || font; ui.chain._t = ''; ui.chartKey._t = ''; schedule(); });
      };
      document.head.appendChild(el);
    });
  }
  function syncPrivacy() {
    $('privacyWithdraw').hidden = !consent.accepted;
    $('privacyLocal').hidden = consent.accepted;
    $('privacyAccept').hidden = consent.accepted;
  }
  function setConsent(accepted) {
    consent.accepted = accepted; consent.decided = true;
    if (accepted) store.set(CONSENT_KEY, 'accepted'); else store.set(CONSENT_KEY, 'declined');
    if (accepted) loadFonts();
    syncPrivacy();
    if (privacy.open) privacy.close();
  }
  function openPrivacy() { syncPrivacy(); if (!privacy.open) { if (privacy.showModal) privacy.showModal(); else privacy.setAttribute('open', ''); } }
  $('privacyAccept').addEventListener('click', function () { setConsent(true); });
  $('privacyLocal').addEventListener('click', function () { setConsent(false); });
  $('privacyWithdraw').addEventListener('click', function () { setConsent(false); });   /* fonts already loaded stay for this visit; the next one starts without them */
  $('privacyOpen').addEventListener('click', openPrivacy);
  privacy.addEventListener('cancel', function (e) { e.preventDefault(); });              /* Escape isn't an answer; the buttons are */
  if (consent.accepted) loadFonts();
  else if (!consent.decided) openPrivacy();

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
    if (zetaPlane) layoutZeta();
    if (stackOn) layoutStack();
    if (curveOn) layoutCurve();
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

  /* with lines=1, one line runs through every prime in ascending order, 2 → 3 → 5 → 7 → 11 → …,
     up to the largest prime in the range; this is its step into prime i from the prime before it */
  function addStep(i) { ctx.moveTo(SX[i - 1], SY[i - 1]); ctx.lineTo(SX[i], SY[i]); }

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

    if (wholeLines && fillPlanes) {
      /* the triangle around each prime of this layer and its neighbours on the line, by layers spanned */
      ctx.fillStyle = c;
      for (var d = 1; d <= 3; d++) {
        ctx.beginPath();
        for (k = 0; k < list.length && (i = list[k]) < m - 1; k++) {
          var ga = T.gen[i - 1], gb = T.gen[i + 1];
          if ((1 + (ga !== g) + (gb !== g && gb !== ga)) !== d) continue;
          ctx.moveTo(SX[i - 1], SY[i - 1]); ctx.lineTo(SX[i], SY[i]); ctx.lineTo(SX[i + 1], SY[i + 1]); ctx.closePath();
        }
        ctx.globalAlpha = PLANE_FILL[d] * (marked ? DIM : 1) * f; ctx.fill();
      }
      ctx.globalAlpha = 1;
    }

    ctx.beginPath();
    for (k = 0; k < list.length && (i = list[k]) < m; k++) if (!(marked && marked[i])) { if (wholeLines) addStep(i); else addEdge(i); }
    ctx.strokeStyle = c; ctx.lineWidth = width;
    ctx.globalAlpha = (marked ? DIM * 0.5 : wholeLines ? (big ? 0.3 : 0.4) : big ? 0.45 : 0.55) * f;
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
    if (!wholeLines) drawRings(m);              /* the line reads better without the rings behind it */

    var solid = wholeLines && fillPlanes && oneSolid;
    cnt.fill(0);
    for (i = 1; i < m; i++) cnt[T.par[i]]++;
    /* painter's order: the layer farthest from the viewer first */
    if (solid) drawSolid(m);
    else for (k = 1; k <= T.maxGen; k++) {
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
    if (solid) { /* the solid would hide the line, so it isn't drawn on top of it */ }
    else if (pair) { trace(near.lo); trace(near.hi); }
    else if (f > 0 && !listing && (picked || !genSel)) trace(f);   /* the automatic line would cross hidden generations */

    /* labelled discs for 2, 3, 5, 17 */
    for (i = 0; i < Math.min(m, 8); i++) if (!solid && isBig(i) && !(i && genHidden(T.gen[i]))) {
      ctx.beginPath(); ctx.arc(SX[i], SY[i], dotSize(i), 0, TAU);
      ctx.fillStyle = i ? col[0] : ink;
      ctx.globalAlpha = marked && i && !marked[i] ? DIM : 1; ctx.fill();
      ctx.globalAlpha = 1;
      var scale = Math.sqrt(s) * SP[i] / fit;
      ctx.font = '500 ' + ((i ? 11 : 12) * scale) + 'px ' + font;
      ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
      ctx.fillStyle = paper; ctx.fillText(String(T.P[i]), SX[i], SY[i] + 0.5 * scale);
    }

    put(ui.chainLabel, listing ? hl.label : 'Line of descent');
    if (pair) { drawTags(near.lo, near.hi); describeNear(); }
    else if (listing) describeRoot(m);
    else describe(f, picked, m);
    put(ui.upto, 'up to ' + fmt(Math.min(T.N, Math.floor(Math.pow(2, L) + 1e-6))));
    put(ui.count, fmt(m) + (m === 1 ? ' prime' : ' primes'));
    drawChart(ts);
    drawZeta();
    drawStack();
    drawCurve();
  }

  /* ---------- one solid: the convex hull of the primes ---------- */

  /* The hull's corners must be corners of some layer's own outline, because each layer is flat.
     So each layer is cut down to its 2D hull first, which leaves a few hundred points even for
     big trees, and the 3D hull is grown from those one point at a time. */
  function layerHull(ids) {
    var pts = ids.slice().sort(function (a, b) { return WX[a] - WX[b] || WY[a] - WY[b]; });
    if (pts.length < 3) return pts;
    var cross = function (o, a, b) { return (WX[a] - WX[o]) * (WY[b] - WY[o]) - (WY[a] - WY[o]) * (WX[b] - WX[o]); };
    var lower = [], upper = [], k;
    for (k = 0; k < pts.length; k++) {
      while (lower.length >= 2 && cross(lower[lower.length - 2], lower[lower.length - 1], pts[k]) <= 0) lower.pop();
      lower.push(pts[k]);
    }
    for (k = pts.length - 1; k >= 0; k--) {
      while (upper.length >= 2 && cross(upper[upper.length - 2], upper[upper.length - 1], pts[k]) <= 0) upper.pop();
      upper.push(pts[k]);
    }
    return lower.slice(0, -1).concat(upper.slice(0, -1));
  }

  function hull3d(ids) {
    if (ids.length < 4) return [];
    var eps = 1e-7 * W, faces = [], k, i;
    var face = function (a, b, c) {
      var ux = WX[b] - WX[a], uy = WY[b] - WY[a], uz = WZ[b] - WZ[a];
      var vx = WX[c] - WX[a], vy = WY[c] - WY[a], vz = WZ[c] - WZ[a];
      var nx = uy * vz - uz * vy, ny = uz * vx - ux * vz, nz = ux * vy - uy * vx, len = Math.hypot(nx, ny, nz) || 1;
      nx /= len; ny /= len; nz /= len;
      return { a: a, b: b, c: c, nx: nx, ny: ny, nz: nz, d: nx * WX[a] + ny * WY[a] + nz * WZ[a], live: true };
    };
    var above = function (f, p) { return f.nx * WX[p] + f.ny * WY[p] + f.nz * WZ[p] - f.d; };

    /* a first tetrahedron from points far apart: the two ends in x, the farthest from their line,
       then the farthest from that plane */
    var p0 = ids[0], p1 = ids[0], p2 = -1, p3 = -1, best = 0, v;
    ids.forEach(function (p) { if (WX[p] < WX[p0]) p0 = p; if (WX[p] > WX[p1]) p1 = p; });
    if (p0 === p1) return [];
    ids.forEach(function (p) {
      var ax = WX[p1] - WX[p0], ay = WY[p1] - WY[p0], az = WZ[p1] - WZ[p0], bx = WX[p] - WX[p0], by = WY[p] - WY[p0], bz = WZ[p] - WZ[p0];
      v = Math.hypot(ay * bz - az * by, az * bx - ax * bz, ax * by - ay * bx);
      if (v > best) { best = v; p2 = p; }
    });
    if (p2 < 0 || best < eps) return [];
    var base = face(p0, p1, p2); best = 0;
    ids.forEach(function (p) { v = Math.abs(above(base, p)); if (v > best) { best = v; p3 = p; } });
    if (p3 < 0 || best < eps) return [];
    if (above(base, p3) > 0) { var t = p1; p1 = p2; p2 = t; }   /* keep every face's normal pointing out */
    faces.push(face(p0, p1, p2), face(p0, p3, p1), face(p1, p3, p2), face(p2, p3, p0));

    for (i = 0; i < ids.length; i++) {
      var p = ids[i];
      if (p === p0 || p === p1 || p === p2 || p === p3) continue;
      var seen = [], edges = new Map();
      for (k = 0; k < faces.length; k++) if (faces[k].live && above(faces[k], p) > eps) seen.push(faces[k]);
      if (!seen.length) continue;                  /* inside the hull so far */
      /* the horizon: edges of the faces p can see whose other side it can't */
      seen.forEach(function (f) {
        f.live = false;
        [[f.a, f.b], [f.b, f.c], [f.c, f.a]].forEach(function (e) {
          var back = e[1] + ',' + e[0];
          if (edges.has(back)) edges.delete(back); else edges.set(e[0] + ',' + e[1], e);
        });
      });
      edges.forEach(function (e) { faces.push(face(e[0], e[1], p)); });
      if (faces.length > 4 * ids.length + 64) faces = faces.filter(function (f) { return f.live; });
    }
    return faces.filter(function (f) { return f.live; });
  }

  var hullCache = { key: '', faces: [] };
  function solidHull(m) {
    var key = m + '|' + W + '|' + (genSel ? genList().join(',') : '');
    if (hullCache.key === key) return hullCache.faces;
    var ids = [0], g, k, list;
    for (g = 1; g <= T.maxGen; g++) {
      if (genHidden(g)) continue;
      list = [];
      for (k = 0; k < T.byGen[g].length && T.byGen[g][k] < m; k++) list.push(T.byGen[g][k]);
      ids = ids.concat(layerHull(list));
    }
    return (hullCache = { key: key, faces: hull3d(ids) }).faces;
  }

  function rgb(hex) { var n = parseInt(hex.slice(1), 16); return [n >> 16, (n >> 8) & 255, n & 255]; }

  /* lit from the upper left, in front; faces are drawn far to near so the solid hides itself */
  function drawSolid(m) {
    var faces = solidHull(m), lx = -0.45, ly = -0.6, lz = 0.66, order = [], k;
    var ramp = col.map(rgb);
    faces.forEach(function (f) {
      var z = 0, q;
      [f.a, f.b, f.c].forEach(function (p) { q = p; var y1 = WX[q] * sinS + WY[q] * cosS; z += y1 * sinT + WZ[q] * cosT; });
      order.push({ f: f, z: z });
    });
    order.sort(function (a, b) { return a.z - b.z; });
    ctx.lineJoin = 'round';
    for (k = 0; k < order.length; k++) {
      var f = order[k].f;
      var nx1 = f.nx * cosS - f.ny * sinS, ny1 = f.nx * sinS + f.ny * cosS;
      var ny2 = ny1 * cosT - f.nz * sinT, nz2 = ny1 * sinT + f.nz * cosT;
      var light = 0.28 + 0.72 * Math.max(0, nx1 * lx + ny2 * ly + nz2 * lz);
      var gz = (WZ[f.a] + WZ[f.b] + WZ[f.c]) / 3, g = layerGap ? Math.round(gz / layerGap + T.maxGen / 2) : 1;
      var c = ramp[Math.max(0, Math.min(ramp.length - 1, g - 1))];
      var fill = 'rgb(' + Math.round(c[0] * light) + ',' + Math.round(c[1] * light) + ',' + Math.round(c[2] * light) + ')';
      ctx.beginPath(); ctx.moveTo(SX[f.a], SY[f.a]); ctx.lineTo(SX[f.b], SY[f.b]); ctx.lineTo(SX[f.c], SY[f.c]); ctx.closePath();
      ctx.fillStyle = fill; ctx.fill();
      ctx.strokeStyle = fill; ctx.lineWidth = 0.8; ctx.stroke();       /* closes the hairline seams between faces */
    }
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
  function sub(e) { var d = '₀₁₂₃₄₅₆₇₈₉'; return String(e).split('').map(function (c) { return d[+c]; }).join(''); }
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
    var found = hl.list.filter(function (i) { return i < m; });
    put(ui.chain, found.length ? found.slice(0, LIST_MAX).map(hl.item).join(', ') + (found.length > LIST_MAX ? ', …' : '') : m >= T.n ? 'None' : 'None yet');
    setDetail(fmt(found.length) + ' of ' + fmt(T.n) + ' primes up to ' + fmt(T.N) + (hl.note ? '\n' + hl.note : ''));
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
  var zeroScan = { t: 50.5, z0: 0 };
  zetaZeros = [14.134725142, 21.022039639, 25.010857580, 30.424876126, 32.935061588,
               37.586178159, 40.918719012, 43.327073281, 48.005150881, 49.773832478];
  zeroScan.z0 = rsZ(zeroScan.t);
  /* scan upward in steps of 0.02 until the stop condition holds, bisecting each sign change */
  function extendZeros(stop) {
    var out = zetaZeros, t = zeroScan.t, h = 0.02, z0 = zeroScan.z0;
    while (!stop(out, t)) {
      var t1 = t + h, z1 = rsZ(t1);
      if ((z0 < 0) !== (z1 < 0)) {
        var lo = t, hi = t1, zl = z0;
        for (var i = 0; i < 40; i++) { var m = (lo + hi) / 2, zm = rsZ(m); if ((zm < 0) === (zl < 0)) { lo = m; zl = zm; } else hi = m; }
        out.push((lo + hi) / 2);
      }
      t = t1; z0 = z1;
    }
    zeroScan.t = t; zeroScan.z0 = z0;
    return out;
  }
  function getZeros() { return extendZeros(function (out) { return out.length >= ZERO_MAX; }); }
  function zerosUpTo(Tz) { return extendZeros(function (out, t) { return t > Tz; }); }

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

  /* ---------- Chebyshev's ψ(x) and its explicit formula ---------- */

  function thetaAt(x) { return T.lnSum[piAt(x)]; }        /* Σ ln p over p ≤ x */
  function psiAt(x) {                                      /* Σ ln p over prime powers p^k ≤ x */
    var v = 0;
    for (var k = 1; ; k++) { var r = Math.pow(x, 1 / k); if (r < 2) break; v += thetaAt(r); }
    return v;
  }
  /* ψ(x) = x − Σ_ρ x^ρ/ρ − ln 2π − ½ ln(1 − x⁻²); a zero and its mirror give 2√x (½ cos γu + γ sin γu)/(¼ + γ²) */
  function explicitPsi(x, K) {
    var u = Math.log(x), r = Math.sqrt(x), zs = getZeros(), v = x - Math.log(TAU) - 0.5 * Math.log(1 - 1 / (x * x));
    for (var k = 0; k < K; k++) { var g = zs[k]; v -= 2 * r * (0.5 * Math.cos(g * u) + g * Math.sin(g * u)) / (0.25 + g * g); }
    return v;
  }
  /* what the chart counts: every prime (π), every prime power by weight (ψ), or only those ≡ 1 mod 2^k */
  function chartMode() { return progOn && stackOn ? 'prog' : psiMode ? 'psi' : 'pi'; }
  function countAt(x) { var m = chartMode(); return m === 'prog' ? psiProgAt(x) : m === 'psi' ? psiAt(x) : piAt(x); }
  function smoothAt(x) { var m = chartMode(); return m === 'prog' ? x / (1 << (stackK - 1)) : m === 'psi' ? x : Li(x); }
  function explicitAt(x, K) { var m = chartMode(); return m === 'prog' ? explicitProg(x) : m === 'psi' ? explicitPsi(x, K) : explicitPi(x, K); }
  /* Schoenfeld's bounds under the Riemann Hypothesis: |π − li| < √x ln x / 8π from 2657, |ψ − x| < √x ln²x / 8π from 73.2 */
  function rhFrom() { var m = chartMode(); return m === 'prog' ? Infinity : m === 'psi' ? 73.2 : 2657; }
  function rhBound(x) { var l = Math.log(x); return Math.sqrt(x) * l * (psiMode ? l : 1) / (8 * Math.PI); }

  /* ---------- the zeta plane: ζ(s) off the line, and a count of its zeros ---------- */

  var B2K = [1 / 6, -1 / 30, 1 / 42, -1 / 30, 5 / 66, -691 / 2730, 7 / 6, -3617 / 510];
  var FACT = [1]; for (var fi = 1; fi <= 16; fi++) FACT[fi] = FACT[fi - 1] * fi;
  /* ζ(σ + it) by Euler–Maclaurin: N ≥ |t| terms of the series, then the integral, the half term and
     eight Bernoulli corrections. Good to about 10 places for Re s > −1 and the heights shown here. */
  function zeta(sig, t) {
    var N = Math.max(12, Math.ceil(Math.abs(t))), sr = 0, si = 0, n, ln, m;
    for (n = 1; n < N; n++) { ln = Math.log(n); m = Math.exp(-sig * ln); sr += m * Math.cos(t * ln); si -= m * Math.sin(t * ln); }
    ln = Math.log(N);
    var mag = Math.exp((1 - sig) * ln), pr = mag * Math.cos(-t * ln), pi = mag * Math.sin(-t * ln);   /* N^(1−s) */
    var dr = sig - 1, dd = dr * dr + t * t;
    sr += (pr * dr + pi * t) / dd; si += (pi * dr - pr * t) / dd;                                      /* ÷ (s − 1) */
    mag = Math.exp(-sig * ln); var nr = mag * Math.cos(t * ln), ni = -mag * Math.sin(t * ln);          /* N^−s */
    sr += nr / 2; si += ni / 2;
    var qr = 1, qi = 0, scale = N, invN2 = 1 / (N * N), k, j, c;
    for (k = 1; k <= 8; k++) {
      for (j = (k === 1 ? 0 : 2 * k - 3); j <= 2 * k - 2; j++) { var tr = qr * (sig + j) - qi * t, ti = qr * t + qi * (sig + j); qr = tr; qi = ti; }
      scale *= invN2;
      c = B2K[k - 1] / FACT[2 * k] * scale;
      sr += c * (qr * nr - qi * ni); si += c * (qr * ni + qi * nr);
    }
    return [sr, si];
  }

  /* N(T), the number of zeros with 0 < Im s < T anywhere in the strip, by the argument principle:
     N(T) = 1 + θ(T)/π + S(T), with S(T) the change in arg ζ along 2 → 2 + iT → ½ + iT, divided by π.
     On Re s = 2, |ζ − 1| < 1, so the argument there is the principal one. Along the top edge the
     step shrinks until the argument turns by less than one radian between samples. */
  function countByArgument(Tz) {
    var z = zeta(2, Tz), arg = Math.atan2(z[1], z[0]), prev = arg, sig = 2, step = 0.01, worst = 0;
    while (sig > 0.5 + 1e-12) {
      var ns = Math.max(0.5, sig - step), zz = zeta(ns, Tz), a = Math.atan2(zz[1], zz[0]), d = a - prev;
      while (d > Math.PI) d -= TAU; while (d < -Math.PI) d += TAU;
      if (Math.abs(d) > 1) { step /= 2; continue; }
      if (Math.abs(d) > worst) worst = Math.abs(d);
      arg += d; prev = a; sig = ns; step = Math.min(0.01, step * 1.5);
    }
    return { N: 1 + rsTheta(Tz) / Math.PI + arg / Math.PI, worst: worst };
  }

  function checkZeros() {
    var Tz = zetaTop;
    while (Math.abs(rsZ(Tz)) < 1e-3) Tz += 0.01;             /* the top edge must not pass through a zero */
    var byArg = countByArgument(Tz), n = Math.round(byArg.N), onLine = zerosBelow(Tz);
    var text;
    if (Math.abs(byArg.N - n) > 0.1) text = 'The argument count came out at ' + byArg.N.toFixed(3) + ', not near a whole number, so this height can’t be checked. Try another.';
    else text = 'Argument principle: ' + n + ' zeros with 0 < Im s < ' + Tz.toFixed(2) + ' anywhere in the strip. Sign changes of Z(t) on the line: ' + onLine + '. ' +
      (onLine === n ? 'So every zero below that height lies on Re s = ½ and is simple.' : 'The line is short by ' + (n - onLine) + ': a zero off the line, a double zero, or two zeros closer than the 0.02 scan.') +
      ' Largest turn of arg ζ between samples: ' + byArg.worst.toFixed(3) + ' rad.';
    put(ui.checkOut, text);
  }

  function zerosBelow(Tz) { var zs = zerosUpTo(Tz), n = 0; while (n < zs.length && zs[n] < Tz) n++; return n; }

  var ZW = 0, ZH = 0, zmap = document.createElement('canvas'), zmapKey = '';
  function hsl(h, s, l) {
    var a = s * Math.min(l, 1 - l), f = function (n) { var k = (n + h / 30) % 12; return l - a * Math.max(-1, Math.min(k - 3, 9 - k, 1)); };
    return [f(0) * 255, f(8) * 255, f(4) * 255];
  }
  function layoutZeta() {
    var w = ui.zplane.clientWidth;
    if (!w) return;
    ZW = w; ZH = Math.round(w / 3);
    ui.zplane.width = Math.round(ZW * dpr); ui.zplane.height = Math.round(ZH * dpr);
    zmapKey = '';
  }
  var S_LO = -0.5, S_HI = 1.5;                             /* the strip is 0 ≤ Re s ≤ 1; a margin shows the pole and beyond */
  function renderMap(cols, rows) {
    var img = zctx.createImageData(cols, rows), d = img.data, r, c, p = 0;
    for (r = 0; r < rows; r++) {
      var sig = S_HI - (S_HI - S_LO) * (r + 0.5) / rows;
      for (c = 0; c < cols; c++) {
        var t = zetaTop * (c + 0.5) / cols, z = zeta(sig, t), mag = Math.hypot(z[0], z[1]);
        var hue = (Math.atan2(z[1], z[0]) / TAU + 1) % 1 * 360;
        var light = 0.06 + 0.86 * (1 - Math.exp(-mag / 0.7));     /* dark at a zero, bright where |ζ| is large */
        var rgb = hsl(hue, 0.7, light);
        d[p++] = rgb[0]; d[p++] = rgb[1]; d[p++] = rgb[2]; d[p++] = 255;
      }
    }
    zmap.width = cols; zmap.height = rows;
    zmap.getContext('2d').putImageData(img, 0, 0);
  }
  function drawZeta() {
    if (!zetaPlane || !ZW) return;
    var padL = 46, padR = 10, padT = 8, padB = 22, pw = ZW - padL - padR, ph = ZH - padT - padB, c = zctx, k, t, step;
    var key = zetaTop + '|' + ZW;
    if (zmapKey !== key) { renderMap(Math.round(pw), Math.round(ph / 2)); zmapKey = key; }
    var px = function (t) { return padL + t / zetaTop * pw; }, py = function (sig) { return padT + (S_HI - sig) / (S_HI - S_LO) * ph; };
    c.setTransform(dpr, 0, 0, dpr, 0, 0);
    c.clearRect(0, 0, ZW, ZH);
    c.imageSmoothingEnabled = true;
    c.drawImage(zmap, padL, padT, pw, ph);
    c.font = '11px ' + font; c.lineWidth = 1;
    /* the strip's edges and the critical line */
    [[0, muted], [1, muted], [0.5, ink]].forEach(function (e) {
      c.beginPath(); c.moveTo(padL, py(e[0])); c.lineTo(padL + pw, py(e[0]));
      c.strokeStyle = e[1]; c.setLineDash(e[0] === 0.5 ? [4, 4] : [2, 3]); c.globalAlpha = 0.9; c.stroke();
    });
    c.setLineDash([]); c.globalAlpha = 1;
    /* the zeros */
    var zs = zerosUpTo(zetaTop), ring = Math.min(3.5, Math.max(1.5, pw / (3 * zerosBelow(zetaTop))));
    for (k = 0; k < zs.length && zs[k] < zetaTop; k++) {
      c.beginPath(); c.arc(px(zs[k]), py(0.5), ring, 0, TAU);
      c.strokeStyle = ink; c.lineWidth = 1.2; c.stroke();
    }
    /* axes */
    c.fillStyle = muted; c.textAlign = 'right'; c.textBaseline = 'middle';
    [[1, '1'], [0.5, '½'], [0, '0']].forEach(function (e) { c.fillText(e[1], padL - 8, py(e[0])); });
    c.save(); c.translate(11, padT + ph / 2); c.rotate(-Math.PI / 2); c.textAlign = 'center'; c.fillText('Re s', 0, 0); c.restore();
    c.textAlign = 'center'; c.textBaseline = 'top';
    step = niceStep(zetaTop, Math.max(2, Math.floor(pw / 80)));
    for (t = step; t <= zetaTop; t += step) c.fillText(fmtAxis(t), px(t), padT + ph + 6);
    c.textAlign = 'left'; c.fillText('Im s →', padL, padT + ph + 6);
    put(ui.zetaKey, 'Color is the phase of ζ(s); dark is small |ζ(s)|, the zeros. Bright at the left edge is the pole at s = 1. ' +
      k + (k === 1 ? ' zero' : ' zeros') + ' below ' + fmt(zetaTop) + ', ringed, all on the dashed line Re s = ½.');
  }
  function showZeta() {
    ui.zetaWrap.hidden = !zetaPlane; ui.zetaRow.hidden = !zetaPlane;
    ui.zetaToggle.checked = zetaPlane; ui.zt.value = zetaTop; ui.ztOut.value = ui.ztOut.textContent = zetaTop;
    fsHost.classList.toggle('zeta-on', zetaPlane);
    if (zetaPlane) layoutZeta();
    schedule();
  }

  /* ---------- Fermat curves over finite fields, where the Riemann Hypothesis is a theorem ---------- */

  function powmod(b, e, p) { var r = 1; b %= p; while (e > 0) { if (e & 1) r = r * b % p; b = b * b % p; e = Math.floor(e / 2); } return r; }
  function primitiveRoot(p) {
    var fs = T.factor(p - 1);
    for (var g = 2; g < p; g++) {
      var ok = true;
      for (var i = 0; i < fs.length; i++) if (powmod(g, (p - 1) / fs[i][0], p) === 1) { ok = false; break; }
      if (ok) return g;
    }
    return 1;
  }
  /* The curve x^m + y^m = 1 over F_p, for p ≡ 1 mod m. Weil (1949): its zeta function has 2g = (m−1)(m−2)
     zeros, the Jacobi sums α = −J(χ^a, χ^b) with a, b, a + b ≢ 0 mod m, and each has |α| = √p exactly.
     The number of points is then p + 1 − Σα, which is checked here against a direct count. */
  function fermatCurve(p, m) {
    var g = primitiveRoot(p), ind = new Uint8Array(p), u = 1, i, j, a, b;
    for (i = 0; i < p - 1; i++) { ind[u] = i % m; u = u * g % p; }
    var H = new Int32Array(m * m);
    for (u = 2; u < p; u++) H[ind[u] * m + ind[p + 1 - u]]++;
    var cs = new Float64Array(m), sn = new Float64Array(m);
    for (i = 0; i < m; i++) { cs[i] = Math.cos(TAU * i / m); sn[i] = Math.sin(TAU * i / m); }
    var n = (m - 1) * (m - 2), re = new Float64Array(n), im = new Float64Array(n), k = 0, sum = 0, dev = 0, root = Math.sqrt(p);
    for (a = 1; a < m; a++) for (b = 1; b < m; b++) {
      if ((a + b) % m === 0) continue;
      var jr = 0, ji = 0;
      for (i = 0; i < m; i++) for (j = 0; j < m; j++) { var h = H[i * m + j]; if (h) { var w = (a * i + b * j) % m; jr += h * cs[w]; ji += h * sn[w]; } }
      re[k] = -jr; im[k++] = -ji; sum -= jr;
      dev = Math.max(dev, Math.abs(Math.hypot(jr, ji) - root) / root);
    }
    /* the direct count uses no characters: every (x, y) with x^m + y^m = 1, plus the points at infinity */
    var pw = new Int32Array(p), x, N;
    for (x = 0; x < p; x++) pw[powmod(x, m, p)]++;
    N = pw[p - 1];
    for (u = 0; u < p; u++) N += pw[u] * pw[(p + 1 - u) % p];
    return { p: p, i: T.idx[p], re: re, im: im, points: N, ok: Math.abs(N - (p + 1 - sum)) < 1e-6, dev: dev };
  }

  var CURVE_MAX = 20000, curveCache = { m: 0, N: 0, next: 0, list: [], bad: 0, dev: 0 };
  function curveData(limit) {
    var c = curveCache;
    if (c.m !== curveM || c.N !== T.N) c = curveCache = { m: curveM, N: T.N, next: curveM + 1, list: [], bad: 0, dev: 0 };
    for (; c.next <= limit; c.next += c.m) if (T.idx[c.next] >= 0) {
      var r = fermatCurve(c.next, c.m);
      c.list.push(r); if (!r.ok) c.bad++; if (r.dev > c.dev) c.dev = r.dev;
    }
    return c;
  }

  var FW = 0, FH = 0, curveDrawn = '';
  function layoutCurve() {
    var w = ui.fcurve.clientWidth;
    if (!w) return;
    FW = w; FH = Math.round(w / 2);
    ui.fcurve.width = Math.round(FW * dpr); ui.fcurve.height = Math.round(FH * dpr);
    curveDrawn = '';
  }
  function drawCurve() {
    if (!curveOn || !FW) return;
    var limit = Math.min(T.N, CURVE_MAX, Math.floor(Math.pow(2, L) + 1e-6)), data = curveData(limit), list = data.list, n = 0, k, j, e;
    while (n < list.length && list[n].p <= limit) n++;
    var key = curveM + '|' + n + '|' + FW + '|' + theme + '|' + sel + '|' + T.N;
    if (key === curveDrawn) return;
    curveDrawn = key;
    var c = fctx, genus = (curveM - 1) * (curveM - 2) / 2, top = Math.max(limit, curveM + 1);
    c.setTransform(dpr, 0, 0, dpr, 0, 0);
    c.clearRect(0, 0, FW, FH);
    c.font = '11px ' + font; c.lineWidth = 1;

    /* left: every zero in the plane; the zeros of the curve over F_p lie on the circle of radius √p */
    var side = FH - 16, cx0 = 8 + side / 2, cy0 = FH / 2, R = side / 2 - 4, sc = R / Math.sqrt(top), dot = n > 400 ? 1.2 : n > 60 ? 1.8 : 2.6;
    c.strokeStyle = line; c.beginPath(); c.moveTo(cx0 - R, cy0); c.lineTo(cx0 + R, cy0); c.moveTo(cx0, cy0 - R); c.lineTo(cx0, cy0 + R); c.stroke();
    c.beginPath(); c.arc(cx0, cy0, R, 0, TAU); c.strokeStyle = line2; c.stroke();
    for (k = 0; k < n; k++) {
      e = list[k];
      var color = genColor(T.gen[e.i]), picked = e.i === sel;
      if (n <= 120 || picked) { c.beginPath(); c.arc(cx0, cy0, Math.sqrt(e.p) * sc, 0, TAU); c.strokeStyle = picked ? ink : color; c.globalAlpha = picked ? 1 : 0.3; c.lineWidth = picked ? 1.4 : 1; c.stroke(); c.globalAlpha = 1; }
      c.fillStyle = color;
      for (j = 0; j < e.re.length; j++) c.fillRect(cx0 + e.re[j] * sc - dot / 2, cy0 - e.im[j] * sc - dot / 2, dot, dot);
    }
    c.fillStyle = muted; c.textAlign = 'center'; c.textBaseline = 'bottom';
    c.fillText('radius √' + fmt(top), cx0, cy0 - R - 1 > 12 ? cy0 - R + 13 : 12);

    /* right: points on the curve minus p + 1, against the bound 2g√p that those circles force */
    var x0 = 8 + side + 58, x1 = FW - 10, y0 = 12, y1 = FH - 24, mid = (y0 + y1) / 2, span = 2 * genus * Math.sqrt(top) * 1.08;
    var qx = function (p) { return x0 + p / top * (x1 - x0); }, qy = function (v) { return mid - v / span * (y1 - y0) / 2; };
    if (x1 - x0 > 80) {
      var step = niceStep(top, Math.max(2, Math.floor((x1 - x0) / 80)));
      c.textAlign = 'center'; c.textBaseline = 'top'; c.fillStyle = muted;
      for (k = step; k <= top; k += step) { c.beginPath(); c.moveTo(qx(k), y0); c.lineTo(qx(k), y1); c.strokeStyle = line; c.stroke(); c.fillText(fmtAxis(k), qx(k), y1 + 6); }
      step = niceStep(2 * span, 4);
      c.textAlign = 'right'; c.textBaseline = 'middle';
      for (k = -Math.floor(span / step) * step; k <= span; k += step) { c.beginPath(); c.moveTo(x0, qy(k)); c.lineTo(x1, qy(k)); c.strokeStyle = k ? line : line2; c.stroke(); c.fillText((k < 0 ? '−' : '') + fmtAxis(Math.abs(k)), x0 - 8, qy(k)); }
      [1, -1].forEach(function (sign) {
        c.beginPath();
        for (k = 0; k <= 120; k++) { var p = top * k / 120, v = sign * 2 * genus * Math.sqrt(p); if (k) c.lineTo(qx(p), qy(v)); else c.moveTo(qx(p), qy(v)); }
        c.strokeStyle = muted; c.setLineDash([2, 3]); c.stroke(); c.setLineDash([]);
      });
      for (k = 0; k < n; k++) {
        e = list[k];
        c.beginPath(); c.arc(qx(e.p), qy(e.points - e.p - 1), e.i === sel ? 4 : n > 400 ? 1.3 : 2, 0, TAU);
        c.fillStyle = genColor(T.gen[e.i]); c.fill();
        if (e.i === sel) { c.strokeStyle = ink; c.lineWidth = 1.2; c.stroke(); }
      }
    }
    var zeros = n * 2 * genus;
    put(ui.curveKey, 'x' + sup(curveM) + ' + y' + sup(curveM) + ' = 1 over 𝔽ₚ, for the ' + fmt(n) + (n === 1 ? ' prime' : ' primes') + ' p ≡ 1 mod ' + curveM + ' up to ' + fmt(limit) +
      ', in the tree’s colors. Left: the ' + fmt(zeros) + ' zeros of their zeta functions; each curve’s ' + 2 * genus + ' lie on a circle of radius √p. ' +
      'Right: points on the curve minus p + 1, inside the bound ±' + 2 * genus + '√p. ' +
      (n ? (data.bad ? data.bad + ' point counts disagree with the zeros.' : 'All ' + fmt(n) + ' point counts were checked by counting directly, and every zero is on its circle to ' + Math.min(15, Math.floor(-Math.log10(data.dev || 1e-16))) + ' digits.') : ''));
  }
  function showCurve() {
    ui.curveWrap.hidden = !curveOn; ui.curveRow.hidden = !curveOn;
    ui.curveToggle.checked = curveOn; ui.curveM.value = curveM;
    if (curveOn) layoutCurve();
    schedule();
  }

  /* ---------- the L-function stack: Dirichlet characters mod 2^k ---------- */

  /* (Z/2^c)* is generated by −1 and 5: n = (−1)^u 5^v, and χ(n) = (−1)^(e·u) · exp(2πi·j·v / 2^(c−2)).
     Returns the primitive characters of conductor 4, 8, …, 2^k: a table of values, the parity a, and
     half the argument of the root number ε = τ(χ) / (i^a √q), from the Gauss sum τ. */
  function charsMod2(k) {
    var out = [];
    for (var c = 2; c <= k; c++) {
      var q = 1 << c, V = Math.max(1, q >> 2), U = new Int8Array(q), Vv = new Int32Array(q), x = 1, v, e, j, n;
      for (v = 0; v < V; v++) { U[x] = 0; Vv[x] = v; U[q - x] = 1; Vv[q - x] = v; x = x * 5 % q; }
      for (e = 0; e < 2; e++) for (j = 0; j < V; j++) {
        if (c === 2 ? !(e === 1 && j === 0) : j % 2 === 0) continue;      /* primitive: χ(5) has full order */
        var re = new Float64Array(q), im = new Float64Array(q), tr = 0, ti = 0;
        for (n = 1; n < q; n += 2) { var ang = TAU * j * Vv[n] / V + (e && U[n] ? Math.PI : 0); re[n] = Math.cos(ang); im[n] = Math.sin(ang); }
        for (n = 1; n < q; n += 2) { var w = TAU * n / q, cw = Math.cos(w), sw = Math.sin(w); tr += re[n] * cw - im[n] * sw; ti += re[n] * sw + im[n] * cw; }
        out.push({ q: q, a: e, re: re, im: im, half: -Math.atan2(e ? -tr : ti, e ? ti : tr) / 2 });
      }
    }
    return out;
  }
  /* Σ_{i≥0} (β + i)^−s by Euler–Maclaurin: the integral, the half term and eight Bernoulli corrections */
  function emTail(beta, sig, t) {
    var ln = Math.log(beta), mag = Math.exp((1 - sig) * ln), pr = mag * Math.cos(t * ln), pi = -mag * Math.sin(t * ln);
    var dr = sig - 1; if (dr === 0 && t === 0) dr = 1e-9;       /* the pole terms cancel across a character, but not as 0/0 */
    var dd = dr * dr + t * t, sr = (pr * dr + pi * t) / dd, si = (pi * dr - pr * t) / dd;
    mag = Math.exp(-sig * ln); var nr = mag * Math.cos(t * ln), ni = -mag * Math.sin(t * ln);
    sr += nr / 2; si += ni / 2;
    var qr = 1, qi = 0, scale = beta, inv2 = 1 / (beta * beta), k, j, c;
    for (k = 1; k <= 8; k++) {
      for (j = (k === 1 ? 0 : 2 * k - 3); j <= 2 * k - 2; j++) { var a = qr * (sig + j) - qi * t, b = qr * t + qi * (sig + j); qr = a; qi = b; }
      scale *= inv2; c = B2K[k - 1] / FACT[2 * k] * scale;
      sr += c * (qr * nr - qi * ni); si += c * (qr * ni + qi * nr);
    }
    return [sr, si];
  }
  /* L(σ + it, χ): the first qM terms, then the rest residue by residue through emTail */
  function lfun(ch, sig, t) {
    var q = ch.q, M = Math.max(8, Math.ceil(Math.abs(t) / 2)), sr = 0, si = 0, n, ln, mag, c, s;
    for (n = 1; n < q * M; n += 2) {
      var r = n % q; ln = Math.log(n); mag = Math.exp(-sig * ln); c = mag * Math.cos(t * ln); s = -mag * Math.sin(t * ln);
      sr += ch.re[r] * c - ch.im[r] * s; si += ch.re[r] * s + ch.im[r] * c;
    }
    var tr = 0, ti = 0;
    for (var a = 1; a < q; a += 2) { var tl = emTail(M + a / q, sig, t); tr += ch.re[a] * tl[0] - ch.im[a] * tl[1]; ti += ch.re[a] * tl[1] + ch.im[a] * tl[0]; }
    ln = Math.log(q); mag = Math.exp(-sig * ln); c = mag * Math.cos(t * ln); s = -mag * Math.sin(t * ln);
    return [sr + tr * c - ti * s, si + tr * s + ti * c];
  }
  /* Im ln Γ(x + iy): eight steps up, then Stirling's series */
  function imLogGamma(x, y) {
    var acc = 0, j;
    for (j = 0; j < 8; j++) acc -= Math.atan2(y, x + j);
    x += 8;
    var th = Math.atan2(y, x), r2 = x * x + y * y, ir = x / r2, ii = -y / r2;
    var i3i = ii * (3 * ir * ir - ii * ii), i3r = ir * (ir * ir - 3 * ii * ii), i2r = ir * ir - ii * ii, i2i = 2 * ir * ii;
    return acc + (x - 0.5) * th + y * 0.5 * Math.log(r2) - y + ii / 12 - i3i / 360 + (i3r * i2i + i3i * i2r) / 1260;
  }
  function lTheta(ch, t) { return t / 2 * Math.log(ch.q / Math.PI) + imLogGamma((0.5 + ch.a) / 2, t / 2); }
  /* the functional equation makes this real on the line: Z(t, χ) = Re[e^{iθ(t)} ε^{−1/2} L(½ + it, χ)] */
  function lZ(ch, t) { var v = lfun(ch, 0.5, t), ph = lTheta(ch, t) + ch.half; return v[0] * Math.cos(ph) - v[1] * Math.sin(ph); }

  /* Zeros of every character at once, as sign changes of Z. One table of n^−½ e^{−it ln n}, folded by
     residue mod 2^k, serves them all. The scan starts on the real axis because a zero can sit very low
     (one character mod 128 has a zero at height 0.018), and a dip that turns back without crossing is
     searched for a pair of zeros inside a single step. */
  function stackZeros(k, H, h) {
    var q = 1 << k, chars = charsMod2(k), lnq = Math.log(q), t, n, a, ci, i;
    var Sr = new Float64Array(q), Si = new Float64Array(q), zeros = chars.map(function () { return []; });
    function allZ(t, out) {
      var M = Math.max(8, Math.ceil(t / 2));
      Sr.fill(0); Si.fill(0);
      for (n = 1; n < q * M; n += 2) { var ln = Math.log(n), mag = 1 / Math.sqrt(n), r = n % q; Sr[r] += mag * Math.cos(t * ln); Si[r] -= mag * Math.sin(t * ln); }
      var mq = Math.exp(-0.5 * lnq), cq = mq * Math.cos(t * lnq), sq = -mq * Math.sin(t * lnq);
      for (a = 1; a < q; a += 2) { var tl = emTail(M + a / q, 0.5, t); Sr[a] += tl[0] * cq - tl[1] * sq; Si[a] += tl[0] * sq + tl[1] * cq; }
      for (ci = 0; ci < chars.length; ci++) {
        var ch = chars[ci], lr = 0, li = 0;
        for (a = 1; a < q; a += 2) { var r2 = a % ch.q; lr += ch.re[r2] * Sr[a] - ch.im[r2] * Si[a]; li += ch.re[r2] * Si[a] + ch.im[r2] * Sr[a]; }
        var ph = lTheta(ch, t) + ch.half;
        out[ci] = lr * Math.cos(ph) - li * Math.sin(ph);
      }
    }
    function root(ch, lo, hi, flo, fhi) {              /* regula falsi between heights where Z changes sign */
      var x = lo, fx;
      for (i = 0; i < 14; i++) {
        x = (lo * fhi - hi * flo) / (fhi - flo); fx = lZ(ch, x);
        if (Math.abs(fx) < 1e-11) break;
        if ((fx < 0) === (flo < 0)) { lo = x; flo = fx; fhi /= 2; } else { hi = x; fhi = fx; flo /= 2; }
      }
      return x;
    }
    var old = new Float64Array(chars.length), prev = new Float64Array(chars.length), cur = new Float64Array(chars.length), steps = 0;
    allZ(0, prev);
    for (t = h; t <= H + h; t += h, steps++) {
      allZ(t, cur);
      for (ci = 0; ci < chars.length; ci++) {
        if ((prev[ci] < 0) !== (cur[ci] < 0)) { var x = root(chars[ci], t - h, t, prev[ci], cur[ci]); if (x < H) zeros[ci].push(x); }
        else if (steps && (old[ci] < 0) === (prev[ci] < 0) && Math.abs(prev[ci]) < Math.abs(old[ci]) && Math.abs(prev[ci]) < Math.abs(cur[ci])) {
          var sgn = prev[ci] < 0 ? -1 : 1, lo = t - 2 * h, hi = t, g = 0.6180339887, x1 = hi - g * (hi - lo), x2 = lo + g * (hi - lo);
          var f1 = sgn * lZ(chars[ci], x1), f2 = sgn * lZ(chars[ci], x2);
          for (i = 0; i < 24 && f1 > 0 && f2 > 0; i++) {
            if (f1 < f2) { hi = x2; x2 = x1; f2 = f1; x1 = hi - g * (hi - lo); f1 = sgn * lZ(chars[ci], x1); }
            else { lo = x1; x1 = x2; f1 = f2; x2 = lo + g * (hi - lo); f2 = sgn * lZ(chars[ci], x2); }
          }
          var xm = f1 < f2 ? x1 : x2, fm = Math.min(f1, f2);
          if (fm < 0) {
            var za = root(chars[ci], t - 2 * h, xm, old[ci], sgn * fm), zb = root(chars[ci], xm, t, sgn * fm, cur[ci]);
            if (za < H) zeros[ci].push(za); if (zb < H) zeros[ci].push(zb);
          }
        }
      }
      var tmp = old; old = prev; prev = cur; cur = tmp;
    }
    zeros.forEach(function (z) { z.sort(function (p, r) { return p - r; }); });
    return { chars: chars, zeros: zeros };
  }

  /* zeros of L(s, χ) with 0 < Im s < T anywhere in the strip. The completed function Λ satisfies
     Λ(s) = ε·conj Λ(1 − conj s), so half the contour is enough: N = [θ(T) + Δ arg L]/π, with arg L
     followed along ½ → 2 → 2 + iT → ½ + iT. */
  function argTrack(ch, s0, t0, s1, t1) {
    var z = lfun(ch, s0, t0), prev = Math.atan2(z[1], z[0]), total = 0, u = 0, step = 0.02;
    while (u < 1 - 1e-12) {
      var nu = Math.min(1, u + step), zz = lfun(ch, s0 + (s1 - s0) * nu, t0 + (t1 - t0) * nu), a = Math.atan2(zz[1], zz[0]), d = a - prev;
      while (d > Math.PI) d -= TAU; while (d < -Math.PI) d += TAU;
      if (Math.abs(d) > 0.8 && step > 1e-6) { step /= 2; continue; }
      total += d; prev = a; u = nu; step = Math.min(0.02, step * 1.5);
    }
    return total;
  }
  function lCount(ch, Tz) {
    var z0 = lfun(ch, 2, 0), z1 = lfun(ch, 2, Tz);      /* |L − 1| < 1 on Re s = 2, so principal values do there */
    return (lTheta(ch, Tz) + argTrack(ch, 0.5, 0, 2, 0) + Math.atan2(z1[1], z1[0]) - Math.atan2(z0[1], z0[0]) + argTrack(ch, 2, Tz, 0.5, Tz)) / Math.PI;
  }
  /* the constant b(χ) of the explicit formula: L′/L at 0 for odd χ; for even χ, where L(0) = 0, what is left after the 1/s pole */
  function bConst(ch) {
    var h = 1e-3, p = lfun(ch, h, 0), m = lfun(ch, -h, 0), z = lfun(ch, 0, 0);
    var d1r = (p[0] - m[0]) / (2 * h), d1i = (p[1] - m[1]) / (2 * h), d2r = (p[0] - 2 * z[0] + m[0]) / (h * h), d2i = (p[1] - 2 * z[1] + m[1]) / (h * h);
    var nr = ch.a ? d1r : d2r / 2, ni = ch.a ? d1i : d2i / 2, dr = ch.a ? z[0] : d1r, di = ch.a ? z[1] : d1i;
    return (nr * dr + ni * di) / (dr * dr + di * di);
  }

  var STACK_H = 80, stackCache = {}, stackBusy = false;
  /* rows[0] is ζ itself, then the characters by conductor; each row holds its zeros below STACK_H */
  function buildStack(k) {
    var st = stackZeros(k, STACK_H, 0.04), rows = [{ q: 1, ch: null, zeros: zerosUpTo(STACK_H).filter(function (z) { return z < STACK_H; }) }], bsum = 0, evens = 0, odds = 0;
    st.chars.forEach(function (ch, i) { rows.push({ q: ch.q, ch: ch, zeros: st.zeros[i] }); bsum += bConst(ch); if (ch.a) odds++; else evens++; });
    return { k: k, rows: rows, bsum: bsum, evens: evens, odds: odds };
  }
  function stackData(k) {
    if (stackCache[k]) return stackCache[k];
    if (!stackBusy) {
      stackBusy = true;
      setTimeout(function () { stackCache[k] = buildStack(k); stackBusy = false; waveCache.key = ''; stackDrawn = ''; schedule(); }, 30);
    }
    return null;
  }
  function stackZerosBelow(data, H) { var out = []; data.rows.forEach(function (r) { for (var i = 0; i < r.zeros.length && r.zeros[i] < H; i++) out.push(r.zeros[i]); }); return out; }

  /* ψ(x; q, 1) = Σ ln p over prime powers p^j ≤ x with p^j ≡ 1 mod q: the primes that can divide F_n when q = 2^(n+2) */
  var progCache = { q: 0, N: 0 }, progZeros = { key: '', arr: [] };
  function progData() {
    var q = 1 << stackK, c = progCache, i;
    if (c.q === q && c.N === T.N) return c;
    c = progCache = { q: q, N: T.N, pref: new Float64Array(T.n + 1), list: [], pv: [], pc: [0] };
    for (i = 0; i < T.n; i++) { var on = T.P[i] % q === 1; c.pref[i + 1] = c.pref[i] + (on ? Math.log(T.P[i]) : 0); if (on) c.list.push(i); }
    var pows = [];
    for (i = 1; i < T.n && T.P[i] * T.P[i] <= T.N; i++) for (var pw = T.P[i] * T.P[i]; pw <= T.N; pw *= T.P[i]) if (pw % q === 1) pows.push([pw, Math.log(T.P[i])]);
    pows.sort(function (a, b) { return a[0] - b[0]; });
    pows.forEach(function (e) { c.pv.push(e[0]); c.pc.push(c.pc[c.pc.length - 1] + e[1]); });
    return c;
  }
  function psiProgAt(x) {
    var c = progData(), lo = 0, hi = c.pv.length;
    while (lo < hi) { var m = (lo + hi) >> 1; if (c.pv[m] <= x) lo = m + 1; else hi = m; }
    return c.pref[piAt(x)] + c.pc[lo];
  }
  /* Its explicit formula sums the one for ψ(x, χ) over every character mod q. The trivial character gives
     ψ(x) less the powers of 2; each other one gives −Σ x^ρ/ρ − (1 − a) ln x − b(χ) + Σ_m x^(a−2m)/(2m − a).
     Zeros of χ and of its conjugate pair up, so every zero adds the same 2·Re(x^ρ/ρ) wave as for ζ. */
  function explicitProg(x) {
    var data = stackCache[stackK], key = stackK + '|' + stackTop;
    if (progZeros.key !== key) progZeros = { key: key, arr: stackZerosBelow(data, stackTop) };
    var u = Math.log(x), r = Math.sqrt(x), half = 0.5 * Math.log(1 - 1 / (x * x)), zs = progZeros.arr;
    var v = x - Math.log(TAU) - half - Math.floor(Math.log2(x) + 1e-12) * Math.LN2;
    v -= data.evens * (u + half) + data.bsum - data.odds * 0.5 * Math.log((x + 1) / (x - 1));
    for (var k = 0; k < zs.length; k++) { var g = zs[k]; v -= 2 * r * (0.5 * Math.cos(g * u) + g * Math.sin(g * u)) / (0.25 + g * g); }
    return v / (1 << (stackK - 1));
  }

  var KW = 0, KH = 0, stackDrawn = '';
  function layoutStack() {
    var w = ui.lstack.clientWidth;
    if (!w) return;
    KW = w; KH = Math.round(w / 2);
    ui.lstack.width = Math.round(KW * dpr); ui.lstack.height = Math.round(KH * dpr);
    stackDrawn = '';
  }
  function stackColor(q) { return q === 1 ? ink : col[Math.round(Math.log2(q)) - 2]; }
  function drawStack() {
    if (!stackOn || !KW) return;
    var data = stackData(stackK), q = 1 << stackK;
    if (!data) { put(ui.stackKey, 'Finding the zeros of ' + (q / 2) + ' L-functions…'); return; }
    var key = stackK + '|' + stackTop + '|' + KW + '|' + theme;
    if (key === stackDrawn) return;
    stackDrawn = key;
    var c = kctx, rows = data.rows, n = rows.length, padL = 40, padR = 12, padT = 10, padB = 22, pw = KW - padL - padR, ph = KH - padT - padB;
    var dy = Math.min(44, (ph - 8) / n), th = Math.max(1.5, Math.min(dy * 0.72, 13)), shear = th * 1.1, r, k, total = 0, lastQ = 0, first = 0;
    var px = function (t) { return padL + t / stackTop * (pw - shear); };
    c.setTransform(dpr, 0, 0, dpr, 0, 0);
    c.clearRect(0, 0, KW, KH);
    c.font = '11px ' + font; c.lineWidth = 1;
    var labelY = Infinity;
    var label = function (qq, from, to) {              /* one label per conductor, at the middle of its sheets, where there is room */
      var y = padT + ph - 4 - (from + to) / 2 * dy - th / 2;
      if (labelY - y < 12) return;
      labelY = y;
      c.fillStyle = muted; c.textAlign = 'right'; c.textBaseline = 'middle';
      c.fillText(qq === 1 ? 'ζ' : String(qq), padL - 8, y);
    };
    /* back to front, so nearer sheets overlap the ones behind */
    for (r = n - 1; r >= 0; r--) {
      var row = rows[r], y0 = padT + ph - 4 - r * dy, color = stackColor(row.q), rad = Math.max(0.9, Math.min(2.6, th * 0.32));
      c.beginPath(); c.moveTo(px(0), y0); c.lineTo(px(stackTop), y0); c.lineTo(px(stackTop) + shear, y0 - th); c.lineTo(px(0) + shear, y0 - th); c.closePath();
      c.fillStyle = color; c.globalAlpha = 0.13; c.fill();
      c.strokeStyle = color; c.globalAlpha = 0.4; c.stroke(); c.globalAlpha = 1;
      c.beginPath();
      for (k = 0; k < row.zeros.length && row.zeros[k] < stackTop; k++) { var zx = px(row.zeros[k]) + shear / 2, zy = y0 - th / 2; c.moveTo(zx + rad, zy); c.arc(zx, zy, rad, 0, TAU); total++; }
      c.fillStyle = color; c.fill();
    }
    for (r = 0; r <= n; r++) if (r === n || rows[r].q !== lastQ) { if (r) label(lastQ, first, r - 1); if (r < n) { lastQ = rows[r].q; first = r; } }
    c.fillStyle = muted; c.textAlign = 'center'; c.textBaseline = 'top';
    var step = niceStep(stackTop, Math.max(2, Math.floor(pw / 80)));
    for (k = step; k <= stackTop; k += step) c.fillText(fmtAxis(k), px(k), padT + ph + 6);
    c.textAlign = 'left'; c.fillText('Im s →', padL, padT + ph + 6);
    put(ui.stackKey, n + ' L-functions, one sheet each: ζ(s) at the front, then the ' + (n - 1) + (n === 2 ? ' character' : ' characters') + ' mod ' + q +
      ' by conductor. The dots are their ' + fmt(total) + ' zeros below ' + stackTop + ', each on the middle of its sheet, where Re s = ½.');
  }
  function checkStack() {
    var data = stackCache[stackK];
    if (!data) { put(ui.stackOut, 'Still finding the zeros. Try again in a moment.'); return; }
    var Tz = stackTop + 0.0137, bad = [], byArg = 0, onLine = 0, clash = true;
    while (clash) { clash = false; data.rows.forEach(function (r) { r.zeros.forEach(function (z) { if (Math.abs(z - Tz) < 1e-3) clash = true; }); }); if (clash) Tz += 0.0041; }
    data.rows.forEach(function (r) {
      var raw = r.ch ? lCount(r.ch, Tz) : countByArgument(Tz).N, n = Math.round(raw), line = 0;
      while (line < r.zeros.length && r.zeros[line] < Tz) line++;
      byArg += n; onLine += line;
      if (n !== line || Math.abs(raw - n) > 0.1) bad.push((r.q === 1 ? 'ζ' : 'a character of conductor ' + r.q) + ' (' + raw.toFixed(2) + ' against ' + line + ')');
    });
    put(ui.stackOut, 'Argument principle: ' + fmt(byArg) + ' zeros with 0 < Im s < ' + Tz.toFixed(2) + ' across the ' + data.rows.length + ' L-functions, anywhere in the strip. Sign changes on the line: ' + fmt(onLine) + '. ' +
      (bad.length ? 'They disagree for ' + bad.join(', ') + '.' : 'They agree for every one, so each of these zeros lies on Re s = ½ and is simple: the generalized Riemann Hypothesis holds here below that height.'));
  }
  function showStack() {
    ui.stackWrap.hidden = !stackOn; ui.stackRow.hidden = !stackOn;
    ui.stackToggle.checked = stackOn; ui.stackQ.value = 1 << stackK; ui.sh.value = stackTop; ui.shOut.value = ui.shOut.textContent = stackTop;
    ui.progToggle.checked = progOn; ui.progLabel.textContent = 'Chart only the primes ≡ 1 mod ' + (1 << stackK);
    if (stackOn) layoutStack();
    schedule();
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
    ui.piToggle.checked = piChart; ui.waveToggle.checked = waves; ui.gapToggle.checked = gapView; ui.psiToggle.checked = psiMode;
    ui.zeros.value = zeroCount; ui.zeroOut.value = ui.zeroOut.textContent = zeroCount;
    if (piChart) layoutChart();
    schedule();
  }

  /* samples of the explicit formula, reused until the range, zero count or width changes */
  function waveSamples(X, K, cols) {
    var key = X + '|' + K + '|' + cols + '|' + chartMode() + '|' + stackK + '|' + stackTop;
    if (waveCache.key === key) return waveCache;
    var xs = new Float64Array(cols + 1), ys = new Float64Array(cols + 1), top = 0;
    for (var c = 0; c <= cols; c++) {
      var x = 2 + (X - 2) * c / cols, y = explicitAt(x, K);
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
    var mode = chartMode(), ready = mode !== 'prog' || !!stackData(stackK);     /* the progression's waves wait for its zeros */
    var count = countAt(X), smooth = smoothAt(X), w = waves && ready ? waveSamples(X, zeroCount, Math.round(pw * (playing ? 1 : 2))) : null;
    var accent = cssVar('--accent', '#d4a84b'), c = cctx, k, x, y, step, xa, xb;
    var sx = [], sy = [], wy = null, env = [];     /* staircase and waves as points, in the units being shown */
    var val = gapView ? function (x, y) { return y - smoothAt(x); } : function (x, y) { return y; };

    /* the staircase: every step when they fit; otherwise each pixel column spans the counts inside it */
    sx.push(0); sy.push(0);
    if (mode === 'pi' && count <= pw) {
      for (k = 0; k < count; k++) { x = T.P[k]; sx.push(x, x); sy.push(val(x, k), val(x, k + 1)); }
      sx.push(X); sy.push(val(X, count));
    } else {
      for (k = 1, xa = 2; k <= pw; k++, xa = xb) {
        xb = X * k / pw;
        if (gapView) {                         /* the gap's low and high inside the column, from a few samples */
          var gl = Infinity, gh = -Infinity;
          for (var q = 1; q <= 6; q++) { x = xa + (xb - xa) * q / 6; y = countAt(x) - smoothAt(x); if (y < gl) gl = y; if (y > gh) gh = y; }
          sx.push(xb, xb); sy.push(gl, gh);
        }
        else { sx.push(xb); sy.push(countAt(xb)); }
      }
    }
    if (w) { wy = new Float64Array(w.ys.length); for (k = 0; k < wy.length; k++) wy[k] = val(w.xs[k], w.ys[k]); }
    var from = rhFrom();
    if (gapView && X > from) for (k = 0; k <= pw; k++) env.push(from + (X - from) * k / pw);

    var lo = 0, hi = 1, grow = function (v) { if (v < lo) lo = v; if (v > hi) hi = v; };
    sy.forEach(grow); if (wy) wy.forEach(grow);
    if (gapView) { hi = Math.max(hi, 1); lo = Math.min(lo, -1); if (env.length) { grow(rhBound(X)); grow(-rhBound(X)); } }
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
    else for (k = 0; k <= pw; k++) { x = 2 + (X - 2) * k / pw; if (k) c.lineTo(px(x), py(smoothAt(x))); else c.moveTo(px(x), py(0)); }
    c.strokeStyle = accent; c.lineWidth = 1.6; c.setLineDash([5, 4]); c.stroke();

    if (env.length) {
      [1, -1].forEach(function (sign) {
        c.beginPath();
        env.forEach(function (x, i) { var e = sign * rhBound(x); if (i) c.lineTo(px(x), py(e)); else c.moveTo(px(x), py(e)); });
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
      c.beginPath(); c.arc(px(T.P[sel]), py(val(T.P[sel], countAt(T.P[sel]))), 4, 0, TAU);
      c.fillStyle = genColor(T.gen[sel]); c.fill(); c.strokeStyle = ink; c.lineWidth = 1.2; c.stroke();
    }
    c.restore();

    var fn = mode === 'pi' ? 'π' : 'ψ', arg2 = mode === 'prog' ? '; ' + (1 << stackK) + ', 1' : '', sm = mode === 'pi' ? 'Li' : mode === 'psi' ? 'x' : 'x/' + (1 << (stackK - 1));
    var fc = mode === 'pi' ? fmt : function (v) { return fmt(Math.round(v)); };
    var items = [[ink, '', gapView ? fn + '(x' + arg2 + ') − ' + sm + ' at ' + fmt(X) + ': ' + signed(count - smooth) : fn + '(' + fmt(X) + arg2 + ') = ' + fc(count)],
                 [accent, 'dash', gapView ? sm + (mode === 'pi' ? '(x)' : '') : sm + ' = ' + fmt(Math.round(smooth))]];
    if (w) items.push([waveColor(), '', (mode === 'prog' ? fmt(progZeros.arr.length) + ' zeros below ' + stackTop : zeroCount + (zeroCount === 1 ? ' zero' : ' zeros')) + ': ' +
                       (gapView ? signed : function (v) { return v.toFixed(1); })(val(X, w.ys[w.ys.length - 1]))]);
    if (env.length) items.push([muted, 'dot', 'RH bound']);
    /* the primes so far, fed back into Euler's product: ∏ 1/(1 − p⁻²) → ζ(2) = π²/6 */
    if (mode === 'pi' && !gapView) items.push([paper, '', '∏ 1/(1 − p⁻²) = ' + Math.exp(T.euler[count]).toFixed(5) + ' → π²/6 = 1.64493']);
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
  function syncPlaneRows() { ui.planeRow.hidden = !wholeLines; ui.solidRow.hidden = !(wholeLines && fillPlanes); }
  ui.lineToggle.addEventListener('change', function () { wholeLines = ui.lineToggle.checked; syncPlaneRows(); writeHash(); schedule(); });
  ui.planeToggle.addEventListener('change', function () { fillPlanes = ui.planeToggle.checked; syncPlaneRows(); writeHash(); schedule(); });
  ui.solidToggle.addEventListener('change', function () { oneSolid = ui.solidToggle.checked; writeHash(); schedule(); });
  ui.fillToggle.addEventListener('change', function () { fillFans = ui.fillToggle.checked; writeHash(); schedule(); });
  /* the waves are drawn on the chart, so turning them on brings the chart with them */
  ui.piToggle.addEventListener('change', function () {
    piChart = ui.piToggle.checked; if (!piChart) waves = gapView = psiMode = false;
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
  ui.fdivToggle.addEventListener('change', function () {
    fermatOnly = ui.fdivToggle.checked;
    if (fermatOnly) { sel = -1; clearNear(); }
    applyRoot(); writeHash(); schedule();
  });
  ui.stackToggle.addEventListener('change', function () { stackOn = ui.stackToggle.checked; if (!stackOn) progOn = false; applyRoot(); showStack(); showChart(); writeHash(); });
  ui.stackQ.addEventListener('change', function () { stackK = Math.round(Math.log2(+ui.stackQ.value)); put(ui.stackOut, ''); applyRoot(); showStack(); writeHash(); });
  ui.sh.addEventListener('input', function () { stackTop = +ui.sh.value; ui.shOut.value = ui.shOut.textContent = stackTop; put(ui.stackOut, ''); writeHash(); schedule(); });
  ui.progToggle.addEventListener('change', function () {
    progOn = ui.progToggle.checked;
    if (progOn) { piChart = true; sel = -1; clearNear(); }
    applyRoot(); showChart(); writeHash();
  });
  ui.stackCheck.addEventListener('click', function () { put(ui.stackOut, 'Checking…'); setTimeout(checkStack, 20); });
  ui.curveToggle.addEventListener('change', function () { curveOn = ui.curveToggle.checked; showCurve(); writeHash(); });
  ui.curveM.addEventListener('change', function () { curveM = +ui.curveM.value; writeHash(); schedule(); });
  ui.psiToggle.addEventListener('change', function () { psiMode = ui.psiToggle.checked; if (psiMode) piChart = true; showChart(); writeHash(); });
  ui.zetaToggle.addEventListener('change', function () { zetaPlane = ui.zetaToggle.checked; showZeta(); writeHash(); });
  ui.zt.addEventListener('input', function () { zetaTop = +ui.zt.value; ui.ztOut.value = ui.ztOut.textContent = zetaTop; put(ui.checkOut, ''); writeHash(); schedule(); });
  ui.checkBtn.addEventListener('click', function () { put(ui.checkOut, 'Checking…'); setTimeout(checkZeros, 20); });
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
    var i = rootP >= 2 && rootP % 1 === 0 && rootP <= T.N ? T.idx[rootP] : -1, plain = function (k) { return String(T.P[k]); };
    marked = null; hl = null;
    /* one highlight at a time: Fermat divisors, then the progression on the chart, then the root filter */
    if (fermatOnly) hl = { list: T.fdivList, label: 'Dividing a Fermat number', note: 'p divides Fₙ when 2 has order 2ⁿ⁺¹ mod p',
                           item: function (k) { return T.P[k] + ' | F' + sub(T.fdiv[k] - 1); } };
    else if (progOn && stackOn) hl = { list: progData().list, label: 'One more than a multiple of ' + (1 << stackK),
                                       note: stackK >= 4 ? 'Every prime factor of F' + sub(stackK - 2) + ' is one of these' : '', item: plain };
    else if (i >= 0) hl = { list: T.kids[i], label: 'Hanging directly from ' + rootP, note: rootP === 2 ? 'Fermat primes: p − 1 is a power of 2' : '', item: plain };
    if (!hl) return;
    marked = new Uint8Array(T.n);
    if (!fermatOnly && !(progOn && stackOn) && i >= 0) marked[i] = 1;
    hl.list.forEach(function (k) { marked[k] = 1; });
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
      (oneSolid ? '&solid=1' : params.get('solid') ? '&solid=0' : '') +
      (fillPlanes ? '&planes=1' : params.get('planes') ? '&planes=0' : '') +
      (wholeLines ? '&lines=1' : params.get('lines') ? '&lines=0' : '') +
      (piChart ? '&pi=1' : params.get('pi') ? '&pi=0' : '') +
      (waves ? '&zeros=' + zeroCount : params.get('zeros') ? '&zeros=0' : '') +
      (gapView ? '&gap=1' : params.get('gap') ? '&gap=0' : '') +
      (psiMode ? '&psi=1' : params.get('psi') ? '&psi=0' : '') +
      (zetaPlane ? '&zeta=' + zetaTop : params.get('zeta') ? '&zeta=0' : '') +
      (stackOn ? '&stack=' + (1 << stackK) + (stackTop !== 40 ? '&sh=' + stackTop : '') + (progOn ? '&prog=1' : '') : params.get('stack') ? '&stack=0' : '') +
      (curveOn ? '&curve=' + curveM : params.get('curve') ? '&curve=0' : '') +
      (fermatOnly ? '&fdiv=1' : params.get('fdiv') ? '&fdiv=0' : '');
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
  wholeLines = (hp.get('lines') || params.get('lines')) === '1';
  fillPlanes = (hp.get('planes') || params.get('planes')) === '1';
  oneSolid = (hp.get('solid') || params.get('solid')) === '1';
  var startZeros = +(hp.get('zeros') || params.get('zeros') || 0);
  waves = startZeros >= 1 && startZeros % 1 === 0;
  if (waves) zeroCount = Math.min(startZeros, ZERO_MAX);
  gapView = (hp.get('gap') || params.get('gap')) === '1';
  psiMode = (hp.get('psi') || params.get('psi')) === '1';
  piChart = waves || gapView || psiMode || (hp.get('pi') || params.get('pi')) === '1';
  var startStack = +(hp.get('stack') || params.get('stack') || 0), startSh = +(hp.get('sh') || params.get('sh') || 0), startCurve = +(hp.get('curve') || params.get('curve') || 0);
  stackOn = [4, 8, 16, 32, 64, 128].indexOf(startStack) >= 0;
  if (stackOn) stackK = Math.round(Math.log2(startStack));
  if (startSh >= 10 && startSh <= 80) stackTop = Math.round(startSh / 5) * 5;
  progOn = stackOn && (hp.get('prog') || params.get('prog')) === '1';
  if (progOn) piChart = true;
  curveOn = [3, 4, 8, 16].indexOf(startCurve) >= 0;
  if (curveOn) curveM = startCurve;
  fermatOnly = (hp.get('fdiv') || params.get('fdiv')) === '1';
  var startZeta = +(hp.get('zeta') || params.get('zeta') || 0);
  zetaPlane = startZeta >= 30;
  if (zetaPlane) zetaTop = Math.min(390, Math.round(startZeta / 10) * 10);

  bound = startBound;
  T = build(bound > BigInt(TREE_MAX) ? TREE_MAX : Number(bound)); cnt = new Uint32Array(T.n);
  applyRoot();
  ui.rootToggle.checked = rootP === 2;
  ui.fdivToggle.checked = fermatOnly;
  ui.fillToggle.checked = fillFans;
  ui.ringToggle.checked = ringsByValue;
  ui.lineToggle.checked = wholeLines;
  ui.planeToggle.checked = fillPlanes; ui.solidToggle.checked = oneSolid; syncPlaneRows();
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
  showZeta();
  showStack();
  showCurve();

  var startOk = startP >= 2 && startP % 1 === 0 && startP <= TREE_MAX;
  if (startOk && isPrime(startP)) focusPrime(startP);
  else if (startOk && startP >= 4) focusNearest(startP);
  else if (reduceMotion) showAll();
  else play();
})();
