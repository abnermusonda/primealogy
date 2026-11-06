/*
 * The prime family tree
 * Every prime p > 2 is drawn as a child of the largest prime factor of p - 1.
 * The result is a single tree rooted at 2, laid out radially:
 *   radius = log2(p), angle = a wedge proportional to the number of leaves below,
 *   color = generation (steps back to 2).
 * No dependencies. Works as a standalone page or inside an iframe (?embed=1).
 */
(function () {
  'use strict';

  var TAU = Math.PI * 2;
  var GAP = 0.22;                       /* empty wedge at 12 o'clock that holds the ring labels */
  var A0 = -Math.PI / 2 + GAP / 2;
  var A1 = 1.5 * Math.PI - GAP / 2;
  var GROW_SECONDS = 15;                /* one full growth animation */
  var MAX_N_EXP = 16;
  var RANGES = [10, 12, 13, 14, 16];
  var RAMPS = {
    dark:  ['#F2D28A', '#EF9F27', '#ED93B1', '#AFA9EC', '#85B7EB', '#5DCAA5', '#9FE1CB', '#E1F5EE', '#FFFFFF'],
    light: ['#BA7517', '#EF9F27', '#D4537E', '#7F77DD', '#378ADD', '#1D9E75', '#0F6E56', '#04342C', '#000000']
  };

  var $ = function (id) { return document.getElementById(id); };
  var stage = $('stage'), cv = $('tree'), ctx = cv.getContext('2d');
  var off = document.createElement('canvas'), octx = off.getContext('2d');
  var ui = {
    play: $('play'), playIcon: $('playIcon'), grow: $('grow'), upto: $('upto'), count: $('count'),
    chain: $('chain'), detail: $('detail'), find: $('find'), q: $('q'), qerr: $('qerr'),
    range: $('range'), stats: $('stats'), legend: $('legend'), theme: $('theme'),
    zin: $('zin'), zout: $('zout'), zreset: $('zreset')
  };

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

  function build(exp) {
    var N = 1 << exp;
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
    var par = new Int32Array(n).fill(-1), gen = new Uint8Array(n), kids = [];
    var lg = new Float64Array(n), wt = new Float64Array(n), ang = new Float64Array(n);
    for (i = 0; i < n; i++) kids.push([]);
    lg[0] = 1;
    for (i = 1; i < n; i++) {
      j = idx[gpf(P[i] - 1)];
      par[i] = j; gen[i] = gen[j] + 1; kids[j].push(i); lg[i] = Math.log2(P[i]);
    }
    for (i = n - 1; i >= 0; i--) { if (!kids[i].length) wt[i] = 1; if (i) wt[par[i]] += wt[i]; }
    (function place(k, a0, a1) {
      ang[k] = (a0 + a1) / 2;
      var a = a0, c = kids[k];
      for (var t = 0; t < c.length; t++) { var w = (a1 - a0) * wt[c[t]] / wt[k]; place(c[t], a, a + w); a += w; }
    })(0, A0, A1);

    var deep = 0, leaves = 0;
    for (i = 1; i < n; i++) if (gen[i] > gen[deep]) deep = i;
    for (i = 0; i < n; i++) if (!kids[i].length) leaves++;
    var factor = function (v) {
      var out = [];
      while (v > 1) { var q = spf[v], e = 0; while (v % q === 0) { v /= q; e++; } out.push([q, e]); }
      return out;
    };
    return { exp: exp, N: N, P: P, n: n, idx: idx, par: par, gen: gen, kids: kids, lg: lg, ang: ang,
             deep: deep, maxGen: gen[deep], leaves: leaves, factor: factor };
  }

  /* ---------- state ---------- */

  var T = null;                                  /* the current tree */
  var X, Y, cnt;                                 /* world positions, live child counts */
  var W = 0, dpr = 1, cx = 0, cy = 0, unit = 0;
  var s = 1, tx = 0, ty = 0;                     /* view: screen = world * s + t */
  var L = 1;                                     /* growth front, in log2 units */
  var playing = false, lastTs = 0, sel = -1, shown = 0, shownAt = 0;
  var needBake = true, frameReq = 0;
  var theme = 'dark', col = RAMPS.dark, ink = '#eef1f6', muted = '#7d8aa1', line = 'rgba(255,255,255,.09)', line2 = 'rgba(255,255,255,.16)';
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
    ink = cssVar('--ink', ink); muted = cssVar('--muted', muted); line = cssVar('--line', line); line2 = cssVar('--line-2', line2);
    font = getComputedStyle(document.body).fontFamily || font;
    ui.theme.textContent = theme === 'dark' ? 'Switch to light' : 'Switch to dark';
    var meta = document.querySelector('meta[name="theme-color"]');
    if (meta) meta.setAttribute('content', cssVar('--bg', '#0a1424'));
    buildLegend();
    needBake = true; schedule();
  }

  function buildLegend() {
    if (!T) return;
    ui.legend.textContent = '';
    for (var g = 1; g <= T.maxGen; g++) {
      var sp = document.createElement('span'), sw = document.createElement('i');
      sw.style.background = col[g - 1];
      sp.appendChild(sw); sp.appendChild(document.createTextNode(String(g)));
      ui.legend.appendChild(sp);
    }
  }

  /* ---------- geometry ---------- */

  function layout() {
    var w = stage.clientWidth;
    if (!w) return;
    W = w; dpr = Math.min(window.devicePixelRatio || 1, 3);
    cv.width = cv.height = off.width = off.height = Math.round(W * dpr);
    cx = cy = W / 2; unit = (W / 2 - 14) / T.exp;
    X = new Float64Array(T.n); Y = new Float64Array(T.n);
    for (var i = 0; i < T.n; i++) {
      var r = i ? T.lg[i] * unit : 0;
      X[i] = cx + r * Math.cos(T.ang[i]); Y[i] = cy + r * Math.sin(T.ang[i]);
    }
    clampView(); needBake = true; schedule();
  }

  function edgePath(c, i, segs) {
    var j = T.par[i], r0 = j ? T.lg[j] * unit : 0, r1 = T.lg[i] * unit, a1 = T.ang[i], a0 = j ? T.ang[j] : a1;
    c.moveTo(cx + r0 * Math.cos(a0), cy + r0 * Math.sin(a0));
    for (var k = 1; k <= segs; k++) {
      var t = k / segs, a = a0 + (a1 - a0) * (1 - Math.pow(1 - t, 3)), r = r0 + (r1 - r0) * t;
      c.lineTo(cx + r * Math.cos(a), cy + r * Math.sin(a));
    }
  }

  /* all edges, pre-rendered at the current view; redrawn only when the view or theme changes */
  function bake() {
    needBake = false;
    if (!W) return;
    var big = T.exp >= 16, segs = big ? 12 : 16;
    octx.setTransform(1, 0, 0, 1, 0, 0); octx.clearRect(0, 0, off.width, off.height);
    octx.setTransform(dpr * s, 0, 0, dpr * s, dpr * tx, dpr * ty);
    octx.lineWidth = (big ? 0.5 : 0.7) * Math.pow(s, 0.3) / s;
    octx.globalAlpha = big ? 0.45 : 0.55;
    for (var g = 1; g <= T.maxGen; g++) {
      octx.beginPath();
      for (var i = 1; i < T.n; i++) if (T.gen[i] === g) edgePath(octx, i, segs);
      octx.strokeStyle = col[g - 1]; octx.stroke();
    }
    octx.globalAlpha = 1;
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
    var base = T.exp >= 16 ? 0.8 : T.exp >= 14 ? 1 : 1.15, k = T.exp >= 16 ? 0.45 : 0.62;
    return base + k * Math.sqrt(cnt[i]);
  }

  /* ---------- drawing ---------- */

  function draw(ts) {
    if (!W) return;
    if (needBake) bake();
    var m = upto(L), rho = L * unit, zf = Math.pow(s, 0.5) / s;   /* dots grow gently with zoom */
    var scx = cx * s + tx, scy = cy * s + ty, i, k;

    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, W, W);

    /* doubling rings + labels in the gap */
    var step = T.exp <= 13 ? 3 : 4;
    ctx.lineWidth = 1; ctx.font = '11px ' + font; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    for (k = 2; k <= T.exp; k++) {
      ctx.beginPath(); ctx.arc(scx, scy, k * unit * s, A0, A1);
      ctx.strokeStyle = k % step ? line : line2; ctx.stroke();
      if (k > 3 && k % step === 0) { ctx.fillStyle = muted; ctx.fillText((1 << k).toLocaleString('en-US'), scx, scy - k * unit * s); }
    }

    /* edges, revealed up to the growth front */
    ctx.save(); ctx.beginPath(); ctx.arc(scx, scy, rho * s, 0, TAU); ctx.clip();
    ctx.drawImage(off, 0, 0, W, W);
    ctx.restore();

    ctx.setTransform(dpr * s, 0, 0, dpr * s, dpr * tx, dpr * ty);
    cnt.fill(0);
    for (i = 1; i < m; i++) cnt[T.par[i]]++;
    for (var g = 1; g <= T.maxGen; g++) {
      ctx.beginPath();
      for (i = 1; i < m; i++) if (T.gen[i] === g && !isBig(i)) {
        var r = radius(i) * zf; ctx.moveTo(X[i] + r, Y[i]); ctx.arc(X[i], Y[i], r, 0, TAU);
      }
      ctx.fillStyle = col[g - 1]; ctx.fill();
    }
    if (L < T.exp) {
      ctx.beginPath(); ctx.arc(cx, cy, rho, 0, TAU);
      ctx.strokeStyle = muted; ctx.lineWidth = 1 / s; ctx.stroke();
    }

    /* the line being described */
    if (!playing || ts - shownAt > 130 || shown > m - 1) { shown = m - 1; shownAt = ts; }
    var picked = sel >= 0 && sel < m;
    var f = picked ? sel : m >= T.n ? T.deep : shown;
    if (f > 0) {
      ctx.beginPath();
      for (k = f; k > 0; k = T.par[k]) edgePath(ctx, k, 16);
      ctx.strokeStyle = ink; ctx.lineWidth = 1.7 / s; ctx.lineJoin = 'round'; ctx.stroke();
      for (k = f; k > 0; k = T.par[k]) {
        ctx.beginPath(); ctx.arc(X[k], Y[k], radius(k) * zf + (k === f ? 3 : 1.3) / s, 0, TAU);
        ctx.lineWidth = (k === f ? 1.7 : 1.2) / s; ctx.stroke();
      }
    }

    /* labelled discs for 2, 3, 5, 17 */
    for (i = 0; i < Math.min(m, 8); i++) if (isBig(i)) {
      ctx.beginPath(); ctx.arc(X[i], Y[i], radius(i) * zf, 0, TAU);
      ctx.fillStyle = i ? col[0] : ink; ctx.fill();
    }
    ctx.globalCompositeOperation = 'destination-out'; ctx.fillStyle = '#000';
    for (i = 0; i < Math.min(m, 8); i++) if (isBig(i)) {
      ctx.font = '500 ' + ((i ? 11 : 12) * zf) + 'px ' + font;
      ctx.fillText(String(T.P[i]), X[i], Y[i] + 0.5 * zf);
    }
    ctx.globalCompositeOperation = 'source-over';

    describe(f, picked, m);
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
      if (ui.detail._t !== text) {
        ui.detail._t = text; ui.detail.textContent = '';
        text.split('\n').forEach(function (t) { var d = document.createElement('div'); d.textContent = t; ui.detail.appendChild(d); });
      }
    } else {
      var t0 = 'The root · every prime traces back to 2' + (playing ? '' : '\n' + T.kids[0].length + ' children: ' + T.kids[0].map(function (c) { return T.P[c]; }).join(', '));
      if (ui.detail._t !== t0) {
        ui.detail._t = t0; ui.detail.textContent = '';
        t0.split('\n').forEach(function (t) { var d = document.createElement('div'); d.textContent = t; ui.detail.appendChild(d); });
      }
    }
    put(ui.upto, 'up to ' + fmt(Math.min(T.N, Math.floor(Math.pow(2, L) + 1e-6))));
    put(ui.count, fmt(m) + (m === 1 ? ' prime' : ' primes'));
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
  function play() { if (L >= T.exp) { L = 1; sel = -1; writeHash(); } playing = true; lastTs = 0; setPlayButton(); schedule(); }
  function pause() { playing = false; setPlayButton(); schedule(); }
  function showAll() { playing = false; L = T.exp; ui.grow.value = 1000; setPlayButton(); schedule(); }

  /* ---------- view: pan and zoom ---------- */

  function clampView() {
    if (s <= 1.0001) { s = 1; tx = 0; ty = 0; }
    else {
      tx = Math.min(0, Math.max(W - W * s, tx));
      ty = Math.min(0, Math.max(W - W * s, ty));
    }
    cv.style.touchAction = s > 1 ? 'none' : 'pan-y';
  }
  function zoomAt(px, py, factor) {
    var ns = Math.min(60, Math.max(1, s * factor)), f = ns / s;
    tx = px - (px - tx) * f; ty = py - (py - ty) * f; s = ns;
    clampView(); needBake = true; schedule();
  }
  function resetView() { s = 1; clampView(); needBake = true; schedule(); }

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
      if (moved && s > 1) { tx += p.x - prev.x; ty += p.y - prev.y; clampView(); needBake = true; cv.classList.add('grab'); schedule(); }
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
  cv.addEventListener('dblclick', function (e) { e.preventDefault(); resetView(); });
  ui.zin.addEventListener('click', function () { zoomAt(W / 2, W / 2, 1.6); });
  ui.zout.addEventListener('click', function () { zoomAt(W / 2, W / 2, 1 / 1.6); });
  ui.zreset.addEventListener('click', resetView);

  function pick(p) {
    var m = upto(L), best = -1, bd = 22 * 22;
    for (var i = 0; i < m; i++) {
      var dx = X[i] * s + tx - p.x, dy = Y[i] * s + ty - p.y, d = dx * dx + dy * dy;
      if (d < bd) { bd = d; best = i; }
    }
    sel = best;
    if (playing) pause();
    writeHash(); schedule();
  }

  /* ---------- controls ---------- */

  ui.play.addEventListener('click', function () { if (playing) pause(); else play(); });
  ui.grow.addEventListener('input', function () {
    playing = false; L = 1 + ui.grow.value / 1000 * (T.exp - 1); setPlayButton(); schedule();
  });
  ui.range.addEventListener('change', function () { setRange(+ui.range.value, true); });
  ui.theme.addEventListener('click', function () { applyTheme(theme === 'dark' ? 'light' : 'dark'); store.set('pft-theme', theme); });
  ui.q.addEventListener('input', function () { ui.qerr.textContent = ''; });

  ui.find.addEventListener('submit', function (e) {
    e.preventDefault();
    var raw = ui.q.value.replace(/[\s,]/g, '');
    if (!raw) { ui.qerr.textContent = 'Enter a prime number.'; return; }
    if (!/^\d+$/.test(raw) || +raw < 2) { ui.qerr.textContent = 'Enter a whole number, 2 or larger.'; return; }
    var v = +raw;
    if (v > (1 << MAX_N_EXP)) { ui.qerr.textContent = 'This page goes up to ' + fmt(1 << MAX_N_EXP) + '. Try a smaller prime.'; return; }
    if (!isPrime(v)) {
      var lo = v - 1, hi = v + 1;
      while (lo >= 2 && !isPrime(lo)) lo--;
      while (!isPrime(hi)) hi++;
      ui.qerr.textContent = fmt(v) + ' isn’t prime. Nearest primes: ' + (lo >= 2 ? fmt(lo) + ' and ' : '') + fmt(hi) + '.';
      return;
    }
    ui.qerr.textContent = '';
    focusPrime(v);
  });

  function focusPrime(v) {
    if (v > T.N) {
      var e = RANGES.filter(function (r) { return (1 << r) >= v; })[0];
      setRange(e, false);
    }
    var i = T.idx[v];
    if (i < 0) return;
    sel = i; showAll(); writeHash();
  }

  function setRange(exp, animate) {
    if (!T || T.exp !== exp) {
      T = build(exp);
      cnt = new Uint16Array(T.n);
      ui.range.value = String(exp);
      ui.stats.textContent = fmt(T.n) + ' primes · ' + fmt(T.leaves) + ' with no children · deepest line ' + T.maxGen + ' steps';
      buildLegend();
    }
    sel = -1; s = 1; layout();
    if (animate && !reduceMotion) { L = 1; ui.grow.value = 0; play(); } else showAll();
    writeHash();
  }

  function writeHash() {
    var h = 'n=' + T.exp + (sel >= 0 ? '&p=' + T.P[sel] : '');
    try { window.history.replaceState(null, '', '#' + h); } catch (e) { /* sandboxed */ }
  }

  /* ---------- start ---------- */

  var hp = new URLSearchParams(window.location.hash.replace(/^#/, ''));
  var startExp = RANGES.indexOf(+hp.get('n')) >= 0 ? +hp.get('n') : RANGES.indexOf(+params.get('n')) >= 0 ? +params.get('n') : 13;
  var startP = +(hp.get('p') || params.get('p') || 0);

  T = build(startExp); cnt = new Uint16Array(T.n);
  ui.range.value = String(startExp);
  ui.stats.textContent = fmt(T.n) + ' primes · ' + fmt(T.leaves) + ' with no children · deepest line ' + T.maxGen + ' steps';
  applyTheme(params.get('theme') || store.get('pft-theme') ||
    (window.matchMedia && window.matchMedia('(prefers-color-scheme: light)').matches ? 'light' : 'dark'));

  if (window.ResizeObserver) new ResizeObserver(layout).observe(stage);
  else window.addEventListener('resize', layout);
  layout();
  if (document.fonts && document.fonts.ready) document.fonts.ready.then(function () { font = getComputedStyle(document.body).fontFamily || font; ui.chain._t = ''; schedule(); });

  if (startP && isPrime(startP) && startP <= (1 << MAX_N_EXP)) focusPrime(startP);
  else if (reduceMotion) showAll();
  else play();
})();
