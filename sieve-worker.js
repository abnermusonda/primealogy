/*
 * Segmented sieve of Eratosthenes for one block of numbers. app.js hands each worker
 * { lo, hi } plus the odd base primes up to sqrt(hi); it replies with how many primes
 * are in [lo, hi) and the largest one. Primes aren't kept, so memory stays flat.
 */
'use strict';

var base = new Uint32Array(0);
var seg = new Uint8Array(0);

self.onmessage = function (e) {
  var d = e.data, lo = d.lo, hi = d.hi;
  if (d.base) base = d.base;

  /* only odd numbers are stored: seg[j] stands for first + 2j */
  var first = lo % 2 ? lo : lo + 1;
  var size = Math.ceil((hi - first) / 2);
  if (seg.length < size) seg = new Uint8Array(size); else seg.fill(0, 0, size);

  for (var i = 0; i < base.length; i++) {
    var p = base[i], m = p * p;
    if (m >= hi) break;
    if (m < first) { var r = first % p; m = r ? first + p - r : first; }
    if (m % 2 === 0) m += p;
    for (var j = (m - first) / 2; j < size; j += p) seg[j] = 1;
  }

  var count = 0, top = -1;
  for (var k = 0; k < size; k++) if (seg[k] === 0) { count++; top = k; }
  self.postMessage({ lo: lo, hi: hi, count: count, last: top < 0 ? 0 : first + 2 * top });
};
