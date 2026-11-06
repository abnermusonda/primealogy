#!/usr/bin/env node
/*
 * Builds primes-reference.json: exact prime counts and the largest prime at fixed points,
 * so the page can start counting from a checkpoint rather than from 2.
 *
 *   curl -o b006880.txt https://oeis.org/A006880/b006880.txt
 *   node tools/build-prime-reference.mjs b006880.txt primes-reference.json
 *
 * Up to 10^12 every entry comes from the sieve here, and the run aborts if a power of ten
 * disagrees with OEIS A006880. Past that, counts are taken from A006880 unverified. The
 * largest primes are checked with Miller-Rabin on the first 13 primes, which is proven
 * correct below 3.3e24, so the table stops at 10^24.
 */
import { readFileSync, writeFileSync } from 'node:fs';
import { availableParallelism } from 'node:os';
import { Worker, isMainThread, parentPort, workerData } from 'node:worker_threads';

const BLOCK = 1e8, STEP = 1e10, MAX = 1e12, SEGMENT = 1 << 22, TOP_POWER = 24;

function sieveBlock(lo, hi, base, seg) {
  let count = 0, last = 0;
  for (let a = lo; a < hi; a = Math.min(a + SEGMENT, hi)) {
    const b = Math.min(a + SEGMENT, hi);
    const first = a % 2 ? a : a + 1;
    const size = Math.ceil((b - first) / 2);
    seg.fill(0, 0, size);
    for (let i = 0; i < base.length; i++) {
      const p = base[i];
      let m = p * p;
      if (m >= b) break;
      if (m < first) { const r = first % p; m = r ? first + p - r : first; }
      if (m % 2 === 0) m += p;
      for (let j = (m - first) / 2; j < size; j += p) seg[j] = 1;
    }
    for (let k = 0; k < size; k++) if (seg[k] === 0) { count++; last = first + 2 * k; }
  }
  return { count, last };
}

if (!isMainThread) {
  const seg = new Uint8Array(SEGMENT / 2 + 1);
  parentPort.on('message', ({ k, lo, hi }) => {
    parentPort.postMessage({ k, ...sieveBlock(lo, hi, workerData.base, seg) });
  });
} else {
  const [oeisPath, outPath] = process.argv.slice(2);
  if (!oeisPath || !outPath) { console.error('usage: build-prime-reference.mjs <b006880.txt> <output.json>'); process.exit(2); }

  const published = new Map();
  for (const line of readFileSync(oeisPath, 'utf8').split('\n')) {
    const m = /^(\d+) (\d+)$/.exec(line.trim());
    if (m) published.set(+m[1], m[2]);
  }

  function isPrime(n) {
    const bases = [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n, 41n];
    for (const p of bases) if (n % p === 0n) return n === p;
    let d = n - 1n, r = 0;
    while (d % 2n === 0n) { d /= 2n; r++; }
    const powMod = (b, e, m) => { let x = 1n; b %= m; for (; e; e >>= 1n) { if (e & 1n) x = x * b % m; b = b * b % m; } return x; };
    next: for (const a of bases) {
      let x = powMod(a, d, n);
      if (x === 1n || x === n - 1n) continue;
      for (let i = 1; i < r; i++) { x = x * x % n; if (x === n - 1n) continue next; }
      return false;
    }
    return true;
  }
  const largestBelow = (x) => { let p = x; while (!isPrime(p)) p--; return p; };

  const limit = Math.ceil(Math.sqrt(MAX)) + 1;
  const comp = new Uint8Array(limit + 1), odd = [];
  for (let i = 3; i <= limit; i += 2) {
    if (comp[i]) continue;
    odd.push(i);
    for (let j = i * i; j <= limit; j += 2 * i) comp[j] = 1;
  }
  const base = Uint32Array.from(odd);

  const blocks = MAX / BLOCK, threads = Math.max(1, availableParallelism() - 1), t0 = Date.now();
  const results = new Map(), entries = [];
  let next = 0, ordered = 0, count = 1, last = 2;

  await new Promise((resolve, reject) => {
    const workers = [];
    const send = (w) => {
      if (next >= blocks) return;
      const k = next++;
      w.postMessage({ k, lo: k === 0 ? 3 : k * BLOCK, hi: (k + 1) * BLOCK });
    };
    for (let i = 0; i < threads; i++) {
      const w = new Worker(new URL(import.meta.url), { workerData: { base } });
      w.on('error', reject);
      w.on('message', (m) => {
        results.set(m.k, m);
        while (results.has(ordered)) {
          const d = results.get(ordered);
          results.delete(ordered);
          count += d.count;
          if (d.last) last = d.last;
          ordered++;
          const x = ordered * BLOCK;
          if (x % STEP === 0) {
            entries.push({ x: String(x), pi: String(count), largest: String(last), source: 'sieve' });
            console.log(`${x} pi=${count} ${((Date.now() - t0) / 1000).toFixed(0)}s`);
          }
        }
        if (ordered === blocks) { workers.forEach((t) => t.terminate()); resolve(); } else send(w);
      });
      workers.push(w);
    }
    workers.forEach(send);
  });

  for (const e of entries) {
    if (!isPrime(BigInt(e.largest))) throw new Error('not prime: ' + e.largest);
    const power = Math.log10(+e.x);
    if (Number.isInteger(power) && published.get(power) !== e.pi) {
      throw new Error(`pi(10^${power}): sieve ${e.pi}, OEIS ${published.get(power)}`);
    }
  }
  for (let k = 13; k <= TOP_POWER; k++) {
    const x = 10n ** BigInt(k);
    entries.push({ x: String(x), pi: published.get(k), largest: String(largestBelow(x)), source: 'OEIS A006880' });
  }

  const body = entries.map((e) => '  ' + JSON.stringify(e)).join(',\n');
  writeFileSync(outPath, `[\n${body}\n]\n`);
  console.log(`${entries.length} entries, ${threads} threads, ${((Date.now() - t0) / 1000).toFixed(0)}s`);
  process.exit(0);
}
