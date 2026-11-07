# Primealogy: The prime family tree

An interactive picture of the primes as one family tree. Every prime p > 2 hangs from the
largest prime factor of p − 1, so every prime traces back to 2. Plain HTML, CSS and
JavaScript: no build step, no libraries, no server code.

## What's in the folder

| File | Purpose |
| --- | --- |
| `index.html` | The page |
| `app.js` | Sieve, tree, radial layout, drawing, controls |
| `sieve-worker.js` | Web worker that counts primes in one block, for limits past the tree |
| `primes-reference.json` | Exact prime counts and the largest prime at fixed points, so counting needn't start at 2 |
| `tools/build-prime-reference.mjs` | Regenerates that table; not needed on the site |
| `styles.css` | Dark navy and gold theme, with a light theme |
| `favicon.svg` | Tab icon |
| `react/Primealogy.jsx` | Optional React wrapper that embeds the page in an iframe |

## Deploy on a Vite + React site (Azure Static Web Apps)

1. Copy the whole `primealogy` folder into your project's `public/` folder, so you have
   `public/primealogy/index.html`.
2. Build and push as usual. Vite copies `public/` into `dist/` untouched, and the page goes live at
   `https://<your-domain>/primealogy/`.
3. If `staticwebapp.config.json` has a `navigationFallback` that rewrites to `/index.html`, add the folder
   to its `exclude` list so Azure serves the files directly:

   ```json
   "navigationFallback": {
     "rewrite": "/index.html",
     "exclude": ["/primealogy/*", "/assets/*"]
   }
   ```

4. Link to it from your navigation or a blog post. You can also embed it inside a React page with
   `react/Primealogy.jsx`: copy it into `src/components/` and render `<Primealogy />`.

## Deploy anywhere else

Upload the folder to any static host (Azure Storage static website, GitHub Pages, Netlify, S3) and open
`index.html`. To try it locally, run `python3 -m http.server` inside the folder and visit
`http://localhost:8000`.

## URL options

| Option | Example | Effect |
| --- | --- | --- |
| `embed=1` | `index.html?embed=1` | Hides the title and notes, for iframes |
| `theme` | `?theme=light` | Forces `dark` or `light` (default follows the visitor's setting) |
| `max` | `#max=100000` | Upper limit, up to 1223334444555554444333221. Limits past the tree show a prompt; counting only starts when a visitor presses Go |
| `n` | `#n=16` | Older form of `max`: the limit as a power of two, from 2 to 20 |
| `p` | `#n=13&p=2879` | Opens with that prime selected; the hash updates as visitors tap. A non-prime such as `#p=100` highlights the closest prime on each side |
| `root` | `#root=2` | Highlights only the primes that hang directly from that prime and dims the rest. `root=2` gives the Fermat primes. Ignored unless it's a prime in the current range. The "Only primes hanging directly from 2" checkbox turns `root=2` on and off |
| `gen` | `#max=8192&gen=3,4` | Shows only those generations and hides the rest. The color key does the same: tap colors to add or remove them, or tap All to reset |
| `fill` | `#max=2000000&fill=0` | `fill=0` removes the shading between each prime's children, which is on by default so the feathers read as solid shapes. The "Fill in the feathers" checkbox turns it on and off |

## Controls

Play or pause the growth, scrub with the slider, tap a dot to trace its line back to 2, search for a
prime (up to 5,000,000), set the upper limit, fill in the feathers, pick which generations to show from the color key, go full screen, drag to rotate the tree on both axes, pinch or scroll to zoom, and shift-drag to pan when zoomed in. Each
generation is its own layer. A double-click or the reset button restores the starting view. Visitors who prefer reduced motion see the finished tree without the animation.

## Notes

- Fonts come from Google Fonts (Playfair Display and Outfit). If they are blocked, the page falls back to
  system fonts. To self-host them, replace the two `fonts.googleapis.com` links in `index.html`.
- Everything is computed in the browser. Building the tree takes milliseconds, even at its 5,000,000 limit.
- The tree is drawn up to 5,000,000. Past that, web workers run a segmented sieve upward, keeping an exact
  count and the largest prime rather than a list, so memory stays flat. It uses every CPU core but one,
  and needs the page served over http rather than opened as a file.
- Counting covers about 10¹⁰ numbers a second on an 18-core M5 Pro, but the top limit would still take
  millions of years, so very large limits run until a visitor stops them. The sieve stops at 2⁵³ in any case.

## Prime reference

`primes-reference.json` holds 112 checkpoints. Each one gives a position `x`, the exact count of primes up to
it (`pi`), the largest prime at or below it (`largest`) and its `source`. A count starts from the nearest
checkpoint below the limit, so a limit on a checkpoint needs no sieving, and any limit up to 10¹² is within
about a second of one. If the file can't be read, counting starts at 2 and gets the same answer more slowly.

| Range | Spacing | Counts come from |
| --- | --- | --- |
| 10¹⁰ to 10¹² | Every 10¹⁰ | This repo's sieve, which must match OEIS A006880 at each power of ten |
| 10¹³ to 10²⁴ | Each power of ten | [OEIS A006880](https://oeis.org/A006880), not checked here |

Counts for limits past 10¹² inherit that published starting value. Past 2⁵³ the page can only show the
published count, because the sieve can't start there. Every `largest` value is proven prime by Miller-Rabin
with the first 13 prime bases, which is exact below 3.3 × 10²⁴.

To rebuild it, which takes a few minutes on all cores but one:

```bash
curl -o b006880.txt https://oeis.org/A006880/b006880.txt
node tools/build-prime-reference.mjs b006880.txt primes-reference.json
```
- Tested in Chrome at desktop and phone sizes, in both themes.

## Next steps

The one hard step is factoring p − 1 to find a prime's parent. That fits
[qubolts](https://github.com/abnermusonda/qubolts), so the plan is an honest quantum demo rather than a
speedup:

1. **Big-number lookup.** Extend "Find a prime" with BigInt, primality testing and Pollard rho in a web
   worker, so it can show the line of descent, factorisations and closest primes for numbers far past
   65,536. Listing every prime at that scale isn't possible, so these numbers get a path, not a tree.
2. **A `factoring` qubolt.** Encode p × q = N as a QUBO. Use a compact encoding, because the plain
   multiplication circuit needs 176 variables at 16 bits and `leap_qpu` caps at 150. Factoring is outside
   the qubolts adtech and martech scope, so it may belong in `examples/`.
3. **A small API.** The page is static and a D-Wave token can't go in browser code, so add an Azure
   Function that wraps `qubolts.solve()`. Rate-limit it, because each QPU call costs money.
4. **A "Factor on QPU" button.** Show the classical answer instantly, then the quantum attempt beside it
   with its time and variable count. The browser checks the result by multiplying. Every p − 1 in the tree
   is at most 16 bits, which is within reach of today's annealers.

**For the resolver:** use a trivial `baseline()` and report the Pollard rho comparison separately, or
`solve()` can never show the QPU adding anything. Cast sample values to `int` before decoding, because
numpy `int8` values overflow when shifted.

**What to expect:** a prototype on the local `sa` backend (5 numbers per size, 500 reads, 2,000 sweeps)
factored 5/5 at 12 bits, 4/5 at 16, 1/5 at 20 and none from 24 to 36, against microseconds for Pollard
rho. That's simulated annealing, not a QPU run, so real hardware results are still unknown. The
[record for a quantum annealer](https://www.nature.com/articles/s41598-024-53708-7.pdf) is 23 bits.
Shor's algorithm is the real speedup, but it needs gate-model hardware and isn't a QUBO problem.
