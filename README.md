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

## Privacy and consent

The page sends nothing anywhere. Its only outside request is for two web fonts from Google Fonts, so on the
first visit a dialog asks before loading them; “Continue with system fonts” keeps everything working with the
fonts already on the device. The choice and the color theme are the only things saved in browser storage, and
the “Privacy & data” button under the controls reopens the dialog to change or withdraw the choice. Counting
past 5,000,000 uses most of the CPU, and only starts when a visitor presses Go.

## URL options

| Option | Example | Effect |
| --- | --- | --- |
| `embed=1` | `index.html?embed=1` | Hides the title and notes, for iframes |
| `theme` | `?theme=light` | Forces `dark` or `light` (default follows the visitor's setting) |
| `max` | `#max=100000` | Upper limit, up to 1223334444555554444333221. Limits past the tree show a prompt; counting only starts when a visitor presses Go |
| `n` | `#n=16` | Older form of `max`: the limit as a power of two, from 2 to 20 |
| `p` | `#n=13&p=2879` | Opens with that prime selected; the hash updates as visitors tap. A non-prime such as `#p=100` highlights the closest prime on each side |
| `root` | `#root=2` | Highlights only the primes that hang directly from that prime and dims the rest. `root=2` gives the Fermat primes. Ignored unless it's a prime in the current range. The "Only primes hanging directly from 2" checkbox turns `root=2` on and off |
| `rings` | `#max=8192&rings=value` | Makes the radius of each generation's ring proportional to its largest prime, instead of placing it on the tree's log scale. The "Size generation rings by largest prime" checkbox turns it on and off |
| `gen` | `#max=8192&gen=3,4` | Shows only those generations and hides the rest. The color key does the same: tap colors to add or remove them, or tap All to reset |
| `lines` | `#max=8192&lines=1` | Replaces the edges with one line through every prime in ascending order, 2 → 3 → 5 → 7 → 11 → …, up to the largest prime in the range. Each step is colored by the generation it lands in. The rings and their labels are hidden while it's on. The "Join all the primes in order" checkbox turns it on and off |
| `planes` | `#max=8192&lines=1&planes=1` | With `lines=1`, shades the triangle made by every three primes in a row on the line. A triangle inside one layer (a flat 2D plane) is lightest, one tilted across two layers is deeper, and one spanning three layers is deepest; overlaps add up. The "Fill the planes between steps" checkbox under the line toggle turns it on and off |
| `solid` | `#max=8192&lines=1&planes=1&solid=1` | With `planes=1`, replaces the drawing with one solid: the convex hull of all the primes in range, the tightest closed shape that holds them, drawn opaque and lit, each face in the color of its layer. The "Close it all into one solid" checkbox under the plane toggle turns it on and off |
| `pi` | `#max=8192&pi=1` | Shows the chart of π(x), the exact count of primes, against Li(x) = ∫₂ˣ dt / ln t. Its x axis follows the tree's growth. The "Plot π(x) against Li(x)" checkbox turns it on and off |
| `zeros` | `#max=100&zeros=10` | Adds Riemann's explicit formula to the chart, using the first 1 to 200 zeros of ζ(s). Each zero adds one wave, and together they rebuild the staircase. Implies `pi=1`. The "Add Riemann's waves" checkbox and the slider under it set it |
| `gap` | `#max=50000&zeros=200&gap=1` | Plots π(x) − Li(x) instead, with the bound √x · ln x / 8π that holds from x = 2657 if the Riemann Hypothesis is true. Implies `pi=1`. The "Show the gap" checkbox turns it on and off |
| `psi` | `#max=8192&psi=1&zeros=50` | Swaps π(x) for Chebyshev's ψ(x) = Σ ln p over prime powers ≤ x, whose trend is x itself and whose explicit formula is one √x · cos(γ ln x) wave per zero. Works with `zeros` and `gap` (the RH bound becomes √x · ln²x / 8π). Implies `pi=1`. The "Weigh each prime by ln p" checkbox turns it on and off |
| `zeta` | `#zeta=120` | Shows the zeta plane: a map of ζ(s) across the critical strip up to that height (30 to 390), color for phase and brightness for size, with the zeros ringed on Re s = ½. The "Show the zeta plane" checkbox and its height slider set it. The "Check the zeros" button counts the zeros below that height by the argument principle and compares with the sign changes on the line |
| `fill` | `#max=2000000&fill=0` | `fill=0` removes the shading between each prime's children, which is on by default so the feathers read as solid shapes. The "Fill in the feathers" checkbox turns it on and off |

## Controls

Play or pause the growth, scrub with the slider, tap a dot to trace its line back to 2, search for a
prime (up to 5,000,000), set the upper limit, fill in the feathers, join all the primes in order, size the generation rings by largest prime, plot π(x) against Li(x) and add Riemann's waves from up to 200 zeta zeros, pick which generations to show from the color key, go full screen, drag to rotate the tree on both axes, pinch or scroll to zoom, and shift-drag to pan when zoomed in. Each
generation is its own layer. A double-click or the reset button restores the starting view. Visitors who prefer reduced motion see the finished tree without the animation.

## Notes

- Fonts come from Google Fonts (Playfair Display and Outfit) and load only after consent. If they are blocked, the
  page falls back to system fonts. To self-host them, change the `FONTS` address in `app.js` and drop the dialog.
- Everything is computed in the browser. Building the tree takes milliseconds, even at its 5,000,000 limit.
- The zeta plane evaluates ζ(s) off the line by Euler–Maclaurin summation with at least |Im s| terms and eight
  Bernoulli corrections, good to about 10 places in the strip at the heights shown. The zero check computes N(T) by the
  argument principle, following arg ζ(s) from 2 to 2 + iT to ½ + iT with steps refined until it turns by less than one
  radian, and compares with the sign changes of Z(t) on the line. That is the method behind the numerical verification of
  the Riemann Hypothesis, run here on a small scale.
- The chart's zeta zeros come from the Riemann–Siegel formula, found as sign changes of Z(t). The first ten are
  hard-coded to 9 places, and the rest are good to about 0.001, which is far finer than the chart can show. The
  explicit formula is π(x) = R(x) − Σ R(x^ρ) − 1/ln x + arctan(π/ln x)/π, with each Li(x^ρ) from its
  asymptotic series. With 200 zeros it is within about 0.1 of the true count up to 50,000.
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
