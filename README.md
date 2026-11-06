# The prime family tree

An interactive picture of the primes as one family tree. Every prime p > 2 hangs from the
largest prime factor of p − 1, so every prime traces back to 2. Plain HTML, CSS and
JavaScript: no build step, no libraries, no server code.

## What's in the folder

| File | Purpose |
| --- | --- |
| `index.html` | The page |
| `app.js` | Sieve, tree, radial layout, drawing, controls (about 450 lines) |
| `styles.css` | Dark navy and gold theme, with a light theme |
| `favicon.svg` | Tab icon |
| `react/PrimeFamilyTree.jsx` | Optional React wrapper that embeds the page in an iframe |

## Deploy on a Vite + React site (Azure Static Web Apps)

1. Copy the whole `prime-family-tree` folder into your project's `public/` folder, so you have
   `public/prime-family-tree/index.html`.
2. Build and push as usual. Vite copies `public/` into `dist/` untouched, and the page goes live at
   `https://<your-domain>/prime-family-tree/`.
3. If `staticwebapp.config.json` has a `navigationFallback` that rewrites to `/index.html`, add the folder
   to its `exclude` list so Azure serves the files directly:

   ```json
   "navigationFallback": {
     "rewrite": "/index.html",
     "exclude": ["/prime-family-tree/*", "/assets/*"]
   }
   ```

4. Link to it from your navigation or a blog post. You can also embed it inside a React page with
   `react/PrimeFamilyTree.jsx`: copy it into `src/components/` and render `<PrimeFamilyTree />`.

## Deploy anywhere else

Upload the folder to any static host (Azure Storage static website, GitHub Pages, Netlify, S3) and open
`index.html`. To try it locally, run `python3 -m http.server` inside the folder and visit
`http://localhost:8000`.

## URL options

| Option | Example | Effect |
| --- | --- | --- |
| `embed=1` | `index.html?embed=1` | Hides the title and notes, for iframes |
| `theme` | `?theme=light` | Forces `dark` or `light` (default follows the visitor's setting) |
| `n` | `#n=16` | Range as a power of two: 10, 12, 13, 14 or 16 |
| `p` | `#n=13&p=2879` | Opens with that prime selected; the hash updates as visitors tap |

## Controls

Play or pause the growth, scrub with the slider, tap a dot to trace its line back to 2, search for a
prime (up to 65,536), switch the range, drag to pan, and pinch or scroll to zoom. A double-click resets
the view. Visitors who prefer reduced motion see the finished tree without the animation.

## Notes

- Fonts come from Google Fonts (Playfair Display and Outfit). If they are blocked, the page falls back to
  system fonts. To self-host them, replace the two `fonts.googleapis.com` links in `index.html`.
- Everything is computed in the browser on load. Building the tree takes a few milliseconds, even for
  65,536.
- Tested in Chrome at desktop and phone sizes, in both themes.
