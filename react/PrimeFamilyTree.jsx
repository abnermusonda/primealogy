// Drop-in React page section for a Vite + React site.
// Assumes the app folder is served at /prime-family-tree/ (put it in your project's public/ folder).
export default function PrimeFamilyTree({ theme = 'dark', height = 980 }) {
  return (
    <section aria-label="The prime family tree" style={{ width: '100%' }}>
      <iframe
        title="The prime family tree"
        src={`/prime-family-tree/index.html?embed=1&theme=${theme}`}
        style={{ width: '100%', height, border: 0, display: 'block', background: 'transparent' }}
        loading="lazy"
      />
    </section>
  );
}
