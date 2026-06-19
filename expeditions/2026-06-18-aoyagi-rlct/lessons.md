# lessons.md - aoyagi-rlct

Append-only methodological learnings. Mathematical results belong in
`synthesis.md`, `claims.md`, `theorem-ledger.md`, or thread files.

- 2026-06-18 - Start with root ledgers before scratch artifacts. A prior
  expedition left useful scratch in the main checkout without the root
  `brief/priorities/synthesis/threads` scaffold, which weakens compaction
  recovery. For Aoyagi, keep the root state current from the first tick.
- 2026-06-18 - Source-to-Lean drift is the main controller risk. Aoyagi's proof
  is long, PDF-only in this repo, and notation-heavy; maintain both `claims.md`
  and `theorem-ledger.md`.
- 2026-06-18 - For long formalisation threads, verify worktree isolation and
  teammate idleness before spawning successors. This carries over from the
  core-quiver expedition lessons.
- 2026-06-18 - In Aoyagi, never compress actual layer widths into prefix minima
  without checking the source formula. The blow-up transition uses both notions,
  and conflating them changes exponent counts.
- 2026-06-19 - For Aoyagi's blow-up section, page images are necessary when a
  decision depends on `M^{(s)}` versus `M(S)`: plaintext extraction collapses
  the notations too often. Record the source-imaged formula before accepting a
  repaired transition invariant.
