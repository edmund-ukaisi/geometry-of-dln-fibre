# priorities.md — the taste ledger (core-quiver-engine)

The ranked decision queue. The controller proposes; **the operator edits this file directly**. Nothing
unranked; "unclear-but-keep-going" is first-class.

## Done + reviewed (bedrock)
- ✅ **Mathlib recon** (thread 01).
- ✅ **Ambient objects** (thread 02, rung 1) — `DLNFibre.Core.Setup`; reviewed.
- ✅ **Prop 3.1a inversion** (thread 03, rungs 2–3) — `DLNFibre.Core.RankPattern`; reviewed.
- ✅ **Decorrelated audit** (thread 04) — both SURVIVED; two precision fixes applied + re-gated.

The expedition's stated **bedrock target (rungs 1–3) is met**.

## The decision now — rung 4 (operator-facing strategic fork)

Rung 4 (orbits ↔ Kostant via type-A **Gabriel**) is **build-from-scratch** (recon: the largest new
infrastructure — interval modules `M_{ij}`, the equioriented chain, Krull–Schmidt-style decomposition,
Kostant data) and is **not single-tide whole-in-reach** — it is a sub-build, to be roadmapped, not nibbled.

**The fork (controller recommendation, operator to decide):**
- **(A) Full build** the type-A Gabriel / interval-module decomposition in Lean. This *is* the reusable
  asset absent from Mathlib (maximal value for the "good reusable library" goal), but the largest chunk
  (multi-tide; likely its own expedition).
- **(B) Cite-and-corollary:** state the type-A Gabriel decomposition with a cited reference (Thm 2.5),
  prove the orbit ↔ Kostant corollary (Cor 2.9) + downstream on top. Unblocks the codimension layer fast;
  the heavy classification is Cited, named as such.
- **Controller lean:** (A) for the engine's reusability, but staged — define interval modules + the
  type-A representation + the *existence* of a decomposition first, leaving the indecomposables-are-intervals
  classification as the sharp sub-target (cite initially if it resists). Surfaced for the operator's call.

## Reachable-now (smaller, not the bundle)
1. **`submult` / `rankPattern`** (thread 06) — the matrix-side objects deferred from thread 03 (shifted-tail
   or `List.prod` route for the variable-lower-bound cast). Unblocks Prop 3.1b; bedrock-sized, no Gabriel.
   A good next *formalisation* tide independent of the rung-4 fork.
2. Cosmetic: clear the `abel_nf` info at `RankPattern.lean:128`.

## Parked (next expedition)
- **`Ext` codimension (Cor 3.5)** — reuse Mathlib `Ext` once reps embed in a module category. Depends on
  rung 4. (unclear-but-keep-going.)
- QIP (Thm 6.1) + explicit lattice-point formula (Thm 7.10) — Bundle 1 combinatorics, reachable once the
  rank-pattern objects (thread 06) are in.

## Notes
- Read `../../lean/CLAUDE.md` before any Lean (Core never imports DLN). In-repo memory only.
- Reader-facing paper digestion is the operator's activity — not a thread here.
