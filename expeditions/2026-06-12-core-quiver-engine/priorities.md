# priorities.md — the taste ledger (core-quiver-engine)

The ranked decision queue. The controller proposes; **the operator edits this file directly**. Nothing
unranked; "unclear-but-keep-going" is first-class.

## Done (tick 1)
- ✅ **Mathlib recon** (thread 01) — rungs 1–3 = basic Mathlib; rung 4 = build-from-scratch. (was #1)
- ✅ **Ambient objects** (thread 02, rung 1) — landed green + axiom-clean; encoding (i) endorsed. (was #2)

## Ranked (controller's proposal — operator to edit)

1. **[in flight] Prop 3.1a — the inclusion-exclusion bijection (thread 03, rungs 2–3).** Introduce
   `submult`/`r_{ij}`/`m_{ij}` and prove the abstract array inversion as a characterisation. The first
   real *theorem* of the engine. → `formaliser`.
2. **[gate] Decorrelated fidelity audit of the Core slice (thread 04).** Once 03 lands, one reviewer pass
   over `Setup.lean` (definitions match the paper's `Rep_d`/`mult`/`Σ^r`/fibre) **and** Prop 3.1 (the Lean
   statement is the paper's identity, stated as the abstract inversion — not over-claiming the tuple/Gabriel
   direction). Base audited hardest. → `reviewer` (+ `local-codex-consult`).
3. **[next sub-build, gated] Rung 4 — orbits ↔ Kostant via type-A Gabriel (thread 05).** Build-from-scratch:
   interval modules `M_{ij}`, the equioriented chain, the decomposition. Decide full-build vs cite-and-
   corollary when opened. Whole-in-reach check first; do **not** nibble. → its own thread.
4. **[parked, next expedition] `Ext` codimension (Cor 3.5).** Reuse Mathlib `Ext` once reps are in a module
   category. Out of scope for this expedition; named successor. (unclear-but-keep-going: depends on rung 4.)

## Notes
- Read `../../lean/CLAUDE.md` before any Lean (Core never imports DLN).
- Statement-card every landed result (Proved/Assumed/Cited/Deferred); pin the commit SHA at integration.
- In-repo memory only; never `~/.claude`.
- Reader-facing paper digestion is the operator's activity — not a thread here.
