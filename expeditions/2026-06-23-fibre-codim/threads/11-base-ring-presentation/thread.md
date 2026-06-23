# thread 11 — localized base ring presentation (G2-2, formalisation / tide)

**Type:** formalisation (tide) · `OPENED → SPECIFY/DESIGN → CHECKPOINT(no-skip) → PROVE → AUDIT`.
The next rung of the determinantal-presentation build. G2-1 landed the matrix-level Schur relation
(`Core.DeterminantalChart`); this rung lifts the **base** to an explicit *coordinate-ring* presentation
on the pivot chart — the prerequisite for the Schur `AlgEquiv` (G2-3, the wall).

## Read first — the controller's ring-level architecture
`expeditions/2026-06-23-fibre-codim/synthesis.md` § "RING-LEVEL ARCHITECTURE for G2-2..G2-4" — the full
height-composition the chain rests on (catenary `codim_Rep(fibre)=C+codim_{Σ̄^r}(fibre)`; height-additivity
`height P = height(m_E)+0 = δ` on the descended comorphism `R_base→R_total`, going-down only on the chart).
**Part of your job at the checkpoint is to Codex-vet that whole composition** before we commit the chain.

## Goal (a new `Core` module — e.g. `DeterminantalChartRing.lean`)
Present the **localized base coordinate ring** explicitly. The base is `Mat^{rk≤r} ⊆ Mat (Fin p)(Fin q) k`,
coordinate ring `R_base = MvPolynomial (Fin p × Fin q) k ⧸ vanishingIdeal(Mat^{rk≤r})`. On the pivot chart
(localize at `det Δ`, the top-left r×r minor), G2-1's Schur relation `B22 = B21·Δ⁻¹·B12` forces the
bottom-right block, so:

> `R_base` localized at `det Δ`  ≅  `k[Δ entries, B12, B21][ (det Δ)⁻¹ ]`  (free Schur coordinates).

Deliverables (priority order; checkpoint before grinding the hardest):
1. **The determinantal ideal fact:** `vanishingIdeal(Mat^{rk≤r}) = ` the ideal of `(r+1)`-minors (prime;
   the radical/vanishing ideal over alg-closed `k`). **Probe Mathlib first** — `Matrix.det`/minor ideals,
   `RingTheory.MvPolynomial`/determinantal-variety content; this may be partly present or may need building.
2. **The localized presentation:** `R_base,loc[det Δ⁻¹] ≅ₐ` the explicit Schur polynomial localization.
3. **Base facts for G2-4:** `R_base` is a domain (irreducible determinantal variety), `dim R_base = δ`
   (tie to the thermometer `DeterminantalStratumDim`), and `height(m_E) = δ` for `E` a closed point.

## SPECIFY/DESIGN-first — no-skip checkpoint
1. SPECIFY: pin the localized-presentation statement + the determinantal-ideal handle; probe the Mathlib
   determinantal-ideal + `Localization.Away` + `MvPolynomial`-quotient API with `example` blocks.
   **Fire a decorrelated `local-codex-consult`** (authenticated, xhigh) on BOTH (a) the localized base
   presentation and (b) the full ring-level composition in the synthesis architecture (sanity-check it
   before the chain commits); save under `threads/11-base-ring-presentation/codex/`.
2. **CHECKPOINT — report to `main`**: the determinantal-ideal reachability, the localized-presentation
   plan, the Codex verdict on the full composition, and a GO/NO-GO. If the determinantal ideal or the
   localized presentation needs machinery absent at v4.29 (this is a real risk — determinantal ideals are
   deep), STOP and report precisely. A wall here is important signal (it may mean the whole chart route
   needs a different presentation strategy). Do NOT grind / do NOT sorry / do NOT weaken.
3. PROVE → AUDIT.

## Hard rules (lean/CLAUDE.md)
Build via `scripts/lb` (NEVER bare `lake build`/`lake exe cache get`). Zero sorry/axiom/native_decide/#exit.
`↦`; `decide +kernel`; one-line docstrings; name=content. **Core only — never import `DLNFibre.DLN`.** Do
NOT edit the aggregator — report the import line. Confirm Mathlib lemmas exist before building on them.
Don't touch other worktrees or any stash. In-repo memory only.

## AUDIT gate
`scripts/lb` whole-library green; `scripts/sorries` 0; `#print axioms` on headlines = `[propext,
Classical.choice, Quot.sound]`. Witness: the `(2,2,2), r=1` base chart.

## Scope
**Just G2-2** (the localized base ring presentation + the base facts for G2-4 + the composition Codex-vet).
G2-3 (total + Schur AlgEquiv + flatness), G2-4, G2-5, G3/G4 are later. Report to `main`: theorem names +
signatures; green/sorries/axioms; module path + aggregator line; the determinantal-ideal Mathlib status;
the decorrelated-Codex read (incl. the composition sanity-check); v4.29 friction. Commit when green.
