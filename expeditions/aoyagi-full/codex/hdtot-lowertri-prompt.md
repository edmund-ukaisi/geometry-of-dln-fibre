<task>
Lean 4 / Mathlib v4.29. DECISION before building: is the route-C `lowerTri` assembly for the
`hDtot` determinant TYPE-CORRECT and REACHABLE, or does it re-import a wall via an `eIn ≠ eOut`
rectangular correction?

CONTEXT (all banked, sorry-free):
- `BparamsLeaf ha y : Params M` (L=2), `Params M = ∀ s:Fin 2, Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) ℝ`.
  So `fderiv BparamsLeaf y₀ : (Fin (flatDim M)→ℝ) →L (Params M)` ... actually `Params M` IS the codomain;
  flattened via the linear `paramsEquivFlatCLE : Params M ≃L (Fin (flatDim M)→ℝ)`.
- `Dtot ha y₀ = (paramsEquivFlatCLE ∘L fderiv BparamsLeaf y₀).toLinearMap`, an ENDO of `Fin (flatDim M)→ℝ`.
  Goal: `|det Dtot| = |det K|^{r+c}` (the free-K Schur value; the leaf layer contributes det 1).
- GATE LANDED (RouteMProjV0Gate): the LAYER-0 OUTPUT block of `fderiv BparamsLeaf` — restricted to the
  V0={K,X,N,E} INPUT slots — has fderiv core = `schurFrameDeriv (readX)(readK)(readN)`, det `|det K|^{r+c}`.
  This was done ONE-SIDED (`slotReadV0 : (Fin N→ℝ) →ₗ SchurInc`, NOT a full ambient partition equiv).
- PROVEN OBSTRUCTION (RouteMGradingObstruction): the INPUT grading (chartIdx boundary counts: `(6,2)` at
  (2,2,2)) and the OUTPUT grading (flatIdx layer counts: `M_s·M_{s+1} = (4,4)`) DIFFER as partitions
  (same total 8). So `Dtot` (endo of `Fin 8 → ℝ`) is NOT `Matrix.BlockTriangular` under any SINGLE grading;
  the input boundary-`s` slots and the output layer-`s` slots are different subspaces of `Fin 8 → ℝ`.
- NUMERIC CERT (6 seeds, (3,3,4)): reconstructing `fderiv BparamsLeaf` by hand, under input role-split
  eIn={K,X,N,E}⊕{W,leaf} and output eOut=C1⊕Agen1: `‖J01‖=0` exactly (layer-0 output indep of W,leaf),
  `det J00 = |det K|^4`, `|det J11|=1`, N-block the strictly-lower J10 coupling. So the MATH is block-lower-tri.

THE BANKED `lowerTri` KEYSTONE (RouteMSchurFrameDet):
- `lowerTri (f:M'→M')(g:N'→N')(h:M'→N') : M'×N' →ₗ M'×N'`, `(m,n)↦(f m, g n + h m)`.
- `lowerTri_det : det (lowerTri f g h) = det f · det g` (coupling h det-invisible).
- To use it on `Dtot`, I need `eIn eOut : (Fin 8→ℝ) ≃ₗ M'×N'` with `eOut ∘ Dtot ∘ eIn.symm = lowerTri f g h`,
  then `det Dtot = det(eOut)⁻¹ · det(lowerTri) · det(eIn)` … i.e. only `det Dtot = det(lowerTri)` if eIn=eOut.

THE CRUX: the input/output gradings DIFFER (proven obstruction). The numeric cert's eIn (input role-split)
and eOut (output layer-split) are DIFFERENT collections of the 8 coords. So `lowerTri` would be conjugation
by eIn one side, eOut the other — `det (eOut ∘ Dtot ∘ eIn.symm) = det(eOut)·det(Dtot)·det(eIn.symm)`, and
`|det Dtot| = |det(lowerTri)|` ONLY IF `|det(eOut)·det(eIn.symm)| = 1`. The scoping doc called this "the
analogue of hreg" — UNRESOLVED. If eIn, eOut are PERMUTATION-like reindexes (each a composition of
`finSumFinEquiv`/`finCongr`/`chartIdxEquiv`/`paramsEquivFlat` — all measure-preserving / det ±1), then
`|det eIn| = |det eOut| = 1` and the correction vanishes. Is that the case here?
</task>

<output_contract>
1. VERDICT (one line): is route-C `lowerTri` reachable for `|det Dtot| = |det K|^{r+c}` WITHOUT a new wall,
   or does the eIn≠eOut correction (`|det eOut · det eIn⁻¹| = 1`) itself need a substantive proof?
2. The cleanest concrete decomposition: WHAT are M', N', f, g, h, eIn, eOut for Dtot at L=2? Be specific about
   whether eIn = eOut is achievable (a SINGLE split usable both sides) or genuinely eIn≠eOut is forced by the
   grading obstruction.
3. If eIn≠eOut is forced: is `|det eIn| = |det eOut| = 1` automatic (both are reindex/permutation CLEs built
   from finSumFinEquiv/finCongr/chartIdxEquiv/paramsEquivFlat — measure-preserving), so the correction is a
   one-liner, OR is there a genuine non-permutation shear hidden in eOut that carries a nontrivial det?
4. The cheapest ≤5-step ordering to either CLOSE hDtot or hit the precise wall. Name the single riskiest goal.
5. Where a green-but-WRONG proof hides (the det-correction trap, or g≠det-1, or the J10 reindex).
Flag inference vs. fact. Be decisive on whether to BUILD route-C or surface a wall.
</output_contract>

<grounding_rules>
Only the description above (no repo access). State given-vs-inferred. Don't invent Mathlib lemma names
(mark "verify-exists"). The decision (build vs wall) is what I'm buying — be decisive and give the reason,
especially on the eIn≠eOut det-correction.
</grounding_rules>
