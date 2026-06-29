# Route (b) BUILD-LEVEL SPEC — the fused-frame layer-filtration block-tri det (∀M, for the gate)

Branch genm-interior @0d647c54. F1 is DEAD (genm-mapeq's gate: the chain accumulator C(k+1) couples
boundaries k..L, so composeFold-of-disjoint-factors can't reproduce the cross-boundary mixed partials;
the composeFold-of-conjBlockFactors API was a speculative bet, used nowhere). REVERT to Route (b) — the
fused-frame det_comp route (my 2b grading), generalizing the (3,3,3,3) precedent. DECORRELATED Codex
(xhigh) VALIDATES (b) sound over opaque widths, with two sharp verify-conditions (below).

## WHY (b) IS SOUND WHERE F1 WASN'T (the crux)
The chain coupling C(k+1) = Bmat(k+1)·chainQ + u·Rmat(k+1) feeds A_k = chainA(N_k,W_k,C(k+1)). In the
FUSED Frame's fderiv DFrame, this coupling is GENUINELY PRESENT (not faked by disjoint factors) but lives
in the OFF-DIAGONAL (upper) blocks of a LAYER-graded block-triangular matrix — and BlockTriangular.det
discards off-diagonal blocks (det = ∏ diagonal-block dets). F1 died trying to REPRESENT the chart as
disjoint factors; (b) keeps the full fused matrix and exploits that the coupling is DET-IRRELEVANT.

## CODEX-VALIDATED SOUNDNESS (xhigh, route-b-soundness-answer.md) + the 2 VERIFY-CONDITIONS
- KILL-TEST PASSES: A_k reads only layers ≥ k+1 (C(k+1) reads later boundaries) ⟹ ∂A_k/∂x_j = 0 for
  j < k ⟹ ONE-SIDED (upper) block-triangular, coupling off-diagonal. NOT two-sided. SOUND.
- VERIFY-1 (the cheapest discriminating check, DO FIRST): the dependency lemma
  `layer(input col) < layer(output row) → DFrame entry = 0` (the off-block-vanishing). If a diagonal
  block (input layer = output layer = k) still contains later-layer variables in det-relevant positions,
  STOP — (b) fails. [Codex: this is the kill-condition.]
- VERIFY-2: the diagonal block for layer k = the FROZEN-accumulator local layer assembly (C(k+1) treated
  as constant) = the local Schur/K frame (det = |det K_k|^{r+c}) + the radial. CRITICAL: the K-coupling
  must be LOCAL to a single boundary (the K_k variables all at layer k); if K_k splits across boundaries
  the per-layer product breaks. [Verify K_k is single-layer.]

## THE LEAN ROUTE (Codex-ranked (a) > the per-layer-insertion route — the latter risks re-smuggling F1)
(a) [CHOSEN]: ONE global layer grading `bLayer : Fin N → ℕ` (the chain layer/boundary a coord belongs to)
    + `Matrix.BlockTriangular.det` (Mathlib, any LinearOrder grading) + a GENERAL `Fin (blockSize) ≃
    {i // bLayer i = k}` builder (the cast-avoiding piece — via Finset.card_equiv / the pivotBlowupOnDeriv_det
    `Equiv.swap`+`Finset.card_equiv` pattern, NOT literal index lists). This keeps the FULL fused matrix
    (so the off-diagonal coupling is genuinely there + proven off-block) — does NOT resurrect F1's disjointness.
    AVOID the per-layer-insertion-CLM route (Codex: dangerous, re-smuggles the false disjoint-factors claim
    unless each insertion provably depends on later params).

## BANKED MACHINERY (the (b) build consumes)
- `Matrix.BlockTriangular.det` (Mathlib): det = ∏_{a∈image b} det(toSquareBlock b a), given off-block-vanish.
- `pivotBlowupOnDeriv_det` (S1G5Charts): the OPAQUE-width precedent — `active : Finset (Fin N)` grading +
  Equiv.swap + Finset.card_equiv for the diagonal product, NO literal equivs. THE pattern to transfer.
- `listProd_clm_abs_det` / `general_composed_clm_abs_det` (RouteMAchieverGeneralDet): the det_comp telescope
  for the OUTER `Q ∘ Frame ∘ Kparam` chain (Q det 1, Kparam det monomial, Frame det block-tri) — full-ambient,
  NO casts. (Used for the det_comp chain, NOT for an internal disjoint-factor fold.)
- `lduCoreDeriv_det` / `schurFrame_abs_det` (RouteMSchurFrameDet): the per-layer diagonal-block dets.
- (3,3,3,3) `Frame3333Deriv_det` / `Frame3333Deriv_blockTri` / `frameB` (RouteM3333Atom): the LITERAL
  precedent to generalize (SCC grading frameB → the LAYER grading bLayer; literal e_k equivs → the general
  Finset.card_equiv builder). (2,2,2) `phi222_abs_det` (RouteM222Det): the 2-boundary fused precedent.

## SUB-PIECES (the Route-b tide, in order — VERIFY-1 FIRST per Codex)
- b-0 (VERIFY-1, the cheapest kill-check, DO FIRST): define `bLayer : Fin (routeMAmbient M) → ℕ` (the
  layer grading, via chartIdxEquiv's boundary index — the role-slot's boundary k) + prove the off-block-
  vanishing `bLayer j < bLayer i → DFrame_M entry (i,j) = 0` (the ∂A_k/∂x_j = 0 for j<k dependency).
  If this FAILS (a diagonal block leaks later-layer vars det-relevantly), STOP + report.
- b-1: the general `Fin (blockSize_k) ≃ {i // bLayer i = k}` builder (Finset.card_equiv / Equiv.swap
  pattern, opaque-width — the cast surface). The toSquareBlock reindex.
- b-2: the per-layer diagonal-block det = |det K_k|^{r+c} · (radial/LDU contribution), via schurFrame_abs_det
  + lduCoreDeriv_det (VERIFY-2: K_k single-layer).
- b-3: assemble |det DFrame_M| = ∏_k (diagonal det) via Matrix.BlockTriangular.det; then |det Dphi| =
  1 · (∏ diag) · (Kparam monomial) via the det_comp telescope (listProd_clm_abs_det); = ∏|u_j|^{leafH j}.
  Feeds interiorDet_of_factored-style (or a new det_comp consumer) → the cov field.

## RISK / GATE
SOUND (Codex xhigh-validated, the 2 verify-conditions sharp). The cost center = b-0 (the off-block-
vanishing of the fused frame over opaque Fin (Wext k)) + b-1 (the opaque-width toSquareBlock reindex).
b-0 is the kill-check — DO IT FIRST (if a diagonal block leaks later-layer vars, (b) fails; report + re-route).
This is a genuine multi-tide build (the long pole, now SOUND vs F1's dead disjointness). Recommend genm-mapeq
(primed as the (b) builder) opens b-0 first as the kill-check, then b-1→b-3. Gate this build-level spec.
