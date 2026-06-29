# Is `hdet` banked-reducible via composeFold, or a fused-frame long-pole? (Lean 4 / Mathlib v4.29)

## The disagreement to adjudicate

For the deep-linear-network interior-det headline, route #1 is `φ = B ∘ pivotBlowupOn(active,p)` (radial
arrow factored out), then `|det Dφ| = |u_p|^{minAdm−1}·|det DB|` (one `LinearMap.det_comp`, BANKED as
`radialComp_abs_det`). The boundary factor `B` is the "radial-1 chart" (the achiever chart with the radial
scalar absorbed into the residual blocks — BANKED `phiGen_smul_radial : phiGen u … B = phiGen 1 …
(smulRmatRfin u B)`, sound, axiom-clean).

The OPEN obligation `hdet : |det DB| = ∏_s engine_s` (u-free, `engine_s = |det K_s|^{r_s+c_s}·∏|q|^{...}`).

TWO claims about `hdet`:
- **(MINE)** Define `B := composeFold BFactors` with `BFactors = (finRange (L-1)).flatMap (s ↦ [schur_s,
  chain_s, ldu_s])` (the per-boundary `ChartFactor`s, each a `conjBlockFactor` of the banked
  `schurFrameMap`/`chainUnitMap`/`lduCoreMap` by a `chartIdxEquiv`-derived CLE). Then `DB =
  (foldDerivList BFactors (pivotBlowupOn … u)).prod` (BANKED `composeFold_hasFDerivAt`), and `hdet` is
  the BANKED telescope `foldDerivList_abs_det_perBoundary` (composeFold_abs_det + the chain-1s drop +
  per-boundary schur·ldu grouping) fed by the BANKED per-factor dets `schurChartFactor_abs_det` (=
  `|K_s|^{r+c}`), `lduChartFactor_abs_det` (= `∏|q|^{...}`), `chainChartFactor_abs_det` (= 1). So `hdet`
  is BANKED-reducible — NOT an opaque-width fused-frame det.
- **(FORMALISER + its Codex)** `B = composeFold BFactors` reintroduces the DEAD F1 disjoint-factor-fold
  coupling bug (the chain accumulator couples boundaries; `composeFold fs = φ` was refuted, genm-mapeq
  @d7e75c8d). So `hdet` needs "the existing staircase/fused-frame determinant machinery" (the unfinished
  b-FrameM ladder: HasFDerivAt over opaque widths + toSquareBlock reindex + per-block engine dets), a
  long-pole. The formaliser DECLINED to build `B = composeFold` for this reason.

## The crux

The F1 refutation was: "the whole nonlinear CHART `φ` does NOT equal `composeFold [disjoint factors]`"
(the chain accumulator `C_{k+1}` couples boundaries, so the factor MAPS don't compose to `φ` as VALUES).

My route does NOT claim `composeFold BFactors = φ`. It claims:
(i) `φ = B ∘ pivotBlowupOn` (the radial split — separately, via `phiGen_smul_radial` + the map identity `hmap`);
(ii) `B = composeFold BFactors` (the boundary factor = the radial-1 chart, as a VALUE equality).

So the question reduces to: does (ii) `B = composeFold BFactors` hit the SAME F1 coupling bug? `B` is the
radial-1 chart (still the full chain with `C_{k+1}` coupling, just radial=1). The `BFactors` are the
per-boundary `schur/chain/ldu` factor MAPS conjugated by per-boundary CLEs.

## Questions

1. **Is `hdet` banked-reducible in route #1, or not?** The KEY distinction: `hdet` only needs `|det DB|`,
   NOT a VALUE equality `B = composeFold BFactors`. Even if `B ≠ composeFold BFactors` as VALUES (F1
   coupling), is it enough that `DB` (= B's actual fderiv) has the SAME DET as `(foldDerivList BFactors
   _).prod`? I.e. can I take `DB := (foldDerivList BFactors _).prod` as a FREELY-CHOSEN CLM in the `BData`
   (the `BData.DB` field is arbitrary — it just needs `hasDB : HasFDerivAt B DB`), so I need
   `HasFDerivAt B ((foldDerivList BFactors _).prod)` — which DOES require `B`'s fderiv to equal the
   composeFold fderiv, hence (essentially) the F1 value/derivative equality? OR is there a route where
   `hdet` is read off `B`'s OWN fderiv (whatever it is) being block-triangular with the engine diagonal
   blocks (the locality route), sidestepping `composeFold` entirely?

2. **If `B = composeFold BFactors` genuinely hits F1**, is the formaliser right that `hdet` then needs the
   fused-frame det (b-FrameM)? OR does the radial-1 reduction (`B` = radial-1 chart) make `B`'s fderiv
   block-triangular under the layer grading (the BANKED locality `Agen_..._reads_le` lifted to `B`), so
   `hdet` = `fderiv_abs_det_eq_prod_diagBlocks` (BANKED) + per-boundary diagonal-block engine dets — which
   is the locality route, NOT the dead composeFold AND NOT necessarily the full unfinished b-FrameM (since
   the per-block engine dets are the banked `schurFrameProd_block_*` + `schurFrame_abs_det`)?

3. **Bottom line: is the formaliser's "do NOT build a full BData; the no-hmap routes shed the hmap budget
   piece" recommendation SOUND, or over-pessimistic?** The no-hmap routes
   (`interiorDet_phiFlatLiveR1_of_stairConj`, `interiorDet_headline_of_blockTri`) take the factorization as
   a HYPOTHESIS off the fderiv/frame — so they ALSO need `|det Dφ| = monomial` proven, just packaged
   differently. Does dropping `hmap` actually SHED work, or just RELOCATE the same det obligation? Which of
   {full BData via composeFold-hdet, full BData via locality-hdet, no-hmap stairConj, no-hmap blockTri} is
   the genuinely-least-remaining-work to the unconditional headline, given what's BANKED
   (radialComp_abs_det, foldDerivList_abs_det_perBoundary, the per-factor _abs_det's, phiGen_smul_radial,
   the locality fderiv_abs_det_eq_prod_diagBlocks, schurFrameProd_block_*, the count radialRcols_card)?

Be concrete, skeptical, Lean-v4.29-specific. The disagreement is whether `hdet` is banked-reducible (mine)
or a fused-frame long-pole (formaliser's). Adjudicate, and name the least-work route to the headline.
