# Statement card — direction-2 staircase headline spine + the precise conjugacy residual, `genm-detbridge`

The linear-map-level determinant SPINE of the direction-2 staircase factorization of the unconditional
interior-det headline, tied to the REAL chart `phiFlatLiveR1`. Branch `genm-detbridge` (off
`genm-detalpha`). All bricks sorry-free, clean-three, forced `#print axioms` (oleans deleted + rebuilt).

This leg banks the **sound TARGET-SHAPED spine** that consumes `genm-detalpha`'s bricks
(`fderiv_det_one_of_shear`, `lowerTri_det`, the engine dets) and produces the headline conditional on a
SINGLE remaining obligation — the staircase conjugacy of the real `fderiv`. It does NOT yet build that
conjugacy (the cast-heavy multi-tide construction `staircase-det-bricks-statement-card.md` flags).

## Brick 1 — the general `n`-fold staircase determinant (`RouteMStairFold`)

> **Claim.** A block-lower-triangular endomorphism of a nested product `V 0 × (V 1 × (… × PUnit))`, with
> diagonal blocks `f 0, …, f (n−1)` and arbitrary strictly-lower couplings, has determinant `∏_{s : Fin
> n} (f s).det` — the couplings are det-irrelevant.
>
> - **Lean:** `DLNFibre.DLN.RLCT.{StairProd, StairCoupling, stairMap, stairMap_det}`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMStairFold.lean`)
> - **Gloss.** `StairProd V n` the nested product; `stairMap V n f c` the staircase (recursing as
>   `lowerTri (f 0) (stairMap tail) c.1`); `stairMap_det : det (stairMap V n f c) = ∏_{s:Fin n}(f s).det`,
>   by induction peeling one `RouteMSchurFrameDet.lowerTri_det` per layer + `Fin.prod_univ_succ`.
> - **Proved (unconditional, sorry-free, clean-three).** The general-`L` generalization of
>   `RouteMStaircaseDet.lowerTri3_det` (which the prior card DEFERS); non-vacuity witness at `n = 3`.
> - **Assumed / Cited / Deferred.** none.

## Brick 2 — the staircase det on ANY conjugate endomorphism (`RouteMStairFold`)

> **Claim.** If a flat endomorphism `D` is conjugate — through a layer-collecting `LinearEquiv e` — to a
> `stairMap` (`D = e.symm ∘ stairMap ∘ e`), then `det D = ∏_s (f s).det` (`|det D| = ∏_s |(f s).det|`).
>
> - **Lean:** `DLNFibre.DLN.RLCT.{stairMap_det_conj, stairMap_abs_det_conj}` (same file)
> - **Gloss.** `LinearMap.det_conj` (conjugation det-invariance) + `stairMap_det`. The
>   `prodEquivOfIsCompl`-gluing escape (`coarse-route-grading-obstruction.md`): the det is read at the
>   LINEAR-MAP level, NO single-grading `Matrix.BlockTriangular`. `e` is ONE equiv applied to both
>   input+output, so the off-diagonal couplings absorb the input/output partition mismatch that BLOCKED
>   the `BlockTriangular` route — the conjugation form is genuinely more flexible.
> - **Proved (sorry-free, clean-three).**

## Brick 3 — the cast lemma `finSplit.symm` (`RouteMStaircaseShear`)

> **Claim.** The inverse-direction evaluation of the canonical width split `finSplit`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.{finSplit_symm_inl, finSplit_symm_inr}`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMStaircaseShear.lean`)
> - **Gloss.** `finSplit h .symm (Sum.inl i) = Fin.cast _ (Fin.castAdd _ i)` / `(Sum.inr a) = Fin.cast _
>   (Fin.natAdd _ a)`. The dual of the banked `chainA_apply_castAdd/natAdd` forward reads — every
>   staircase-block read of `chainA`/`chainQ` needs it (Codex's named first de-risking increment).
> - **Proved (sorry-free, `[propext, Quot.sound]`).**

## Brick 4 — the interior-det HEADLINE via the staircase conjugacy (`RouteMStairHeadline`)

> **Claim.** The interior-det headline restated for route-2: IDENTICAL output formula to
> `interiorDet_headline_of_blockTri`, SOUND hypotheses (staircase conjugacy + engine block-dets).
>
> - **Lean:** `DLNFibre.DLN.RLCT.interiorDet_headline_of_stairConj`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMStairHeadline.lean`)
> - **Gloss.** Given `D = e.symm ∘ stairMap V (L+1) f c ∘ e`, radial `|det (f 0)| = |u_p|^{minAdm−1}`,
>   boundary `|det (f (s+1))| = |det K_s|^{r_s+c_s}·∏_i|q_{s,i}|^{2(t_s−1−i)}`, then `|det D| =
>   |u_p|^{minAdm−1}·∏_{s:Fin L}(…)`. `stairMap_abs_det_conj` + `Fin.prod_univ_succ` (radial layer 0 split
>   from the L boundary layers). Non-vacuity witness fires it on a concrete `L=1` frame.
> - **Proved (sorry-free, clean-three).** The SOUND replacement for the REFUTED single-grading
>   `BlockTriangular` form (`RouteMGradingObstruction`); same OUTPUT formula.

## Brick 5 — the headline on the REAL chart `phiFlatLiveR1` (`RouteMInteriorDetReal`)

> **Claim.** Brick 4 tied to the ACTUAL flat chart `fderiv ℝ (phiFlatLiveR1 …) u` — not a surrogate.
>
> - **Lean:** `DLNFibre.DLN.RLCT.interiorDet_phiFlatLiveR1_of_stairConj`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean`)
> - **Gloss.** `hconj : (fderiv ℝ (phiFlatLiveR1 …) u).toLinearMap = e.symm ∘ stairMap V (L+1) f c ∘ e`
>   + engine block-dets ⟹ the real chart Jacobian abs-det is the headline monomial. Stated on the REAL
>   `fderiv` (whose EXISTENCE is the banked `phiFlatLiveR1_differentiableAt`), so the hypothesis cannot be
>   discharged by an engine surrogate (Codex's flagged trap — the decorrelated soundness check).
> - **Proved (sorry-free, clean-three).**

## The precise residual (the lone remaining obligation — for the controller)

The unconditional `interiorDet_headline` (general M) reduces to ONE goal: the **staircase conjugacy of the
real fderiv**, i.e. construct

  `V : ℕ → Type`, `f : (s:ℕ) → V s →ₗ V s`, `c : StairCoupling V (L+1)`,
  `e : (Fin (routeMAmbient M) → ℝ) ≃ₗ StairProd V (L+1)`

with

  `(fderiv ℝ (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u).toLinearMap
     = e.symm ∘ₗ stairMap V (L+1) f c ∘ₗ e`

and the engine block-det identifications `|det (f 0)| = |u_p|^{minAdm−1}` (radial, `radial_abs_det_minAdm`),
`|det (f (s+1))| = |det K_s|^{r_s+c_s}·∏_i|q_{s,i}|^{2(t_s−1−i)}` (Schur⊗LDU,
`schurFrame_abs_det × lduCoreDeriv_abs_det`). Feeding these to `interiorDet_phiFlatLiveR1_of_stairConj`
closes the unconditional headline.

**Why this is the genuine cast-heavy multi-tide construction (not a ≤4-attempt closure):**
- It requires COMPUTING `fderiv (paramsEquivFlat ∘ chartParamsGen)` over opaque `Text`/`Wext` widths,
  where `chartParamsGen ⟨s⟩ = reindex (Agen s)` and `Agen s = chainA(N_s, W_s, C(s+1))` carries the
  bilinear `−dN_s·W_s` shear of `Cgen`. The DIFFERENTIABILITY is banked (`phiFlatLiveR1_differentiableAt`,
  `diffAt_Agen`); the fderiv VALUE as a staircase is NOT.
- The conjugating `e` must be built from `paramsEquivFlat` + a chart-coordinate regrouping into
  `StairProd`; the diagonal blocks `f s` are the radial / per-boundary Schur⊗LDU differentials; the
  couplings `c` are the `−dN·W` shears (det-irrelevant). This is the `Frame3333Deriv`/`shear222`
  hand-machinery generalized to opaque M (`(2,2,2)` bridge ≈ 200 lines; opaque-M more), the dependent-`Fin`
  reindex zone the CLAUDE.md gotchas flag as the cost driver.

**Reusable for the residual** (all banked this leg + prior): the `finSplit.symm` cast lemmas (block reads),
`stairMap_abs_det_conj` (the det once `e`/`f`/`c` are exhibited), `chainA_apply_castAdd/natAdd`,
`chainUnit_det` (the frozen-N part is det-1), `fderiv_det_one_of_shear` (the `−dN·W` shear is det-1).

## Banked this leg
- `lean/DLNFibre/DLN/RLCT/Validate/RouteMStairFold.lean` — Bricks 1+2.
- `lean/DLNFibre/DLN/RLCT/Validate/RouteMStaircaseShear.lean` — Brick 3.
- `lean/DLNFibre/DLN/RLCT/Validate/RouteMStairHeadline.lean` — Brick 4.
- `lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean` — Brick 5.
- `threads/80-genM-nodechart/codex/detbridge-strategy-{prompt,answer}.md` — the route adjudication
  (Codex xhigh: compute det via a `HasFDerivAt` identification + iterated `lowerTri`, NOT the explicit
  `pack_M ∘ T_M = chartParamsGen` value bridge).
