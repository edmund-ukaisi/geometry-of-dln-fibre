# Statement card — general-`L` smeared `hcancel`/`hUpos` reduction to two box determinants

**Status:** PROVED (sorry-free), on `origin/genm-smeardata` (based on `origin/genm-smearcont @ce19dc4a`,
the general-`L` SMEARED ENGINE). Axiom footprint `[propext, Classical.choice, Quot.sound]` — measure-free
pure matrix algebra, NO `monomial_rlct`, NO `sorryAx`. Two new modules, both green (8335 jobs). Aggregator
wiring left for the controller.

## What is proved (the crux, de-risked and reduced ∀L)

The boundary-smeared chart's two genuinely-analytic per-point hypotheses — the shear cancellation
`hcancel` (`P₁·Λ₀ = P₂`, THE CRUX) and the unit positivity `hUpos` (`UunitG > 0`) — are BOTH reduced,
for arbitrary depth `0 < L` and arbitrary widths, to the SAME two determinant conditions on the source
box:

* **Gram** `det ((P1uG u)ᵀ (P1uG u)) ≠ 0` — `P₁` has full column rank `r`;
* **waist-block** `det (V[:, deepWidthEquiv ∘ inl]) ≠ 0` — the top-`r` block of the width-`r` waist
  factor `V` is invertible (`frontProd u = U · V`, inner `Fin r`).

### `RouteMSmearedCancelGen.lean` (the reduction, 132 LoC, sorry-free)
- `frontProd_factorsThrough_waist` — the width-`r` `U·V` factorization of `frontProd = prodAux (L−1)`
  through a waist layer `q ≤ L−1` with `M ⟨q,_⟩ = r`, via banked `prodAux_split_exists` + a `finCongr`
  inner-type recast (`Fin (M ⟨q,_⟩) ≃ Fin r`).
- `hcancelG_of_waist` — `P1uG u · Lam0uG u = P2uG u` from the waist + the two dets, via banked
  `frontShear_cancel_general` (`RouteMSmearedFrontFactor`) with `ρ = deepWidthEquiv ∘ inl`,
  `σ = deepWidthEquiv ∘ inr`. `Lam0uG = (P₁ᵀP₁)⁻¹P₁ᵀP₂` is exactly the projection routing.
- `mul_eq_zero_of_gram_det_ne` — full-column-rank left-injectivity (`P₁·X = 0 ⟹ X = 0` off the Gram
  pole); the tall-`P₁` analog of "left-mult by invertible is injective".
- `UunitG_pos_of_gram_det_ne` — `UunitG > 0` from the Gram det (`H̄_unit` pivot entry `= 1` nonzero
  + left-injectivity ⟹ `P₁·H̄ ≠ 0` ⟹ Frobenius sum positive). Tall analog of the square
  `Uunit_pos_of_det_ne`.

### `RouteMSmearedDetData.lean` (the chart-data wrapper, sorry-free)
- `smearedChartDataGen_of_dets` — a `SmearedChartData M n hN psiMapG RmapG DmapG p (r·c−1) ε` from: a
  waist `q`, the box `(δ₀, box₀)`, Field-A containment `hSpre`, `RmapG`-injectivity `hRinj`,
  measurability, and the two per-point dets (`hGram` at cancellation points, `hGram0` at `z=0`
  positivity points, `hWaist` at cancellation points). Discharges `smearedChartDataGen`'s `hcancel`/
  `hUpos` from the dets via the reduction above; all mechanical chart fields come from `smearedChartDataGen`.

## The soundness-critical structural input (p&p verdict, `1 ≤ minAdm ∧ BoundarySmeared` — UNCONDITIONAL)
There is a **width-`r` front waist**: `∃ q ≤ L−1, M q = r = deepRank M = min_{i≤L−1} M i`. Decomposed as
(A) `r ≤ M q ∀ q ≤ L−1` [universal: weak-decrease of `tStar`/`Text` + `admBound`] and (B)
`smeared ⟹ min_{q≤L−1} M q ≤ r` [the `¬InteriorDrop` contradiction, leans on `Wext L = M L > 0` from
`minAdm ≥ 1` — keep `1 ≤ minAdm` explicit alongside `BoundarySmeared`]. Codex-reconciled, verified
0 violations over L=2..5. **Caveat: the waist location VARIES** — `(1,2,1)` waist@layer0, `(2,1,2,1)`
waist@layer1 — the chart must locate `q`, not assume `M1 = r`.

The **rectangular tall-`P₁` case genuinely occurs** (min witness `M = (2,1,2,1)`, L=3: `deepRank = 1 <
M0 = 2`, boundary-smeared); the L=2 square reduction (`smeared_deepRank_eq_M0`) does NOT generalize past
L=2. So the tall `P₁` and the factors-through `col(P₂) ⊆ col(P₁)` are genuine, not hidden.

## What remains for the FULLY-unconditional `hSmeared ∀L` (the precise scope for a dedicated effort)

Two large-but-standard residuals, each comparable to the L=2 machinery it generalizes. Both are needed
to feed `smearedChartDataGen_of_dets` from a concrete box and close `hSmeared ∀L` outright.

### Residual 1 — the general-box cross-term determinant theorem (discharges `hGram`/`hGram0`/`hWaist`)
The two dets on a POSITIVE-measure box (no exact 0/1 pinning — `hboxpos` forbids singletons). The
obstruction: `P₁ = C·G₁` and `V` are PRODUCTS of raw layers when the waist `q ≥ 1` (or the suffix is
long), and **"product of strictly-diagonally-dominant matrices is diag-dominant" is FALSE** (counter:
`[[1,0.9],[0,1]]·[[1,0],[−0.9,1]]` has row `[0.19, 0.9]`). What replaces it:
- the DET route is cheap — `det (∏ Aᵢ) = ∏ det Aᵢ` (`Matrix.det_mul` + `Finset.prod_ne_zero_iff`), so a
  product of matrices each with `det ≠ 0` has `det ≠ 0`; BUT the relevant `r×r` MINOR of the product is
  `carrier product + off-carrier cross terms`, not a clean product, because positive-width off-carrier
  entries are not exactly 0.
- so the theorem needed is a **combinatorial perturbation bound**: pin each layer's carrier `r×r` block
  near a scaled identity (diagonal in `(3/4,5/4)`, off-diagonal in `(−1/(8r),1/(8r))`) and all
  non-carrier entries in `(−η,η)`; expand the product-minor entry as a sum over paths, isolate the
  unique all-carrier path, bound each off-carrier path by `#paths · η · C^{len−1}`, choose `η` small so
  the selected block stays strictly row-diagonally-dominant (Codex: prove `‖H − I‖_row < 1/2` directly,
  then reuse `Core.Matrix.DiagDominance.StrictRowDominant.det_ne_zero`). ~35–60 lemmas; hardest step =
  the path-expansion cross-term bound for arbitrary widths + arbitrary carrier injections; second
  hardest = "nonzero `r×r` minor of rectangular `C` ⟹ `det(P₁ᵀP₁) ≠ 0`" (full-column-rank ⟹ Gram
  nonzero over ℝ — may need a small local Mathlib bridge). Also nontrivial: keeping the varying waist
  `q` from infecting definitions with casts.
- This is large-but-STANDARD matrix analysis (not a research wall). Recommended vehicle: a p&p
  cross-term-theorem design → broken-down formalise.

### Residual 2 — the general-`L` Field-A entry bound (discharges `hSpre`)
No general-`L` analog of the L=2 `condBox_subset_preimage` exists yet (that is `Fin 3`-hardcoded, via
`psiMap_Rmap_eq_phiL2` + `chartL2Params_entry_bound` + the Varah `Λ₀`-entry bound
`StrictRowDominant.inv_mul_entry_bound`, banked in Core). The general-`L` version bounds each decoded
flat entry of `psiMapG (RmapG u)` by `2δ` (to land in `cubeBox`): `frontProd` entries are products of
`L−1` raw coords (each `≤ δ`, so `≤ δ^{L−1}`), `Λ₀` entries via Varah, `z·H̄` and `S_bot` linear. The
`genDecode_params` decode already gives the flat structure; the residual is the entrywise bound through
the decode + the Varah `Λ₀` bound at general widths. Comparable to the L=2 `RouteMSmearedSquareL2` Field-A
block (~200 lines).

### Non-vacuity witness (`(2,1,2,1)`, L=3, r=1) — NOT built
The minimal rectangular witness. Its two dets ARE cheap in principle (`r=1`: Gram `= ‖P₁‖²`, waist-block
`= 1×1` = single coord `A¹[0][ρ0]`), but the concrete discharge is NOT a quick win: `coordOfG` is the
NONCOMPUTABLE slot bijection (`Fintype.equivFin`), so even the raw-coord readoff needs abstract slot
reasoning, and the full witness additionally needs Residual 2 (Field A) for this specific `M`. Deferred.

## Reusable value banked NOW
`smearedChartDataGen_of_dets` collapses the per-family smeared-chart work at ANY depth to: box + Field-A +
`RmapG`-injectivity + measurability + the two diagonal-dominance dets — with `hcancel`/`hUpos` (the two
genuinely-analytic facts the certificate adjudicated) already discharged. The crux is closed as a
reduction; the residuals are mechanical/standard.
