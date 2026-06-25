
## LANDED transport lemmas

- `chartPsiTower_gaugeEquiv : chartPsiTower (gaugeEquiv (endpointGauge⁻¹) p)
     = eval₂Hom schurToGfib.toRingHom (fun x ↦ chartPsiTower (gaugeSub (endpointGauge⁻¹) x)) p`.
- `gaugeEquiv_endpointGauge_multPoly : gaugeEquiv (endpointGauge) (multPoly rr cc)
     = (((Lmat)⁻¹.map C * Matrix.of (multPoly) * (Hmat)⁻¹.map C) rr cc)` over `SchurLoc`
  (the conjugation transport; `Lmat`, `Hmat` are the SchurLoc endpoint gauge units, det Hmat = detSchurS up to units, det Lmat = 1 (lower-unitriangular)).
- `schurComplement_normal_form` (CommRing, blocks): with `Δ` invertible and `B22 = B21 Δ⁻¹ B12`,
  `L⁻¹ · [[Δ,B12],[B21,B22]] · H⁻¹ = diag(I_r, 0)` where `L=[[I,0],[B21Δ⁻¹,I]]`, `H=[[Δ,B12],[0,I]]`.
- `isUnit_det_schurΔLoc : IsUnit (schurΔLoc).det` (`= detSchurS`, the inverted element).
- `evalAway_chartPsiAeval` (just landed): `evalAway s B hs (chartPsiAeval p)
     = aeval (canonicalCoord (baseChange (evalGauge (schurEval s) endpointGauge⁻¹) B)) p`
  for any p, all fibre points B and s with detSchurS s ≠ 0.

## THE GOAL

`chartPsi_dsig_isUnit : IsUnit (chartPsiQuot chartDsig)`, i.e. `IsUnit (chartPsiAeval ΔPdeep)` in `Away gF`.

## My analysis / candidate routes

ROUTE A (symbolic det). `chartPsiAeval` is an alg-hom, so `chartPsiAeval (det M) = det (M.map chartPsiAeval)`.
Thus `chartPsiAeval ΔPdeep = det (submatrix (fun a b ↦ chartPsiAeval (multPoly a b)) ...)`. By the gauge
transport, `chartPsiAeval (multPoly a b)` = the (a,b) entry (carried into `Away gF` via `chartPsiTower`/
`schurToGfib`) of `Lmat⁻¹ · multPoly · Hmat⁻¹` over SchurLoc. The top-left r×r block of this conjugated
product — is its determinant a unit? Here Lmat,Hmat are the *Schur*-generic gauge (independent of multPoly),
so the top-left block is NOT obviously `I_r`. I worry ROUTE A needs a genuine determinant identity
`det(top-left r×r of Lmat⁻¹ M Hmat⁻¹)` = (unit). Is there a clean Cauchy-Binet / block-det route?

ROUTE B (the value is literally `1`, or a unit, by a different normalization). Is the intended fact that
`chartPsiAeval ΔPdeep` is actually a UNIT MULTIPLE of the image of `detSchurS` (which is a unit in `Away gF`
since `gF = map detSchurS` is the inverted element)? I.e. `chartPsiAeval ΔPdeep = u · algebraMap(...)(detSchurS-image)`
for a unit `u`? If so, the cleanest is to compute the symbolic value as `(unit) · gF-related-unit`.

ROUTE C (avoid the symbolic det entirely). Since `Away gF` is a localization of `P = MvPolynomial SchurVar O(F)`,
and `O(F)` is a domain (F irreducible? actually F = fibre is irreducible), `Away gF` is a domain. In a domain,
`IsUnit z`? No — being a unit in a localization is NOT just being nonzero. BUT: is there a way to show
`chartPsiAeval ΔPdeep` divides a power of `gF` (hence becomes a unit in `Away gF`)? Concretely, is
`chartPsiAeval ΔPdeep` equal to `gF`-image times a unit, OR does `chartPsiAeval ΔPdeep · (something) = gF^n`
so that it's invertible after inverting gF? Pin the cleanest sufficient condition for `IsUnit` in `Away gF`:
`IsUnit z ↔ ∃ w, z * w ∈ (powers gF)`? Or `z` associate to `gF^n`?

## Questions

Q1. Which route? Is the intended symbolic identity `chartPsiAeval ΔPdeep = (unit) · (image of detSchurS)` —
and if so what is the unit (det of the unitriangular Lmat = 1, so maybe `chartPsiAeval ΔPdeep` = det of the
top-left block which telescopes to `det Δ_schur = detSchurS` up to the Hmat triangular factor)? Walk the
block-determinant computation: with M = multPoly (generic p×q), Lmat = [[I,0],[B21Δ⁻¹,I]] (p×p),
Hmat = [[Δ,B12],[0,I]] (q×q) over SchurLoc, what is `det(top-left r×r of Lmat⁻¹ · M · Hmat⁻¹)`?
Lmat⁻¹=[[I,0],[-B21Δ⁻¹,I]], Hmat⁻¹=[[Δ⁻¹,-Δ⁻¹B12],[0,I]]. Top-left r×r of Lmat⁻¹ M Hmat⁻¹ =
(rows 0..r-1, cols 0..r-1). Compute it and its det.

Q2. The cleanest Mathlib v4.29 way to get `IsUnit` in `Localization.Away g` of an element shown equal to a
unit times `algebraMap (the inverted-element-image)`. Is it `isUnit_of_mul_eq_one`, or
`IsLocalization.Away.algebraMap_isUnit` composed with `IsUnit.mul`? And `chartPsiAeval (det M) = det (M.map chartPsiAeval)` — is it `AlgHom.map_det` / `RingHom.map_det` / `MvPolynomial.aeval` + `det`?

Q3. Is ROUTE C (divisibility into a gF-power) viable and SIMPLER than the symbolic det? Pin the lemma for
"x is a unit in Away g iff x divides some power of g in the base" if it exists at v4.29
(`IsLocalization.Away...`), or confirm it does not and route A/B is needed.

Please answer concretely, do the Q1 block-det computation explicitly, and give the cleanest skeleton.

warning: Model metadata for `gpt-5-codex` not found. Defaulting to fallback metadata; this can degrade performance and cause issues.
codex
**Route Choice**
- Route A/B win: via `chartPsiAeval ΔPdeep = det ( (Lmat⁻¹ · multPoly · Hmat⁻¹).submatrix … )` and the transported Schur-complement normal form you already have, the top-left block is literally `I_r`, so the determinant is `1`. This is cleaner than trying to chase divisibility (Route C needs extra infrastructure and still funnels through the same identity) and evaluation alone cannot certify units in a localization.

**Block Computation**
- Write the gauge identity in `SchurLoc` as  
  `chartPsiAeval (Matrix.of (multPoly)) = (Lmat)⁻¹ ⬝ base ⬝ (Hmat)⁻¹`,  
  using `gaugeEquiv_endpointGauge_multPoly`. By your `schurComplement_normal_form`,
  ```
  (Lmat)⁻¹ ⬝ blockMatrix ![![Δ,B₁₂],![B₂₁,B₂₂]] ⬝ (Hmat)⁻¹
    = blockDiagonal ![1̇_r, 0̇]
  ```
  where `Δ = schurΔLoc` is invertible and `B₂₂ = B₂₁ Δ⁻¹ B₁₂`. Taking top-left `r × r` minors commutes with conjugation by block-unitriangular matrices: the first `r` rows of `Lmat⁻¹` equal the first `r` rows of the identity, and the first `r` columns of `Hmat⁻¹` equal those of the identity, so the top-left submatrix of the product is exactly the top-left submatrix of the Schur-normal-form, namely `I_r`. Hence
  ```
  chartPsiAeval ΔPdeep
    = AlgHom.map_det chartPsiAeval _
    = Matrix.det (Matrix.submatrix … (chartPsiAeval ∘ multPoly))
    = Matrix.det (I_r) = 1.
  ```
  You can formalize this with:
  - `AlgHom.map_det` (`Mathlib/LinearAlgebra/Determinant.lean`)
  - `Matrix.submatrix_mul_equiv` or `Matrix.submatrix_mul` for steering the block computation
  - `Matrix.upperLeft_blockDiagonal` to identify the top-left block with `I_r`
  - `Matrix.det_one` for the final step.

**Localization Step**
- Because `chartPsiAeval ΔPdeep = 1`, use `IsUnit.one` (or simply `by simpa using (isUnit_one (R := Away gF))`) to get the goal; no localization lemmas needed.
- If you prefer keeping the unit-multiple-of-`detSchurS` phrasing, your normal form gives  
  `chartPsiAeval ΔPdeep = ((Hmat).det)⁻¹ * detSchurS`, with `det Hmat = detSchurS` and `det Lmat = 1`. Combine `isUnit_det_schurΔLoc` with `IsUnit.mul` and `IsLocalization.Away`. The key lemmas:
  - `IsLocalization.Away.self (R := P)` to inherit units of the inverted element.
  - `IsLocalization.map_units` plus `IsUnit.mul` in `Away gF`.

**Evaluation Route (Why Not)**
- Evaluation at a single point `s` with `detSchurS s ≠ 0` only shows the value is nonzero in that residue field, but units of a localization correspond to elements whose numerator divides a power of the inverted element in the base ring. Without already knowing the symbolic factor of `detSchurS`, evaluation cannot certify invertibility.

**Route C Comment**
- v4.29 offers `IsLocalization.isUnit_iff_exists` (`Mathlib/RingTheory/Localization/Basic.lean`), specializing to `IsLocalization.Away`. To use it you need to produce `n` and `y` with `chartPsiAeval ΔPdeep * y = algebraMap _ _ (gF^n)`. That boils down to exactly the determinant computation above; there isn’t a shorter path.

**Suggested Proof Skeleton**
1. Expand `chartPsiQuot chartDsig` to `chartPsiAeval ΔPdeep`.
2. Apply `AlgHom.map_det`.
3. Rewrite the mapped matrix using `gaugeEquiv_endpointGauge_multPoly`, then apply your `schurComplement_normal_form` lemma to identify the top-left block with `⟨I_r⟩`.
4. Finish with `Matrix.det_one` and `isUnit_one`.
tokens used
18,308
**Route Choice**
- Route A/B win: via `chartPsiAeval ΔPdeep = det ( (Lmat⁻¹ · multPoly · Hmat⁻¹).submatrix … )` and the transported Schur-complement normal form you already have, the top-left block is literally `I_r`, so the determinant is `1`. This is cleaner than trying to chase divisibility (Route C needs extra infrastructure and still funnels through the same identity) and evaluation alone cannot certify units in a localization.

**Block Computation**
- Write the gauge identity in `SchurLoc` as  
  `chartPsiAeval (Matrix.of (multPoly)) = (Lmat)⁻¹ ⬝ base ⬝ (Hmat)⁻¹`,  
  using `gaugeEquiv_endpointGauge_multPoly`. By your `schurComplement_normal_form`,
  ```
  (Lmat)⁻¹ ⬝ blockMatrix ![![Δ,B₁₂],![B₂₁,B₂₂]] ⬝ (Hmat)⁻¹
    = blockDiagonal ![1̇_r, 0̇]
  ```
  where `Δ = schurΔLoc` is invertible and `B₂₂ = B₂₁ Δ⁻¹ B₁₂`. Taking top-left `r × r` minors commutes with conjugation by block-unitriangular matrices: the first `r` rows of `Lmat⁻¹` equal the first `r` rows of the identity, and the first `r` columns of `Hmat⁻¹` equal those of the identity, so the top-left submatrix of the product is exactly the top-left submatrix of the Schur-normal-form, namely `I_r`. Hence
  ```
  chartPsiAeval ΔPdeep
    = AlgHom.map_det chartPsiAeval _
    = Matrix.det (Matrix.submatrix … (chartPsiAeval ∘ multPoly))
    = Matrix.det (I_r) = 1.
  ```
  You can formalize this with:
  - `AlgHom.map_det` (`Mathlib/LinearAlgebra/Determinant.lean`)
  - `Matrix.submatrix_mul_equiv` or `Matrix.submatrix_mul` for steering the block computation
  - `Matrix.upperLeft_blockDiagonal` to identify the top-left block with `I_r`
  - `Matrix.det_one` for the final step.

**Localization Step**
- Because `chartPsiAeval ΔPdeep = 1`, use `IsUnit.one` (or simply `by simpa using (isUnit_one (R := Away gF))`) to get the goal; no localization lemmas needed.
- If you prefer keeping the unit-multiple-of-`detSchurS` phrasing, your normal form gives  
  `chartPsiAeval ΔPdeep = ((Hmat).det)⁻¹ * detSchurS`, with `det Hmat = detSchurS` and `det Lmat = 1`. Combine `isUnit_det_schurΔLoc` with `IsUnit.mul` and `IsLocalization.Away`. The key lemmas:
  - `IsLocalization.Away.self (R := P)` to inherit units of the inverted element.
  - `IsLocalization.map_units` plus `IsUnit.mul` in `Away gF`.

**Evaluation Route (Why Not)**
- Evaluation at a single point `s` with `detSchurS s ≠ 0` only shows the value is nonzero in that residue field, but units of a localization correspond to elements whose numerator divides a power of the inverted element in the base ring. Without already knowing the symbolic factor of `detSchurS`, evaluation cannot certify invertibility.

**Route C Comment**
- v4.29 offers `IsLocalization.isUnit_iff_exists` (`Mathlib/RingTheory/Localization/Basic.lean`), specializing to `IsLocalization.Away`. To use it you need to produce `n` and `y` with `chartPsiAeval ΔPdeep * y = algebraMap _ _ (gF^n)`. That boils down to exactly the determinant computation above; there isn’t a shorter path.

**Suggested Proof Skeleton**
1. Expand `chartPsiQuot chartDsig` to `chartPsiAeval ΔPdeep`.
2. Apply `AlgHom.map_det`.
3. Rewrite the mapped matrix using `gaugeEquiv_endpointGauge_multPoly`, then apply your `schurComplement_normal_form` lemma to identify the top-left block with `⟨I_r⟩`.
4. Finish with `Matrix.det_one` and `isUnit_one`.
