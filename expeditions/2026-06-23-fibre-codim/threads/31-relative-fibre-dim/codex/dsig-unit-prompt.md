# Consult: Lean 4 / Mathlib v4.29 — show a comorphism image of a determinant is a UNIT in a localization

I am formalising the route-(c) localized chart `AlgEquiv` for deep-linear-network fibres. I need to
prove ONE remaining `IsUnit` statement. I want (a) the cleanest route, (b) whether an
evaluation-based argument can work or I genuinely need the symbolic value, (c) v4.29 lemma names.

## Setup (all LANDED, sorry-free)

- `k` alg-closed field char 0.
- `O(F) = MvPolynomial τ k ⧸ vanishingIdeal F` (fibre coord ring), `τ = RepCoord d`.
- `P = MvPolynomial SchurVar O(F)`, `gF = map (algebraMap k O(F)) detSchurS : P`, `Away gF`.
- `SchurLoc = Localization.Away detSchurS` (`detSchurS : MvPolynomial SchurVar k`).
- `multPoly d a b : MvPolynomial (RepCoord d) k` — the (a,b) entry of the generic matrix product
  (a polynomial in the RepCoord variables).
- `ΔPdeep d r := det (submatrix (Matrix.of (multPoly d)) castLE castLE) : MvPolynomial (RepCoord d) k`
  — the top-left r×r minor of the generic product.
- `chartPsiAeval : MvPolynomial (RepCoord d) k →ₐ[k] Away gF` — the Ψ comorphism,
  `= aeval (chartPsiSub)`, where `chartPsiSub x = chartPsiTower (gaugeSub (endpointGauge⁻¹) x)`.
- `chartPsiQuot : O(Σ^r) →ₐ[k] Away gF` — the descent of `chartPsiAeval` through `vanishingIdeal Σ^r`
  (just landed). `chartDsig = mk (vanishingIdeal Σ^r) ΔPdeep`. So
  `chartPsiQuot chartDsig = chartPsiAeval ΔPdeep` (descent commutes with `mk`).

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
