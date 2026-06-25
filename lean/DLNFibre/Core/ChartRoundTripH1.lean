/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartRoundTrip

/-!
# `DLNFibre.Core.ChartRoundTripH1` — the Ψ∘Φ round-trip legs (seam E, h1)

The h1-side round-trip `chartPsiLoc ∘ chartPhiLoc = id` on `Away gF`. By `Localization.algHom_ext` +
`MvPolynomial.algHom_ext'` it splits into:
- the **`O(F)`-coefficient leg** `chartPsiLoc (chartPhiCoeff (mk_F (X x))) = fibCoordT x` — a gauge
  round-trip mirror of h2 (the Φ fibre comorphism composed back through Ψ collapses at `eg * eg⁻¹ = 1`);
- the **`SchurVar` variable leg** `chartPsiLoc (chartPhiVarSub s) = algebraMap (X s)` — NOT a gauge
  round-trip: the var leg reads SchurVar off the product blocks of `M`, and the Ψ-image of those
  blocks is `L'·E·H' = [[Δ', B12'], [B21', *]]` (`map_chartPsiAeval_multPoly_eq`), whose Δ/B12/B21
  blocks are exactly the `schurToGfib`-images of the Schur generators.

## Main results
- `submatrix_map_chartPsiAeval_eq_schurB12` / `_schurB21` — the off-diagonal block read-offs.
- `chartPsiLoc_chartPhiVarSub` — the SchurVar var leg.
- `chartPsiLoc_comp_chartPhiTower` / `chartPsiLoc_chartPhiFibSub` — the O(F)-coefficient leg.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
/-- **The B12 block of the Ψ-image of the generic product is `schurB12Loc.map schurToGfib`.** The
`(castLE i, natAdd b)` (pivot row, bordering col) submatrix of `(M.map chartPsiAeval) = L'·E·H'` is
the `(1,2)` block of `[[1,0],[B21Δ⁻¹,1]]·[[1,0],[0,0]]·[[Δ,B12],[0,1]] = [[Δ,B12],[B21,*]]`, i.e.
`B12' = schurB12Loc.map schurToGfib`. Mirror of `submatrix_map_chartPsiAeval_eq_schurΔ`. -/
theorem submatrix_map_chartPsiAeval_eq_schurB12 (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    (((Matrix.of (multPoly d)).map (chartPsiAeval k d r hp hq)).submatrix
        (fun i : Fin r ↦ (Fin.castLE hp i : Fin (d (Fin.last (N + 1)))))
        (fun b : Fin (d 0 - r) ↦
          (Fin.cast (show r + (d 0 - r) = d 0 by omega) (Fin.natAdd r b) : Fin (d 0))))
      = (schurB12Loc (k := k) (d 0) (d (Fin.last (N + 1))) r).map (schurToGfib k d r hp hq) := by
  rw [map_chartPsiAeval_multPoly_eq]
  rw [show (Lmat (k := k) (d 0) (d (Fin.last (N + 1))) r hp).map (schurToGfib k d r hp hq)
      = ((LblockSum (d 0) (d (Fin.last (N + 1))) r).map (schurToGfib k d r hp hq)).submatrix
          (finSplit hp) (finSplit hp) from by
    rw [Lmat, reindexAlgEquiv_apply, reindex_apply, Equiv.symm_symm, ← Matrix.submatrix_map]]
  rw [show (Hmat (k := k) (d 0) (d (Fin.last (N + 1))) r hq).map (schurToGfib k d r hp hq)
      = ((HblockSum (d 0) (d (Fin.last (N + 1))) r).map (schurToGfib k d r hp hq)).submatrix
          (finSplit hq) (finSplit hq) from by
    rw [Hmat, reindexAlgEquiv_apply, reindex_apply, Equiv.symm_symm, ← Matrix.submatrix_map]]
  rw [show (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq).map
        (algebraMap k (Localization.Away (chartGfib k d r hp hq)))
      = ((Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) _) 0 0 0).map
            (algebraMap k (Localization.Away (chartGfib k d r hp hq)))).submatrix
          (finSplit hp) (finSplit hq) from by
    rw [normalForm, ← Matrix.submatrix_map]]
  rw [Matrix.submatrix_mul_equiv _ _ _ (finSplit hp) _,
    Matrix.submatrix_mul_equiv _ _ _ (finSplit hq) _]
  rw [Matrix.submatrix_submatrix]
  ext i b
  rw [Matrix.submatrix_apply, Function.comp_apply, Function.comp_apply,
    finSplit_castLE, finSplit_natAdd]
  rw [LblockSum, HblockSum, Matrix.fromBlocks_map, Matrix.fromBlocks_map, Matrix.fromBlocks_map,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _),
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_apply₁₂]
  -- block-(1,2): `(1·1+0·0)·B12' + (1·0+0·1)·1 = B12'`.
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]

set_option synthInstance.maxHeartbeats 400000 in
/-- **The B21 block of the Ψ-image of the generic product is `schurB21Loc.map schurToGfib`.** The
`(natAdd a, castLE j)` (bordering row, pivot col) submatrix of `(M.map chartPsiAeval) = L'·E·H'` is
the `(2,1)` block `B21' = schurB21Loc.map schurToGfib`. Mirror of the Δ/B12 read-offs. -/
theorem submatrix_map_chartPsiAeval_eq_schurB21 (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    (((Matrix.of (multPoly d)).map (chartPsiAeval k d r hp hq)).submatrix
        (fun a : Fin (d (Fin.last (N + 1)) - r) ↦
          (Fin.cast (show r + (d (Fin.last (N + 1)) - r) = d (Fin.last (N + 1)) by omega)
            (Fin.natAdd r a) : Fin (d (Fin.last (N + 1)))))
        (fun j : Fin r ↦ (Fin.castLE hq j : Fin (d 0))))
      = (schurB21Loc (k := k) (d 0) (d (Fin.last (N + 1))) r).map (schurToGfib k d r hp hq) := by
  rw [map_chartPsiAeval_multPoly_eq]
  rw [show (Lmat (k := k) (d 0) (d (Fin.last (N + 1))) r hp).map (schurToGfib k d r hp hq)
      = ((LblockSum (d 0) (d (Fin.last (N + 1))) r).map (schurToGfib k d r hp hq)).submatrix
          (finSplit hp) (finSplit hp) from by
    rw [Lmat, reindexAlgEquiv_apply, reindex_apply, Equiv.symm_symm, ← Matrix.submatrix_map]]
  rw [show (Hmat (k := k) (d 0) (d (Fin.last (N + 1))) r hq).map (schurToGfib k d r hp hq)
      = ((HblockSum (d 0) (d (Fin.last (N + 1))) r).map (schurToGfib k d r hp hq)).submatrix
          (finSplit hq) (finSplit hq) from by
    rw [Hmat, reindexAlgEquiv_apply, reindex_apply, Equiv.symm_symm, ← Matrix.submatrix_map]]
  rw [show (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq).map
        (algebraMap k (Localization.Away (chartGfib k d r hp hq)))
      = ((Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) _) 0 0 0).map
            (algebraMap k (Localization.Away (chartGfib k d r hp hq)))).submatrix
          (finSplit hp) (finSplit hq) from by
    rw [normalForm, ← Matrix.submatrix_map]]
  rw [Matrix.submatrix_mul_equiv _ _ _ (finSplit hp) _,
    Matrix.submatrix_mul_equiv _ _ _ (finSplit hq) _]
  rw [Matrix.submatrix_submatrix]
  ext a j
  rw [Matrix.submatrix_apply, Function.comp_apply, Function.comp_apply,
    finSplit_natAdd, finSplit_castLE]
  rw [LblockSum, HblockSum, Matrix.fromBlocks_map, Matrix.fromBlocks_map, Matrix.fromBlocks_map,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _),
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_apply₂₁]
  -- block-(2,1): `(B21Δ⁻¹·1+1·0)·Δ + (B21Δ⁻¹·0+1·0)·0 = (B21Δ⁻¹)·Δ`.
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
  -- entrywise, `((B21Δ⁻¹).map g · Δ.map g) = ((B21Δ⁻¹·Δ).map g) = B21.map g` (`g` a ring hom,
  -- `Δ⁻¹·Δ = 1` over `SchurLoc`).
  rw [← Matrix.map_mul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_det_schurΔLoc _ _ _), Matrix.mul_one]

variable (k) in
/-- `chartPsiLoc` carries a `chartPhiVarSub`-block to `algebraMap (X s)` — the bridge needed by the
SchurVar var leg. `chartPhiVarSub s = algebraMap O(Σ) (Away dsig) (mk_Σ (multPoly block))`, and
`chartPsiLoc (algebraMap (mk_Σ p)) = chartPsiAeval p`, so this is `chartPsiAeval (multPoly block)`. -/
theorem chartPsiLoc_chartPhiVarSub_aux [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (rr : Fin (d (Fin.last (N + 1)))) (cc : Fin (d 0)) :
    chartPsiLoc k d r hp hq
        (algebraMap (sweepSigmaRing k d r) (Localization.Away (chartDsig k d r hp hq))
          (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)) (multPoly d rr cc)))
      = chartPsiAeval k d r hp hq (multPoly d rr cc) := by
  rw [chartPsiLoc, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  show chartPsiQuot k d r hp hq
      (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)) (multPoly d rr cc)) = _
  rw [chartPsiQuot, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk, RingHom.coe_coe]

variable (k) in
/-- **The SchurVar var leg of the h1 round-trip** `chartPsiLoc (chartPhiVarSub s) = algebraMap (X s)`.
By cases on the block of `s`: `chartPhiVarSub s = algebraMap (mk_Σ (multPoly block))`, so
`chartPsiLoc (·) = chartPsiAeval (multPoly block)`, which is the corresponding block entry of the
Ψ-image factorization `L'·E·H'` (Δ/B12/B21 read-offs), `= schurToGfib (algebraMap (X s)) =
algebraMap (X s)` (`schurToGfib_algebraMap`). -/
theorem chartPsiLoc_chartPhiVarSub [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : SchurVar (d 0) (d (Fin.last (N + 1))) r) :
    chartPsiLoc k d r hp hq (chartPhiVarSub k d r hp hq s)
      = algebraMap (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
          (sweepFibreRing k d r hp hq)) (Localization.Away (chartGfib k d r hp hq)) (X s) := by
  -- `schurToGfib (algebraMap (X s)) = algebraMap (mapAlgHom (ofId) (X s)) = algebraMap (X s)`.
  have hgfib : ∀ s' : SchurVar (d 0) (d (Fin.last (N + 1))) r,
      schurToGfib k d r hp hq
          (algebraMap (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) k)
            (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) (X s'))
        = algebraMap (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
            (sweepFibreRing k d r hp hq)) (Localization.Away (chartGfib k d r hp hq)) (X s') := by
    intro s'
    rw [schurToGfib_algebraMap,
      show (MvPolynomial.mapAlgHom (Algebra.ofId k (sweepFibreRing k d r hp hq))) (X s')
        = MvPolynomial.map (algebraMap k (sweepFibreRing k d r hp hq)) (X s') from rfl,
      MvPolynomial.map_X]
  obtain (⟨i, j⟩ | ⟨i, b⟩ | ⟨a, j⟩) := s
  · -- Δ-block: `chartPsiAeval (multPoly (castLE i)(castLE j)) = (schurΔLoc.map schurToGfib) i j`.
    rw [chartPhiVarSub, chartPsiLoc_chartPhiVarSub_aux]
    have := submatrix_map_chartPsiAeval_eq_schurΔ (k := k) d r hp hq
    have h2 := congrFun (congrFun this i) j
    rw [Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply] at h2
    rw [h2, Matrix.map_apply, schurΔLoc, Matrix.map_apply, schurΔ, Matrix.of_apply, hgfib]
  · -- B12-block.
    rw [chartPhiVarSub, chartPsiLoc_chartPhiVarSub_aux]
    have := submatrix_map_chartPsiAeval_eq_schurB12 (k := k) d r hp hq
    have h2 := congrFun (congrFun this i) b
    rw [Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply] at h2
    rw [h2, Matrix.map_apply, schurB12Loc, Matrix.of_apply, hgfib]
  · -- B21-block.
    rw [chartPhiVarSub, chartPsiLoc_chartPhiVarSub_aux]
    have := submatrix_map_chartPsiAeval_eq_schurB21 (k := k) d r hp hq
    have h2 := congrFun (congrFun this a) j
    rw [Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply] at h2
    rw [h2, Matrix.map_apply, schurB21Loc, Matrix.of_apply, hgfib]

/-! ## The O(F)-coefficient leg of the h1 round-trip (mirror of the Φ∘Ψ legs) -/

variable (k) in
/-- `chartPsiLoc` agrees with `chartPsiQuot` on `O(Σ)`-classes. Mirror of `chartPhiLoc_algebraMap`. -/
theorem chartPsiLoc_algebraMap [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (a : sweepSigmaRing k d r) :
    chartPsiLoc k d r hp hq
        (algebraMap _ (Localization.Away (chartDsig k d r hp hq)) a)
      = chartPsiQuot k d r hp hq a := by
  rw [chartPsiLoc, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

variable (k) in
/-- **The coefficient leg `chartPsiLoc ∘ schurToDsig = schurToGfib`.** Both `SchurLoc →ₐ[k] Away gF`;
on `MvPolynomial SchurVar k`-classes, `schurToDsig (algebraMap (X s)) = chartPhiVarSub s`,
`chartPsiLoc` of which is `algebraMap (X s)` (`chartPsiLoc_chartPhiVarSub`); and `schurToGfib
(algebraMap (X s)) = algebraMap (X s)`. -/
theorem chartPsiLoc_comp_schurToDsig [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    (chartPsiLoc k d r hp hq).comp (schurToDsig k d r hp hq)
      = schurToGfib k d r hp hq := by
  apply Localization.algHom_ext (Submonoid.powers (detSchurS (d 0) (d (Fin.last (N + 1))) r))
  apply MvPolynomial.algHom_ext
  intro s
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  show chartPsiLoc k d r hp hq (schurToDsig k d r hp hq
      (algebraMap _ (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) (X s)))
    = schurToGfib k d r hp hq
      (algebraMap _ (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) (X s))
  rw [schurToDsig_algebraMap, chartPhiSchurAeval, aeval_X, chartPsiLoc_chartPhiVarSub,
    schurToGfib_algebraMap,
    show (MvPolynomial.mapAlgHom (Algebra.ofId k (sweepFibreRing k d r hp hq))) (X s)
      = MvPolynomial.map (algebraMap k (sweepFibreRing k d r hp hq)) (X s) from rfl,
    MvPolynomial.map_X]

variable (k) in
/-- **The variable leg `chartPsiLoc (sigmaCoordT x) = chartPsiSub x`.** Mirror of
`chartPhiLoc_fibCoordT`. -/
theorem chartPsiLoc_sigmaCoordT [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (x : RepCoord d) :
    chartPsiLoc k d r hp hq (sigmaCoordT k d r hp hq x) = chartPsiSub k d r hp hq x := by
  rw [sigmaCoordT, chartPsiLoc_algebraMap, chartPsiQuot, Ideal.Quotient.liftₐ_apply,
    Ideal.Quotient.lift_mk, RingHom.coe_coe, chartPsiAeval, aeval_X]

variable (k) in
/-- **The composite `chartPsiLoc ∘ chartPhiTower = aevalTower schurToGfib chartPsiSub`.** Mirror of
`chartPhiLoc_comp_chartPsiTower`. -/
theorem chartPsiLoc_comp_chartPhiTower [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    (chartPsiLoc k d r hp hq).comp (chartPhiTower k d r hp hq)
      = MvPolynomial.aevalTower (schurToGfib k d r hp hq) (chartPsiSub k d r hp hq) := by
  apply MvPolynomial.algHom_ext'
  · rw [AlgHom.comp_assoc]
    rw [show (chartPhiTower k d r hp hq).comp
          (IsScalarTower.toAlgHom k (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
            (MvPolynomial (RepCoord d) (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)))
        = schurToDsig k d r hp hq from by
      rw [chartPhiTower]; exact MvPolynomial.aevalTower_comp_toAlgHom _ _]
    rw [chartPsiLoc_comp_schurToDsig, MvPolynomial.aevalTower_comp_toAlgHom]
  · intro x
    rw [AlgHom.comp_apply, chartPhiTower, MvPolynomial.aevalTower_X, chartPsiLoc_sigmaCoordT,
      MvPolynomial.aevalTower_X]

variable (k) in
/-- **The h1 O(F)-coefficient per-generator identity** `chartPsiLoc (chartPhiFibSub x) = fibCoordT x`.
Collapses via the gauge group law at `eg * eg⁻¹ = 1` to `fibCoordT x`. -/
theorem chartPsiLoc_chartPhiFibSub [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (x : RepCoord d) :
    chartPsiLoc k d r hp hq (chartPhiFibSub k d r hp hq x) = fibCoordT k d r hp hq x := by
  rw [chartPhiFibSub,
    show chartPsiLoc k d r hp hq (chartPhiTower k d r hp hq
        (gaugeSub d (endpointGauge (k := k) d r hp hq) x))
      = (chartPsiLoc k d r hp hq).comp (chartPhiTower k d r hp hq)
          (gaugeSub d (endpointGauge (k := k) d r hp hq) x) from rfl,
    chartPsiLoc_comp_chartPhiTower]
  rw [show chartPsiSub k d r hp hq
        = (fun y ↦ MvPolynomial.aevalTower (schurToGfib k d r hp hq) (fibCoordT k d r hp hq)
            (gaugeSub d (endpointGauge (k := k) d r hp hq)⁻¹ y)) from by
      funext y; rw [chartPsiSub, chartPsiTower]]
  rw [aevalTower_gaugeSub_gaugeSub (schurToGfib k d r hp hq) d (fibCoordT k d r hp hq)
    (endpointGauge (k := k) d r hp hq)⁻¹ (endpointGauge (k := k) d r hp hq) x,
    mul_inv_cancel, gaugeSub_one, MvPolynomial.aevalTower_X]

variable (k) in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The h1 composite `chartPsiLoc ∘ chartPhiAeval = algebraMap P (Away gF)`** (as
`IsScalarTower.toAlgHom k P (Away gF)`). By `MvPolynomial.algHom_ext'`: the `O(F)`-coefficient leg
(`Ideal.Quotient.algHom_ext` + `MvPolynomial`-ext, discharged by `chartPsiLoc_chartPhiFibSub`) and
the `SchurVar` variable leg (`chartPsiLoc_chartPhiVarSub`). The heart of the h1 round-trip. -/
theorem chartPsiLoc_comp_chartPhiAeval [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    (chartPsiLoc k d r hp hq).comp (chartPhiAeval k d r hp hq)
      = IsScalarTower.toAlgHom k (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
            (sweepFibreRing k d r hp hq)) (Localization.Away (chartGfib k d r hp hq)) := by
  refine MvPolynomial.algHom_ext' (R := k)
    (A := sweepFibreRing k d r hp hq) (B := Localization.Away (chartGfib k d r hp hq))
    (σ := SchurVar (d 0) (d (Fin.last (N + 1))) r) ?_ (fun s ↦ ?_)
  · -- coefficient leg: lift `O(F)`-classes to `RepCoord` generators.
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro x
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', Ideal.Quotient.mkₐ_eq_mk]
    show chartPsiLoc k d r hp hq (chartPhiAeval k d r hp hq
        (C (Ideal.Quotient.mk (vanishingIdeal k (sweepFibre k d r hp hq)) (X x))))
      = algebraMap (sweepFibreRing k d r hp hq) (Localization.Away (chartGfib k d r hp hq))
          (Ideal.Quotient.mk (vanishingIdeal k (sweepFibre k d r hp hq)) (X x))
    rw [chartPhiAeval, MvPolynomial.aevalTower_C,
      show chartPhiCoeff k d r hp hq
          (Ideal.Quotient.mk (vanishingIdeal k (sweepFibre k d r hp hq)) (X x))
        = chartPhiFibSub k d r hp hq x from by
        rw [chartPhiCoeff, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk, RingHom.coe_coe,
          chartPhiFibAeval, aeval_X],
      chartPsiLoc_chartPhiFibSub, fibCoordT]
  · -- variable leg: `chartPsiLoc (chartPhiVarSub s) = algebraMap (X s)`.
    rw [AlgHom.comp_apply, chartPhiAeval, MvPolynomial.aevalTower_X, chartPsiLoc_chartPhiVarSub,
      IsScalarTower.coe_toAlgHom']

end DLNFibre.Core
