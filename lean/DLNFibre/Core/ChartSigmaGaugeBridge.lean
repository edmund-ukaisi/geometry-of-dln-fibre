/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartSigmaEvalRealize
import DLNFibre.Core.ChartRetraction

/-!
# `DLNFibre.Core.ChartSigmaGaugeBridge` — the evaluated-gauge = chart-gauge bridge (seam D)

The bridge underlying the Φ descent (thread 31, Codex's flagged break point): the evaluated
**forward** endpoint gauge at a chart point `A`'s Schur data equals the concrete `k`-valued chart
gauge of `mult d A`:

> `evalGauge (schurEval (schurOfMult A)) endpointGauge = chartGauge (mult d A)`.

This crosses three representations of the same pivot data — the `SchurLoc` gauge variables (`Lmat`,
`Hmat`), the evaluated matrix blocks of `mult d A`, and the concrete `Lmatk`/`Hmatk` used by
`chartGauge`. Once it holds, the LANDED `chartGauge_mem_fibre` gives the geometric realization
`baseChange (evalGauge …) A ∈ fibre (normalForm)` the Φ descent rides.

## Main results
- `map_nonsing_inv_of_isUnit` — a ring hom commutes with the nonsingular inverse (both dets units).
- `evalGauge_endpointGauge_eq_chartGauge` — the bridge.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

/-- **A ring hom commutes with the nonsingular inverse.** For `f : R →+* S` and a square matrix `M`
with `M.det` and `(M.map f).det` both units, `(M⁻¹).map f = (M.map f)⁻¹`: the `f`-image of `M⁻¹` is a
(two-sided) inverse of `M.map f` (`f` commutes with the matrix product, `Matrix.map_mul`), and the
nonsingular inverse is unique. -/
theorem map_nonsing_inv_of_isUnit {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (M : Matrix (Fin n) (Fin n) R)
    (hM : IsUnit M.det) (hfM : IsUnit (M.map f).det) :
    (M⁻¹).map f = (M.map f)⁻¹ := by
  -- `(M.map f) * ((M⁻¹).map f) = (M * M⁻¹).map f = (1).map f = 1`, so the `f`-image of `M⁻¹` is the
  -- (right) inverse of `M.map f` — and the nonsingular inverse is unique.
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, Matrix.mul_nonsing_inv M hM,
    RingHom.mapMatrix_apply, Matrix.map_one _ (map_zero f) (map_one f)]

variable {k : Type u} [Field k] {N : ℕ}

/-- The chart-point Schur evaluation maps the localized pivot block `schurΔLoc` to the concrete pivot
block `chartΔ (mult d A)`: entrywise, `schurEval (schurOfMult A) (X (Sum.inl (i, j))) =
(mult d A) (castLE i) (castLE j)`. -/
theorem map_schurEval_schurΔLoc (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (A : Tuple (k := k) d)
    (hs : eval (schurOfMult k d r hp hq A) (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0) :
    (schurΔLoc (k := k) (d 0) (d (Fin.last (N + 1))) r).map
        (schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs
          : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* k)
      = chartΔ (mult d A) hp hq := by
  funext i j
  rw [Matrix.map_apply, schurΔLoc, Matrix.map_apply, schurΔ, Matrix.of_apply,
    show ((schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs
          : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* k))
        (algebraMap (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) k)
          (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) (X (Sum.inl (i, j))))
      = schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs
          (algebraMap (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) k)
            (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) (X (Sum.inl (i, j)))) from rfl,
    schurEval_algebraMap, aeval_X, schurOfMult_inl, chartΔ, Matrix.submatrix_apply]

/-- The chart-point Schur evaluation maps the localized `B12` block `schurB12Loc` to the `B12` block
of `mult d A` (in the pivot split, `chartBlocks (mult d A)`'s `toBlocks₁₂`): entrywise,
`schurEval (schurOfMult A) (X (Sum.inr (Sum.inl (i, b)))) = (mult d A) (castLE i) (natAdd-cast b)`. -/
theorem map_schurEval_schurB12Loc (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (A : Tuple (k := k) d)
    (hs : eval (schurOfMult k d r hp hq A) (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0) :
    (schurB12Loc (k := k) (d 0) (d (Fin.last (N + 1))) r).map
        (schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs
          : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* k)
      = (chartBlocks (mult d A) hp hq).toBlocks₁₂ := by
  funext i b
  rw [Matrix.map_apply, schurB12Loc, Matrix.of_apply,
    show ((schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs
          : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* k))
        (algebraMap (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) k) _
          (X (Sum.inr (Sum.inl (i, b)))))
      = schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs
          (algebraMap (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) k) _
            (X (Sum.inr (Sum.inl (i, b))))) from rfl,
    schurEval_algebraMap, aeval_X]
  rw [Matrix.toBlocks₁₂, Matrix.of_apply, chartBlocks, Matrix.submatrix_apply]
  rfl

/-- The chart-point Schur evaluation maps the localized `B21` block `schurB21Loc` to the `B21` block
of `mult d A` (`chartBlocks (mult d A)`'s `toBlocks₂₁`). -/
theorem map_schurEval_schurB21Loc (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (A : Tuple (k := k) d)
    (hs : eval (schurOfMult k d r hp hq A) (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0) :
    (schurB21Loc (k := k) (d 0) (d (Fin.last (N + 1))) r).map
        (schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs
          : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* k)
      = (chartBlocks (mult d A) hp hq).toBlocks₂₁ := by
  funext a j
  rw [Matrix.map_apply, schurB21Loc, Matrix.of_apply,
    show ((schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs
          : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* k))
        (algebraMap (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) k) _
          (X (Sum.inr (Sum.inr (a, j)))))
      = schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs
          (algebraMap (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) k) _
            (X (Sum.inr (Sum.inr (a, j))))) from rfl,
    schurEval_algebraMap, aeval_X]
  rw [Matrix.toBlocks₂₁, Matrix.of_apply, chartBlocks, Matrix.submatrix_apply]
  rfl

/-- The pivot block of `mult d A` is invertible when the Schur determinant is nonzero at `A`'s data:
`eval (schurOfMult A) detSchurS = det (chartΔ (mult A))` (`eval_schurOfMult_detSchurS`), and a nonzero
field element is a unit. -/
theorem isUnit_det_chartΔ_mult (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (A : Tuple (k := k) d)
    (hs : eval (schurOfMult k d r hp hq A) (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0) :
    IsUnit (chartΔ (mult d A) hp hq).det := by
  rw [← eval_schurOfMult_detSchurS]
  exact isUnit_iff_ne_zero.mpr hs

/-- The chart-point Schur evaluation maps the localized lower-unitriangular gauge block `LblockSum`
to the concrete one of `mult d A` (`fromBlocks 1 0 (B21 · Δ⁻¹) 1`). The off-diagonal block uses
`map_nonsing_inv_of_isUnit` to commute `schurEval` past `schurΔLoc⁻¹`. -/
theorem map_schurEval_LblockSum (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (A : Tuple (k := k) d)
    (hs : eval (schurOfMult k d r hp hq A) (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0) :
    (LblockSum (k := k) (d 0) (d (Fin.last (N + 1))) r).map
        (schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs
          : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* k)
      = Matrix.fromBlocks 1 0
          ((chartBlocks (mult d A) hp hq).toBlocks₂₁ * (chartΔ (mult d A) hp hq)⁻¹) 1 := by
  set g := (schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs
    : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* k) with hg
  -- the off-diagonal block: `(schurB21Loc * schurΔLoc⁻¹).map g = (B21) * (chartΔ)⁻¹`.
  have hΔmap : (schurΔLoc (k := k) (d 0) (d (Fin.last (N + 1))) r).map g = chartΔ (mult d A) hp hq :=
    map_schurEval_schurΔLoc d r hp hq A hs
  have hfΔ : IsUnit ((schurΔLoc (k := k) (d 0) (d (Fin.last (N + 1))) r).map g).det := by
    rw [hΔmap]; exact isUnit_det_chartΔ_mult d r hp hq A hs
  have hoff : (schurB21Loc (k := k) (d 0) (d (Fin.last (N + 1))) r
        * (schurΔLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)⁻¹).map g
      = (chartBlocks (mult d A) hp hq).toBlocks₂₁ * (chartΔ (mult d A) hp hq)⁻¹ := by
    rw [Matrix.map_mul, map_schurEval_schurB21Loc,
      map_nonsing_inv_of_isUnit g _ (isUnit_det_schurΔLoc _ _ _) hfΔ, hΔmap]
  rw [LblockSum, Matrix.fromBlocks_map, Matrix.map_one _ (map_zero g) (map_one g),
    Matrix.map_zero _ (map_zero g), Matrix.map_one _ (map_zero g) (map_one g), hoff]

/-- The chart-point Schur evaluation maps the localized upper-triangular gauge block `HblockSum`
to the concrete one of `mult d A` (`fromBlocks Δ B12 0 1`). -/
theorem map_schurEval_HblockSum (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (A : Tuple (k := k) d)
    (hs : eval (schurOfMult k d r hp hq A) (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0) :
    (HblockSum (k := k) (d 0) (d (Fin.last (N + 1))) r).map
        (schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs
          : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* k)
      = Matrix.fromBlocks (chartΔ (mult d A) hp hq) ((chartBlocks (mult d A) hp hq).toBlocks₁₂) 0 1 := by
  set g := (schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs
    : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* k) with hg
  rw [HblockSum, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero g),
    Matrix.map_one _ (map_zero g) (map_one g), map_schurEval_schurΔLoc, map_schurEval_schurB12Loc]

/-- The chart-point Schur evaluation maps the localized `p×p` gauge unit `Lmat` to the concrete
`k`-valued chart gauge unit `Lmatk (mult d A)` (the reindexed `LblockSum` images coincide). -/
theorem map_schurEval_Lmat (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (A : Tuple (k := k) d)
    (hs : eval (schurOfMult k d r hp hq A) (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0) :
    (Lmat (k := k) (d 0) (d (Fin.last (N + 1))) r hp).map
        (schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs
          : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* k)
      = Lmatk (mult d A) hp hq := by
  rw [Lmat, reindexAlgEquiv_apply, reindex_apply, Equiv.symm_symm, ← Matrix.submatrix_map,
    map_schurEval_LblockSum, Lmatk]

/-- The chart-point Schur evaluation maps the localized `q×q` gauge unit `Hmat` to the concrete
`k`-valued chart gauge unit `Hmatk (mult d A)`. -/
theorem map_schurEval_Hmat (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (A : Tuple (k := k) d)
    (hs : eval (schurOfMult k d r hp hq A) (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0) :
    (Hmat (k := k) (d 0) (d (Fin.last (N + 1))) r hq).map
        (schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs
          : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* k)
      = Hmatk (mult d A) hp hq := by
  rw [Hmat, reindexAlgEquiv_apply, reindex_apply, Equiv.symm_symm, ← Matrix.submatrix_map,
    map_schurEval_HblockSum, Hmatk]

/-- **The bridge: the evaluated forward endpoint gauge is the concrete chart gauge.**
`evalGauge (schurEval (schurOfMult A)) endpointGauge = chartGauge (mult d A)`: at each vertex the
`SchurLoc` gauge unit, pushed through the chart-point evaluation `schurEval (schurOfMult A)`, equals
the `k`-valued chart gauge unit of `mult d A` — at the source vertex `0` it is `Hmat ↦ Hmatk`, at the
target vertex `last` it is `(Lmat)⁻¹ ↦ (Lmatk)⁻¹`, and interior vertices are `1` both sides. This
crosses the three representations of the pivot data (`SchurLoc` variables, evaluated blocks of
`mult d A`, concrete `Lmatk`/`Hmatk`); once it holds, `chartGauge_mem_fibre` gives the realization. -/
theorem evalGauge_endpointGauge_eq_chartGauge (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (A : Tuple (k := k) d)
    (hs : eval (schurOfMult k d r hp hq A) (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0)
    (hΔ : IsUnit (chartΔ (mult d A) hp hq).det) :
    evalGauge (d 0) (d (Fin.last (N + 1))) r
        (schurEval (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs)
        (endpointGauge (k := k) d r hp hq)
      = chartGauge d r hp hq (mult d A) hΔ := by
  funext v
  apply Units.ext
  by_cases hv0 : v = 0
  · -- source vertex: `Hmat ↦ Hmatk`.
    subst hv0
    rw [evalGauge_val, endpointGauge_zero, IsUnit.unit_spec, map_schurEval_Hmat,
      chartGauge_zero, IsUnit.unit_spec]
  · by_cases hvl : v = Fin.last (N + 1)
    · -- target vertex: `(Lmat)⁻¹ ↦ (Lmatk)⁻¹`.
      subst hvl
      set g := (schurEval (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs
        : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* k) with hg
      have hLd : IsUnit (Lmat (k := k) (d 0) (d (Fin.last (N + 1))) r hp).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_Lmat _ _ _ hp)
      have hfLd : IsUnit ((Lmat (k := k) (d 0) (d (Fin.last (N + 1))) r hp).map g).det := by
        rw [map_schurEval_Lmat]; exact (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_Lmatk _ hp hq)
      rw [evalGauge_val, endpointGauge_last, Matrix.coe_units_inv, IsUnit.unit_spec,
        map_nonsing_inv_of_isUnit g _ hLd hfLd, map_schurEval_Lmat,
        chartGauge_last, Matrix.coe_units_inv, IsUnit.unit_spec]
    · -- interior vertex: both gauges are `1`.
      rw [evalGauge, endpointGauge, dif_neg hv0, dif_neg hvl, map_one,
        chartGauge, dif_neg hv0, dif_neg hvl]

end DLNFibre.Core
