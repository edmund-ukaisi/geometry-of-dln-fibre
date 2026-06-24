/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.DeterminantalBasePresentation

/-!
# `DLNFibre.Core.SchurGauge` — the Schur-valued pivot block as a `SchurLoc`-unit (route-(c) rung 2)

The first easier piece of the route-(c) pivot-chart trivialization (thread 31 rung 2): the pivot
block `schurΔ` (the top-left `r×r` submatrix of the generic base matrix, in the `SchurVar`
coordinates), mapped into the localization `SchurLoc = Localization.Away detSchurS`, is an
**invertible matrix**. Its determinant is `detSchurS`, the very element inverted in `SchurLoc`. It
is the unit out of which the endpoint normalizing gauge `L`, `H` (Schur-complement blocks) is built
— the `BaseChangeGroup` element over `SchurLoc` that drives the chart `AlgEquiv`.

This module stays strictly at the `varietyDim`/radical level (the `VarietyDimRadical` shield); it
never re-enters the strict-ideal / reducedness level that walled R2-3b-4.

## Main results
- `schurΔLoc` — the pivot block over `SchurLoc`.
- `det_schurΔLoc` — its determinant is `detSchurS` pushed into `SchurLoc`.
- `isUnit_det_schurΔLoc` — that determinant is a unit (inverted in `SchurLoc`).
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k]

/-- The pivot block `schurΔ` mapped into the localization
`SchurLoc = Localization.Away detSchurS`. -/
noncomputable def schurΔLoc (q p r : ℕ) :
    Matrix (Fin r) (Fin r) (SchurLoc (k := k) q p r) :=
  (schurΔ (k := k) q p r).map (algebraMap _ _)

/-- The determinant of `schurΔLoc` is `detSchurS`, pushed into `SchurLoc`. (`detSchurS` is by
definition `det schurΔ`, and `det` commutes with the algebra map.) -/
theorem det_schurΔLoc (q p r : ℕ) :
    (schurΔLoc (k := k) q p r).det
      = algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r)
          (detSchurS (k := k) q p r) :=
  (RingHom.map_det (algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r))
    (schurΔ (k := k) q p r)).symm

/-- **The pivot block is invertible over `SchurLoc`.** Its determinant `detSchurS` is the element
inverted in `SchurLoc = Localization.Away detSchurS`, hence a unit. -/
theorem isUnit_det_schurΔLoc (q p r : ℕ) : IsUnit (schurΔLoc (k := k) q p r).det := by
  rw [det_schurΔLoc]
  exact IsLocalization.Away.algebraMap_isUnit (detSchurS q p r)

/-- The pivot block is invertible as a matrix over `SchurLoc` (det is a unit, in a commutative
ring). -/
theorem isUnit_schurΔLoc (q p r : ℕ) : IsUnit (schurΔLoc (k := k) q p r) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_det_schurΔLoc (k := k) q p r)

/-! ## The Schur off-diagonal blocks `B12`, `B21` over `SchurLoc`

The `SchurVar` coordinate type is `(Fin r × Fin r) ⊕ ((Fin r × Fin (q−r)) ⊕ (Fin (p−r) × Fin r))`:
the pivot `Δ` is `Sum.inl`, the `B12` block is `Sum.inr ∘ Sum.inl`, the `B21` block is
`Sum.inr ∘ Sum.inr`. We read each off-diagonal block directly off those coordinates, pushed into
`SchurLoc`. -/

/-- The `B12` block (`Fin r × Fin (q−r)`) over `SchurLoc`, from the `Sum.inr ∘ Sum.inl` coords. -/
noncomputable def schurB12Loc (q p r : ℕ) :
    Matrix (Fin r) (Fin (q - r)) (SchurLoc (k := k) q p r) :=
  Matrix.of fun i j ↦ algebraMap (MvPolynomial (SchurVar q p r) k) _
    (X (Sum.inr (Sum.inl (i, j))))

/-- The `B21` block (`Fin (p−r) × Fin r`) over `SchurLoc`, from the `Sum.inr ∘ Sum.inr` coords. -/
noncomputable def schurB21Loc (q p r : ℕ) :
    Matrix (Fin (p - r)) (Fin r) (SchurLoc (k := k) q p r) :=
  Matrix.of fun i j ↦ algebraMap (MvPolynomial (SchurVar q p r) k) _
    (X (Sum.inr (Sum.inr (i, j))))

/-! ## The endpoint normalizing units `L`, `H`

The pivot-cell factorization `M = L · E · H` (`M` the rank-`r` generic product over `SchurLoc`):
- `L` (`p × p`, the `d_N`-vertex unit): lower-unitriangular `[[I, 0], [B21 · Δ⁻¹, I]]`.
- `H` (`q × q`, the `d_0`-vertex unit): upper-triangular `[[Δ, B12], [0, I]]`.

Each is built block-wise over `Fin r ⊕ Fin (n−r)` (where `isUnit_fromBlocks_zero₁₂/₂₁` makes
invertibility immediate from the diagonal blocks), then reindexed to `Fin n` by the pivot split
`finSplit`. Both are units over `SchurLoc` — `Δ⁻¹` exists there (`isUnit_schurΔLoc`). -/

/-- The lower-unitriangular `L` block, `[[I, 0], [B21 · Δ⁻¹, I]]`, on `Fin r ⊕ Fin (p−r)`. -/
noncomputable def LblockSum (q p r : ℕ) :
    Matrix (Fin r ⊕ Fin (p - r)) (Fin r ⊕ Fin (p - r)) (SchurLoc (k := k) q p r) :=
  Matrix.fromBlocks 1 0 (schurB21Loc q p r * (schurΔLoc q p r)⁻¹) 1

/-- The upper-triangular `H` block, `[[Δ, B12], [0, I]]`, on `Fin r ⊕ Fin (q−r)`. -/
noncomputable def HblockSum (q p r : ℕ) :
    Matrix (Fin r ⊕ Fin (q - r)) (Fin r ⊕ Fin (q - r)) (SchurLoc (k := k) q p r) :=
  Matrix.fromBlocks (schurΔLoc q p r) (schurB12Loc q p r) 0 1

/-- `L` as a `p × p` matrix over `SchurLoc` (the `LblockSum` reindexed by the pivot split). -/
noncomputable def Lmat (q p r : ℕ) (hp : r ≤ p) :
    Matrix (Fin p) (Fin p) (SchurLoc (k := k) q p r) :=
  reindexAlgEquiv (SchurLoc (k := k) q p r) (SchurLoc (k := k) q p r) (finSplit hp).symm
    (LblockSum q p r)

/-- `H` as a `q × q` matrix over `SchurLoc` (the `HblockSum` reindexed by the pivot split). -/
noncomputable def Hmat (q p r : ℕ) (hq : r ≤ q) :
    Matrix (Fin q) (Fin q) (SchurLoc (k := k) q p r) :=
  reindexAlgEquiv (SchurLoc (k := k) q p r) (SchurLoc (k := k) q p r) (finSplit hq).symm
    (HblockSum q p r)

/-- `L` is a unit: lower-unitriangular (diagonal `I`, `I`), reindexing preserves units. -/
theorem isUnit_Lmat (q p r : ℕ) (hp : r ≤ p) : IsUnit (Lmat (k := k) q p r hp) := by
  apply IsUnit.map
  rw [LblockSum, isUnit_fromBlocks_zero₁₂]
  exact ⟨isUnit_one, isUnit_one⟩

/-- `H` is a unit: upper-triangular with diagonal `Δ` (a unit) and `I`. -/
theorem isUnit_Hmat (q p r : ℕ) (hq : r ≤ q) : IsUnit (Hmat (k := k) q p r hq) := by
  apply IsUnit.map
  rw [HblockSum, isUnit_fromBlocks_zero₂₁]
  exact ⟨isUnit_schurΔLoc q p r, isUnit_one⟩

/-! ## The endpoint gauge as a `BaseChangeGroup` over `SchurLoc`

The pivot-cell factorization `M = L · E · H` is realized as a base-change datum acting on `Tuple d`
over `SchurLoc`: the source-vertex unit (`v = 0`, dimension `d 0 = q`) is `H`, the target-vertex
unit (`v = last N`, dimension `d (last N) = p`) is `L⁻¹`, and every interior vertex is `1` (those
units telescope away in `mult`). The dependent dimension `Fin (d v)` is aligned to `Fin q`/`Fin p`
by a `cast` along `v = 0` / `v = last N`. -/

/-- **The endpoint normalizing gauge** as a `BaseChangeGroup` over `SchurLoc`: `H` at the source
vertex, `L⁻¹` at the target vertex, `1` interior. -/
noncomputable def endpointGauge (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    BaseChangeGroup (k := SchurLoc (k := k) (d 0) (d (Fin.last N)) r) d :=
  fun v ↦
    if hv0 : v = 0 then
      cast (by rw [hv0]) (isUnit_Hmat (k := k) (d 0) (d (Fin.last N)) r hq).unit
    else if hvl : v = Fin.last N then
      cast (by rw [hvl]) (isUnit_Lmat (k := k) (d 0) (d (Fin.last N)) r hp).unit⁻¹
    else 1

end DLNFibre.Core

/-- Non-vacuity witness: at `(q,p,r) = (2,2,1)` over `ℚ`, the `1×1` pivot block over `SchurLoc` is
invertible (the existential is inhabited). -/
example : IsUnit (DLNFibre.Core.schurΔLoc (k := ℚ) 2 2 1).det :=
  DLNFibre.Core.isUnit_det_schurΔLoc 2 2 1
