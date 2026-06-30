/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import DLNFibre.Core.RankNormalFormDim

/-!
# `Matrix` — Schur-complement coordinates on the pivot rank chart

Over a field `k` (and, for the conjugation normal form, an arbitrary `CommRing`), the **pivot rank
chart** of a block matrix `M = [[Δ, B12], [B21, B22]]` — where the top-left block `Δ` is invertible
— carries explicit Schur-complement coordinates. This file collects the matrix/Schur content of the
determinantal atlas, all of it general matrix/field facts (the DLN flavour, which ring the
coordinates sit in, lives in the application layer).

* **Block-rank additivity** `rank_fromBlocks_zero` (absent in Mathlib v4.29): over a field, a
  block-diagonal matrix `[[A, 0], [0, D]]` has `rank = A.rank + D.rank` (general index types — the
  `prodMap` conjugation of `mulVecLin`). The `Fin`-indexed sibling
  `rank_fromBlocks_zero_offdiag` lives in `DLNFibre.Core.RankNormalFormDim`.

* **The pivot Schur rank criterion.** With `Δ` invertible, the block matrix has rank exactly
  `card Δ` (the size of `Δ`) **iff** the bottom-right block is the Schur-forced value
  `B22 = B21 · Δ⁻¹ · B12`: `rank_fromBlocks_eq_card_iff_schur` (general index, `⅟Δ` form),
  `rank_fromBlocks_eq_card_iff_schur_inv` (`Δ⁻¹` form, under `IsUnit Δ.det`). The `Fin`-indexed
  ≤/= chart-membership iffs are `rank_le_iff_schur_eq` / `rank_eq_iff_schur_eq`, via the explicit
  block-rank value `rank_fromBlocks_invertible₁₁` (`rank = r + rank (B22 − B21 Δ⁻¹ B12)`).

* **The explicit chart parametrization.** `pivotRankChart`/`pivotRankChartEquiv`: the exact-rank-`r`
  block matrices with `Δ` invertible are in explicit bijection with
  `{Δ // IsUnit Δ.det} × Mat × Mat` — the three free blocks `(Δ, B12, B21)`, the fourth
  Schur-forced. The parametrizing affine space has `finrank = δ = r(p+q−r)`
  (`finrank_pivotRankChart_params` + `dim_params_eq_delta`).

* **The Schur-complement normal form** (over any `CommRing`): with `Δ` invertible and the Schur
  relation, the lower/upper unitriangular conjugation collapses `M` to `diag(I_r, 0)`
  (`schurComplement_normal_form`).

**Provenance.** Re-homed (namespace `Matrix`, mirroring `Mathlib.LinearAlgebra.Matrix.Rank` /
`Matrix.SchurComplement`) from `DLNFibre.Core.DeterminantalChart` (block-rank additivity, the pivot
Schur rank criterion, the chart parametrization), `DLNFibre.Core.SchurChartIff` (the `Fin`-indexed
chart-membership iffs), and `DLNFibre.Core.SchurGauge` (the `CommRing` normal form). Mathlib's Schur
*det* identities (`det_fromBlocks₁₁`/`₂₂`, `fromBlocks₁₁Invertible`) are reused, not re-proved.

**Connection to the rank strata** (`DLNFibre.Core.RingTheory.Determinantal.Strata`): a matrix in the
top-left pivot chart `minorChart` has the Schur normal form, and its rank is exactly `r` iff the
Schur complement vanishes (`rank_eq_iff_schur_eq`). `Strata.minorChart`/`rankEqLocus` are the
set-level chart/locus; the Schur iff here is the local coordinate read of membership.

**Dependency rule:** network-free `Core` — never import `DLNFibre.DLN`.
-/

namespace Matrix

open Module

universe u

variable {k : Type u} [Field k] {m l n o : Type u}

/-! ## A block-diagonal map is the `prodMap` of its diagonal blocks (after reindexing) -/

/-- Conjugating the block-diagonal matrix map `fromBlocks A 0 0 D` by the sum/product
arrow equivalences turns it into `A.mulVecLin.prodMap D.mulVecLin`. -/
theorem mulVecLin_fromBlocks_zero_conj
    [Fintype m] [Fintype n] [Fintype l] [Fintype o]
    (A : Matrix m n k) (D : Matrix l o k) :
    (LinearEquiv.sumArrowLequivProdArrow m l k k).toLinearMap.comp
        ((fromBlocks A (0 : Matrix m o k) (0 : Matrix l n k) D).mulVecLin.comp
          (LinearEquiv.sumArrowLequivProdArrow n o k k).symm.toLinearMap)
      = A.mulVecLin.prodMap D.mulVecLin := by
  ext x i <;>
  simp [Matrix.mulVecLin, fromBlocks_mulVec, LinearEquiv.sumArrowLequivProdArrow,
    Equiv.sumArrowEquivProdArrow, Function.comp]

/-! ## Block-diagonal rank additivity (general index types; missing in Mathlib v4.29) -/

/-- `S.prod T ≃ₗ S × T` — a `private` file-local helper for `rank_fromBlocks_zero` (general `Submodule`
infra, kept off this determinantal module's public surface; promote to a `Submodule` foundation file
if a second consumer appears). -/
private noncomputable def _root_.Submodule.prodLequiv (S : Submodule k (m → k)) (T : Submodule k (l → k)) :
    (S.prod T) ≃ₗ[k] (S × T) where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Block-diagonal rank additivity** (general index types). Over a field, the rank of a
block-diagonal matrix is the sum of the ranks of its diagonal blocks:
`rank (fromBlocks A 0 0 D) = rank A + rank D`. (No such lemma in Mathlib v4.29; the proof conjugates
`mulVecLin` to `A.mulVecLin.prodMap D.mulVecLin` and applies `LinearMap.range_prodMap` +
`Module.finrank_prod`. The `Fin`-indexed sibling is `Matrix.rank_fromBlocks_zero_offdiag`.) -/
theorem rank_fromBlocks_zero
    [Fintype m] [Fintype n] [Fintype l] [Fintype o]
    (A : Matrix m n k) (D : Matrix l o k) :
    (fromBlocks A (0 : Matrix m o k) (0 : Matrix l n k) D).rank = A.rank + D.rank := by
  set M := fromBlocks A (0 : Matrix m o k) (0 : Matrix l n k) D with hM
  set e := LinearEquiv.sumArrowLequivProdArrow m l k k with he
  set e' := LinearEquiv.sumArrowLequivProdArrow n o k k with he'
  -- conjugation: e ∘ M.mulVecLin ∘ e'.symm = prodMap
  have hconj : e.toLinearMap.comp (M.mulVecLin.comp e'.symm.toLinearMap)
      = A.mulVecLin.prodMap D.mulVecLin := mulVecLin_fromBlocks_zero_conj (k := k) A D
  -- rank M = finrank (range M.mulVecLin)
  have hMrank : M.rank = finrank k (LinearMap.range M.mulVecLin) := rfl
  -- range (prodMap) = e.map (range (M.mulVecLin ∘ e'.symm)) = e.map (range M.mulVecLin)
  have hpm : finrank k (LinearMap.range (A.mulVecLin.prodMap D.mulVecLin))
      = finrank k (LinearMap.range M.mulVecLin) := by
    rw [← hconj, LinearMap.range_comp]
    -- range (M.mulVecLin ∘ e'.symm) = range M.mulVecLin (e'.symm surjective)
    rw [LinearMap.range_comp_of_range_eq_top _
        (LinearMap.range_eq_top.mpr e'.symm.surjective)]
    -- finrank (e.map (range M.mulVecLin)) = finrank (range M.mulVecLin)
    exact e.finrank_map_eq _
  -- finrank (range prodMap) = finrank ((range A.mulVecLin) × (range D.mulVecLin))
  --   = rank A + rank D
  rw [hMrank, ← hpm, LinearMap.range_prodMap]
  rw [(Submodule.prodLequiv (LinearMap.range A.mulVecLin) (LinearMap.range D.mulVecLin)).finrank_eq,
    Module.finrank_prod]
  rfl

/-! ## `rank = 0 ↔ matrix = 0` over a field (general index)

The `Fin`-indexed public version is `Matrix.rank_eq_zero_iff` (in `DLNFibre.Core.RankNormalFormDim`,
imported above); this general-index form is a private helper for the Schur criterion below. -/

/-- Over a field, a matrix has rank `0` iff it is the zero matrix (general index type). -/
private theorem rank_eq_zero_iff_general [Fintype n] (A : Matrix m n k) :
    A.rank = 0 ↔ A = 0 := by
  classical
  constructor
  · intro h
    have hbot : LinearMap.range A.mulVecLin = ⊥ :=
      (Submodule.finrank_eq_zero (R := k) (M := (m → k))
        (S := LinearMap.range A.mulVecLin)).mp h
    rw [LinearMap.range_eq_bot] at hbot
    ext i j
    have hj := congrArg (fun f => f (Pi.single j 1) i) hbot
    simpa [Matrix.mulVecLin, Matrix.mulVec_single] using hj
  · rintro rfl; exact rank_zero

/-! ## The pivot-chart Schur rank criterion (general index) -/

/-- **The pivot-chart Schur rank criterion.** Over a field, with the top-left block `Δ`
invertible, the block matrix `[[Δ, B12], [B21, B22]]` has rank exactly `card m` (the size of
`Δ`) **iff** the bottom-right block is the Schur-forced value `B22 = B21 · Δ⁻¹ · B12`. -/
theorem rank_fromBlocks_eq_card_iff_schur
    [Fintype m] [Fintype l] [Fintype n]
    [DecidableEq m] [DecidableEq l] [DecidableEq n]
    (Δ : Matrix m m k) (B12 : Matrix m n k) (B21 : Matrix l m k) (B22 : Matrix l n k)
    [Invertible Δ] :
    (fromBlocks Δ B12 B21 B22).rank = Fintype.card m ↔ B22 = B21 * ⅟Δ * B12 := by
  classical
  set S := B22 - B21 * ⅟Δ * B12 with hS
  -- LDU factorization (Schur complement)
  have hldu : fromBlocks Δ B12 B21 B22
      = fromBlocks 1 0 (B21 * ⅟Δ) 1 * fromBlocks Δ 0 0 S *
          fromBlocks 1 (⅟Δ * B12) 0 1 :=
    fromBlocks_eq_of_invertible₁₁ Δ B12 B21 B22
  -- the two unipotent factors have det 1, hence are units
  have hLdet : (fromBlocks (1 : Matrix m m k) 0 (B21 * ⅟Δ) 1).det = 1 := by
    rw [det_fromBlocks_one₁₁]; simp
  have hUdet : (fromBlocks (1 : Matrix m m k) (⅟Δ * B12) 0 1).det = 1 := by
    rw [det_fromBlocks_one₂₂]; simp
  -- rank is preserved by the unipotent sandwich
  have hrankM : (fromBlocks Δ B12 B21 B22).rank = (fromBlocks Δ 0 0 S).rank := by
    rw [hldu, rank_mul_eq_left_of_isUnit_det _ _ (hUdet ▸ isUnit_one),
      rank_mul_eq_right_of_isUnit_det _ _ (hLdet ▸ isUnit_one)]
  -- block-diagonal rank additivity + rank Δ = card m
  have hΔrank : Δ.rank = Fintype.card m :=
    rank_of_isUnit Δ (isUnit_of_invertible Δ)
  rw [hrankM, rank_fromBlocks_zero, hΔrank]
  -- now: card m + rank S = card m ↔ B22 = B21 ⅟Δ B12
  rw [show (Fintype.card m + S.rank = Fintype.card m) ↔ S.rank = 0 by omega,
    rank_eq_zero_iff_general, hS, sub_eq_zero]

/-- **The Schur criterion in nonsingular-inverse form.** Same as `rank_fromBlocks_eq_card_iff_schur`
but stated with `Δ⁻¹` (the `Matrix.inv`) rather than `⅟Δ`, so it applies under an `IsUnit Δ.det`
hypothesis without first materializing an `Invertible Δ` instance. -/
theorem rank_fromBlocks_eq_card_iff_schur_inv
    [Fintype m] [Fintype l] [Fintype n] [DecidableEq m] [DecidableEq l] [DecidableEq n]
    (Δ : Matrix m m k) (B12 : Matrix m n k) (B21 : Matrix l m k) (B22 : Matrix l n k)
    (hΔ : IsUnit Δ.det) :
    (fromBlocks Δ B12 B21 B22).rank = Fintype.card m ↔ B22 = B21 * Δ⁻¹ * B12 := by
  letI : Invertible Δ := Δ.invertibleOfIsUnitDet hΔ
  rw [rank_fromBlocks_eq_card_iff_schur Δ B12 B21 B22, invOf_eq_nonsing_inv]

/-! ## The pivot chart and its explicit parametrization (general index) -/

variable (k m l n) in
/-- The **pivot rank chart**: the exact-rank-`card m` block matrices whose top-left block `Δ` is
invertible (det a unit). Det-open, matching the localization element `det Δ` of the later
localized Schur `AlgEquiv`. The set-level pivot chart and rank locus are `Matrix.minorChart` /
`Matrix.rankEqLocus` (`DLNFibre.Core.RingTheory.Determinantal.Strata`). -/
def pivotRankChart [Fintype m] [Fintype n] [DecidableEq m] :
    Set (Matrix (m ⊕ l) (m ⊕ n) k) :=
  {M | M.rank = Fintype.card m ∧ IsUnit M.toBlocks₁₁.det}

/-- **The explicit chart parametrization.** On the pivot chart, an exact-rank-`r` block matrix is
determined by its three free blocks `(Δ, B12, B21)` with `Δ` invertible: the bottom-right block is
the Schur-forced `B21·Δ⁻¹·B12`. So the chart is in explicit bijection with
`GL_r × Mat_{r×(q−r)} × Mat_{(p−r)×r}` — i.e.
`{Δ // IsUnit Δ.det} × Matrix m n k × Matrix l m k`. -/
noncomputable def pivotRankChartEquiv
    [Fintype m] [Fintype l] [Fintype n] [DecidableEq m] [DecidableEq l] [DecidableEq n] :
    {M // M ∈ pivotRankChart k m l n} ≃
      {Δ : Matrix m m k // IsUnit Δ.det} × Matrix m n k × Matrix l m k where
  toFun M := (⟨M.1.toBlocks₁₁, M.2.2⟩, M.1.toBlocks₁₂, M.1.toBlocks₂₁)
  invFun p :=
    ⟨fromBlocks p.1.1 p.2.1 p.2.2 (p.2.2 * p.1.1⁻¹ * p.2.1), by
      refine ⟨?_, ?_⟩
      · rw [rank_fromBlocks_eq_card_iff_schur_inv _ _ _ _ p.1.2]
      · rw [toBlocks_fromBlocks₁₁]; exact p.1.2⟩
  left_inv := by
    rintro ⟨M, hrank, hunit⟩
    -- M = fromBlocks of its four blocks, and the (2,2) block is Schur-forced by hrank.
    have hb22 : M.toBlocks₂₂ = M.toBlocks₂₁ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂ := by
      have := (rank_fromBlocks_eq_card_iff_schur_inv
        M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ hunit).mp
      rw [fromBlocks_toBlocks] at this
      exact this hrank
    apply Subtype.ext
    simp only
    rw [← hb22, fromBlocks_toBlocks]
  right_inv := by
    rintro ⟨⟨Δ, hΔ⟩, B12, B21⟩
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁]

/-! ## Dimension cross-check — the parametrizing space has `finrank = δ`

The parametrization `pivotRankChartEquiv` identifies the chart with
`{Δ // IsUnit Δ.det} × Matrix m n k × Matrix l m k`. The ambient affine space of the parameters
`Matrix m m k × Matrix m n k × Matrix l m k` has `k`-dimension
`r² + r(q−r) + r(p−r) = r(p+q−r) = δ` (with `r = card m`, `q = card n + r`, `p = card l + r`). The
`{Δ // IsUnit Δ.det}` factor is Zariski-open in `Matrix m m k`, so it has the same variety
dimension `r²` as the full block — hence the chart's variety dimension is `δ`. We record here the
*parameter-space* dimension identity (the AG step "open subset has the dimension of its ambient
space" is the variety-dimension content, deferred to the AG engine). -/

/-- **The parameter-space dimension is `δ`.** The `k`-dimension of the affine parameter space
`Matrix m m k × Matrix m n k × Matrix l m k` of `pivotRankChartEquiv` is
`(card m)² + (card m)(card n) + (card l)(card m)`, the three free-block coordinate counts whose sum
is `δ = r(p+q−r)` with `r = card m`, `p = card l + r`, `q = card n + r`. -/
theorem finrank_pivotRankChart_params [Fintype m] [Fintype n] [Fintype l] :
    finrank k (Matrix m m k × Matrix m n k × Matrix l m k)
      = Fintype.card m * Fintype.card m + Fintype.card m * Fintype.card n
        + Fintype.card l * Fintype.card m := by
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_matrix, Module.finrank_matrix,
    Module.finrank_matrix, Module.finrank_self, mul_one, mul_one, mul_one, ← add_assoc]

/-- **`δ` matches `r(p+q−r)`.** The three free-block coordinate counts sum to the determinantal
stratum dimension `r·(p+q−r)`, with `r = card m`, `p = card l + r`, `q = card n + r`. (Pure
arithmetic; ties `finrank_pivotRankChart_params` to the thermometer value `δ`.) -/
theorem dim_params_eq_delta (r p q : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    r * r + r * (q - r) + (p - r) * r = r * (p + q - r) := by
  obtain ⟨a, rfl⟩ := Nat.le.dest hp
  obtain ⟨b, rfl⟩ := Nat.le.dest hq
  have h1 : r + b - r = b := by omega
  have h2 : r + a - r = a := by omega
  have h3 : r + a + (r + b) - r = r + a + b := by omega
  rw [h1, h2, h3]; ring

/-! ## The `Fin`-indexed chart-membership iffs (≤ / = forms)

The exact-rank Schur criterion specialised to `Fin`-indexed blocks, stated with the rank value `r`
directly (rather than `Fintype.card (Fin r)`), via the explicit block-rank value
`rank_fromBlocks_invertible₁₁`. These are the chart-membership iffs for `Strata.minorChart`: a block
matrix lies in the rank-`≤ r` (resp. rank-`= r`) locus on the pivot chart iff its Schur complement
vanishes. -/

variable {K : Type*} [Field K] {r s t : ℕ}

/-- **Block-rank via the Schur complement.** For `Δ` invertible (`r×r`), the rank of the block
matrix `[[Δ, B12], [B21, B22]]` is `r + rank (B22 − B21 Δ⁻¹ B12)`: the LDU factorization conjugates
`M` to `diag(Δ, Schur)` by unitriangular units, and the block-diagonal rank adds. -/
theorem rank_fromBlocks_invertible₁₁
    (Δ : Matrix (Fin r) (Fin r) K) (B12 : Matrix (Fin r) (Fin t) K)
    (B21 : Matrix (Fin s) (Fin r) K) (B22 : Matrix (Fin s) (Fin t) K) (hΔ : IsUnit Δ.det) :
    (Matrix.fromBlocks Δ B12 B21 B22).rank = r + (B22 - B21 * Δ⁻¹ * B12).rank := by
  -- Promote `IsUnit Δ.det` to an `Invertible Δ` instance for the LDU lemma.
  have invΔ : Invertible Δ := Δ.invertibleOfIsUnitDet hΔ
  -- The LDU factorization `M = L · diag(Δ, Schur) · U`.
  have hLDU := Matrix.fromBlocks_eq_of_invertible₁₁ Δ B12 B21 B22
  -- The lower-unitriangular `L` and upper-unitriangular `U` are units (det 1).
  have hLdet : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 (B21 * ⅟Δ) 1).det := by
    rw [Matrix.det_fromBlocks_zero₁₂]; simp
  have hUdet : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) K) (⅟Δ * B12) 0 1).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]; simp
  rw [hLDU, rank_mul_eq_left_of_isUnit_det _ _ hUdet,
    rank_mul_eq_right_of_isUnit_det _ _ hLdet,
    Matrix.rank_fromBlocks_zero_offdiag, rank_of_isUnit Δ ((Matrix.isUnit_iff_isUnit_det _).mpr hΔ),
    Fintype.card_fin]
  -- `⅟Δ = Δ⁻¹` (the canonical inverse from `IsUnit`).
  congr 1
  rw [invOf_eq_nonsing_inv]

/-- **The chart-membership iff (≤ form).** On the chart `detΔ ≠ 0`, `rank [[Δ,B12],[B21,B22]] ≤ r`
iff the Schur relation `B22 = B21 Δ⁻¹ B12` holds. -/
theorem rank_le_iff_schur_eq
    (Δ : Matrix (Fin r) (Fin r) K) (B12 : Matrix (Fin r) (Fin t) K)
    (B21 : Matrix (Fin s) (Fin r) K) (B22 : Matrix (Fin s) (Fin t) K) (hΔ : IsUnit Δ.det) :
    (Matrix.fromBlocks Δ B12 B21 B22).rank ≤ r ↔ B22 = B21 * Δ⁻¹ * B12 := by
  rw [rank_fromBlocks_invertible₁₁ Δ B12 B21 B22 hΔ]
  constructor
  · intro h
    have hz : (B22 - B21 * Δ⁻¹ * B12).rank = 0 := by omega
    rw [Matrix.rank_eq_zero_iff] at hz
    exact sub_eq_zero.mp hz
  · intro h
    rw [h, sub_self, (Matrix.rank_eq_zero_iff (0 : Matrix (Fin s) (Fin t) K)).mpr rfl]
    omega

/-- **The chart-membership iff (= form).** On the chart `detΔ ≠ 0`, `rank [[Δ,B12],[B21,B22]] = r`
iff the Schur relation `B22 = B21 Δ⁻¹ B12` holds. (The `r` lower bound is automatic from the
invertible pivot block.) -/
theorem rank_eq_iff_schur_eq
    (Δ : Matrix (Fin r) (Fin r) K) (B12 : Matrix (Fin r) (Fin t) K)
    (B21 : Matrix (Fin s) (Fin r) K) (B22 : Matrix (Fin s) (Fin t) K) (hΔ : IsUnit Δ.det) :
    (Matrix.fromBlocks Δ B12 B21 B22).rank = r ↔ B22 = B21 * Δ⁻¹ * B12 := by
  rw [rank_fromBlocks_invertible₁₁ Δ B12 B21 B22 hΔ]
  constructor
  · intro h
    have hz : (B22 - B21 * Δ⁻¹ * B12).rank = 0 := by omega
    rw [Matrix.rank_eq_zero_iff] at hz
    exact sub_eq_zero.mp hz
  · intro h
    rw [h, sub_self, (Matrix.rank_eq_zero_iff (0 : Matrix (Fin s) (Fin t) K)).mpr rfl, add_zero]

/-! ## The Schur-complement normal-form identity (over any `CommRing`)

The pivot-cell factorization, abstractly: for a block matrix `M = [[Δ, B12], [B21, B22]]` over a
commutative ring with `Δ` invertible and `B22 = B21 Δ⁻¹ B12` (the rank-`r` / fibre condition),
`L⁻¹ · M · H⁻¹ = diag(I_r, 0)`, where `L = [[I,0],[B21 Δ⁻¹,I]]`, `H = [[Δ,B12],[0,I]]` (so
`L⁻¹ = [[I,0],[−B21 Δ⁻¹,I]]`, `H⁻¹ = [[Δ⁻¹,−Δ⁻¹ B12],[0,I]]`). The matrix heart of the chart
normalization; network-free, over any `CommRing`. -/

/-- **Schur-complement normal form** (block form). With `Δ` invertible and the Schur relation
`B22 = B21 Δ⁻¹ B12`, the lower/upper unitriangular conjugation collapses `M` to `diag(I_r, 0)`. -/
theorem schurComplement_normal_form {R : Type*} [CommRing R] {r s t : ℕ}
    (Δ : Matrix (Fin r) (Fin r) R) (B12 : Matrix (Fin r) (Fin t) R)
    (B21 : Matrix (Fin s) (Fin r) R) (hΔ : IsUnit Δ.det) :
    (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) R) (0 : Matrix (Fin r) (Fin s) R)
        (-(B21 * Δ⁻¹)) (1 : Matrix (Fin s) (Fin s) R))
      * (Matrix.fromBlocks Δ B12 B21 (B21 * Δ⁻¹ * B12))
      * (Matrix.fromBlocks Δ⁻¹ (-(Δ⁻¹ * B12)) (0 : Matrix (Fin t) (Fin r) R)
          (1 : Matrix (Fin t) (Fin t) R))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) R) 0 0 0 := by
  have hinv : Δ * Δ⁻¹ = 1 := Matrix.mul_nonsing_inv Δ hΔ
  have hinv' : Δ⁻¹ * Δ = 1 := Matrix.nonsing_inv_mul Δ hΔ
  have c1 : B21 * Δ⁻¹ * Δ = B21 := by rw [Matrix.mul_assoc, hinv', Matrix.mul_one]
  have c2 : Δ * (Δ⁻¹ * B12) = B12 := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj.mpr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.mul_zero, hinv]
  · simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.mul_one, Matrix.mul_neg, c2,
      neg_add_cancel]
  · rw [Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.neg_mul, c1, Matrix.add_mul,
      Matrix.neg_mul, neg_add_cancel]
  · rw [Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul, c1, Matrix.one_mul, Matrix.add_mul,
      Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc B21 Δ⁻¹ B12]
    abel

/-! ## Non-vacuity witnesses -/

/-- **Witness.** With `m = l = n = Fin 1` (the `(2,2,2)` anchor at `r = 1`), the block matrix
`[[1, 0], [0, 0]]` (a `2×2` rank-`1` matrix with invertible top-left scalar `Δ = [1]`) lies in the
pivot chart, and its Schur criterion holds: its `(2,2)` entry is the forced value. -/
example :
    (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) (0 : Matrix (Fin 1) (Fin 1) ℚ)
        (0 : Matrix (Fin 1) (Fin 1) ℚ) (0 : Matrix (Fin 1) (Fin 1) ℚ)).rank
        = Fintype.card (Fin 1) ↔
      (0 : Matrix (Fin 1) (Fin 1) ℚ) = 0 * (1 : Matrix (Fin 1) (Fin 1) ℚ)⁻¹ * 0 := by
  rw [rank_fromBlocks_eq_card_iff_schur_inv (1 : Matrix (Fin 1) (Fin 1) ℚ)
    (0 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 (by simp)]

end Matrix

/-- Non-vacuity witness: `[[1,0],[0,0]]` (i.e. `Δ = [1]`, `B12 = B21 = [0]`, `B22 = [0]`) over `ℚ`
has rank `≤ 1`, and indeed satisfies the Schur relation `0 = 0`. -/
example :
    (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) (0 : Matrix (Fin 1) (Fin 1) ℚ)
        (0 : Matrix (Fin 1) (Fin 1) ℚ) (0 : Matrix (Fin 1) (Fin 1) ℚ)).rank ≤ 1 :=
  (Matrix.rank_le_iff_schur_eq 1 0 0 0 (by simp)).mpr (by simp)

/-- Non-vacuity witness: the `CommRing` Schur normal form at `r = s = t = 1` over `ℚ`, with
`Δ = [1]`, `B12 = B21 = [0]`: `I · diag(1,0) · I = diag(1,0)`. -/
example :
    (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) (0 : Matrix (Fin 1) (Fin 1) ℚ)
        (-((0 : Matrix (Fin 1) (Fin 1) ℚ) * (1 : Matrix (Fin 1) (Fin 1) ℚ)⁻¹))
        (1 : Matrix (Fin 1) (Fin 1) ℚ))
      * (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) (0 : Matrix (Fin 1) (Fin 1) ℚ) 0
          ((0 : Matrix (Fin 1) (Fin 1) ℚ) * (1 : Matrix (Fin 1) (Fin 1) ℚ)⁻¹ * 0))
      * (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ)⁻¹
          (-((1 : Matrix (Fin 1) (Fin 1) ℚ)⁻¹ * 0)) (0 : Matrix (Fin 1) (Fin 1) ℚ)
          (1 : Matrix (Fin 1) (Fin 1) ℚ))
      = Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 0 :=
  Matrix.schurComplement_normal_form 1 0 0 (by simp)
