import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod

/-!
# `DLNFibre.Core.DeterminantalChart` — the pivot-chart Schur parametrization of `Mat^{rk=r}`

The first explicit handle on the exact-rank determinantal locus (G2-1, foundation of the
determinantal-presentation build). Over a field `k`, on the **pivot chart** where the top-left
block `Δ` of a block matrix `M = [[Δ, B12], [B21, B22]]` is invertible, `M` has rank exactly
`card Δ` (the size of `Δ`) **iff** the Schur complement vanishes:

> `(fromBlocks Δ B12 B21 B22).rank = Fintype.card m  ⟺  B22 = B21 · Δ⁻¹ · B12`.

This gives an explicit parametrization of the chart `Mat^{rk=r} ∩ U` by `GL_r × Mat × Mat`
(the bottom-right block `B22` is Schur-forced by the other three), of dimension `r(p+q−r) = δ`.

**The route.** LDU factorization (`fromBlocks_eq_of_invertible₁₁`) sandwiches `M` between two
unipotent (det = 1) block-triangular factors, which preserve rank
(`rank_mul_eq_left/right_of_isUnit_det`); the middle factor is block-diagonal
`fromBlocks Δ 0 0 S` with Schur complement `S = B22 − B21 Δ⁻¹ B12`. Block-diagonal rank is
additive (`rank_fromBlocks_zero` — built here, missing in Mathlib v4.29, via the `prodMap`
conjugation of `mulVecLin`), `rank Δ = card m` (Δ invertible), and `rank S = 0 ↔ S = 0`, so
`rank M = card m ↔ S = 0 ↔ B22 = B21 Δ⁻¹ B12`.

**Scope.** This is the *matrix/variety-level* presentation — the explicit handle for the later
localized Schur `AlgEquiv` (G2-3). It is NOT itself that `AlgEquiv`: the flatness route consumes a
localized coordinate-ring isomorphism, not a bijection of `k`-points.

**Witness:** `m = l = n = Fin 1` (the `(2,2,2), r=1` chart): `Δ` a `1×1` invertible scalar.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix Module

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

/-! ## Block-diagonal rank additivity (missing in Mathlib v4.29) -/

/-- The natural `LinearEquiv` from a product of submodules `S.prod T` to `S × T`. -/
noncomputable def Submodule.prodLequiv (S : Submodule k (m → k)) (T : Submodule k (l → k)) :
    (S.prod T) ≃ₗ[k] (S × T) where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Block-diagonal rank additivity.** Over a field, the rank of a block-diagonal matrix is the
sum of the ranks of its diagonal blocks: `rank (fromBlocks A 0 0 D) = rank A + rank D`. (No such
lemma in Mathlib v4.29; the proof conjugates `mulVecLin` to `A.mulVecLin.prodMap D.mulVecLin` and
applies `LinearMap.range_prodMap` + `Module.finrank_prod`.) -/
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

/-! ## `rank = 0 ↔ matrix = 0` over a field -/

/-- Over a field, a matrix has rank `0` iff it is the zero matrix. -/
theorem rank_eq_zero_iff [Fintype n] (A : Matrix m n k) :
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

/-! ## The pivot-chart Schur iff (the headline) -/

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
    rank_eq_zero_iff, hS, sub_eq_zero]

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

/-! ## The pivot chart and its explicit parametrization -/

variable (k m l n) in
/-- The **pivot rank chart**: the exact-rank-`card m` block matrices whose top-left block `Δ` is
invertible (det a unit). Det-open, matching the localization element `det Δ` of the later
localized Schur `AlgEquiv`. -/
def pivotRankChart [Fintype m] [Fintype n] [DecidableEq m] :
    Set (Matrix (m ⊕ l) (m ⊕ n) k) :=
  {M | M.rank = Fintype.card m ∧ IsUnit M.toBlocks₁₁.det}

/-- **The explicit chart parametrization (G2-1 headline).** On the pivot chart, an exact-rank-`r`
block matrix is determined by its three free blocks `(Δ, B12, B21)` with `Δ` invertible: the
bottom-right block is the Schur-forced `B21·Δ⁻¹·B12`. So the chart is in explicit bijection with
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
arithmetic; ties `finrank_pivotRankChart_params` to the thermometer value `δ` of
`DeterminantalStratumDim`.) -/
theorem dim_params_eq_delta (r p q : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    r * r + r * (q - r) + (p - r) * r = r * (p + q - r) := by
  obtain ⟨a, rfl⟩ := Nat.le.dest hp
  obtain ⟨b, rfl⟩ := Nat.le.dest hq
  have h1 : r + b - r = b := by omega
  have h2 : r + a - r = a := by omega
  have h3 : r + a + (r + b) - r = r + a + b := by omega
  rw [h1, h2, h3]; ring

/-! ## Non-vacuity witness — the `(2,2,2), r = 1` chart (`Δ` a `1×1` invertible scalar) -/

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

end DLNFibre.Core
