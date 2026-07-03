import DLNFibre.DLN.RLCT.Validate.D1HChartRank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# `D1JointDiffRankExact` — the EXACT joint-differential rank (b3)

The joint differential `Dg(v) : δ ↦ δ⁰·v¹ + v⁰·δ¹` at `L = 2` (`jointDiffL2 H v`) has rank EXACTLY

    finrank (range (jointDiffL2 H v)) = H0·rank(v¹) + rank(v⁰)·H2 − rank(v⁰)·rank(v¹)

**UNCONDITIONALLY** in the two layer ranks (no middle-stratum / `rank(prod v) = r` hypothesis;
the value only READS `rank(v⁰)`, `rank(v¹)`). The lower bound `nReg ≤ …` is banked
(`nReg_le_finrank_range_jointDiffL2`); this is the exact value — the DLN loss-entry Jacobian
rank formula, certified `rank = extraCountRect + nReg` at a middle stratum (d1gates, 0 fails).

## The decomposition (inclusion–exclusion at the matrix level)

`range (Dg v) = R ⊔ C` (coprod of the two single-argument ranges), where

  * `R = range (δ⁰ ↦ δ⁰·v¹)` — matrices with rows in `rowspace v¹`; `finrank R = H0·rank(v¹)`.
  * `C = range (δ¹ ↦ v⁰·δ¹)` — matrices with cols in `colspace v⁰`; `finrank C = rank(v⁰)·H2`.
  * `R ⊓ C` — rows in `rowspace v¹` AND cols in `colspace v⁰`; `finrank = rank(v⁰)·rank(v¹)`.

Then `Submodule.finrank_sup_add_finrank_inf_eq` (the inclusion–exclusion identity) plus honest ℕ
subtraction (`rank(v⁰)·rank(v¹) ≤ H0·rank(v¹)`, `≤ rank(v⁰)·H2`).

## Each finrank via an INJECTIVE map into a matrix space (uniform pattern)

Factor `v⁰ = U0·W0` (`U0 : H0×p` full col rank `p = rank v⁰`, `W0 : p×H1` full row rank), giving
`Λ0·U0 = 1`, `W0·Ρ0 = 1`; likewise `v¹ = U1·W1`, `Λ1·U1 = 1`, `W1·Ρ1 = 1` (`s = rank v¹`).

  * `R = range (Y ↦ Y·W1 : Mat(H0×s) →ₗ Mat(H0×H2))`, and `Y ↦ Y·W1` is INJECTIVE (`Ρ1` right-inv),
    so `finrank R = finrank Mat(H0×s) = H0·s`. (`⊆`: `δ⁰·v¹ = (δ⁰·U1)·W1`; `⊇`: `Y = (Y·Λ1)·U1`.)
  * `C = range (Z ↦ U0·Z : Mat(p×H2) →ₗ Mat(H0×H2))`, INJECTIVE (`Λ0` left-inv), `finrank C = p·H2`.
  * `R ⊓ C = range (T ↦ U0·T·W1 : Mat(p×s) →ₗ Mat(H0×H2))`, INJECTIVE, `finrank = p·s`.

Scope L = 2. Uses `exists_rank_factorization` / `exists_left_inverse_of_rank_eq_width` /
`exists_right_inverse_of_rank_eq_height` (banked in `D1HChartRank`).
-/

open Matrix Module
namespace DLNFibre.DLN.RLCT

/-! ## A generic rank factorization for an arbitrary rectangular matrix

`exists_rank_factorization` (banked in `D1HChartRank`) is stated for the width vector
`H : Fin 3 → ℕ` with codomain `H (Fin.last 2)`. We instantiate it at `H = ![p, q, q]` to obtain
the generic factorization of any `Mat(Fin p × Fin q)`. -/

/-- **Generic rank factorization.** Any real `p×q` matrix `B` factors `B = U·V` with `U : p×rank(B)`
and `V : rank(B)×q` both of rank `rank(B)`. (Instantiate `exists_rank_factorization` at
`H = ![p, q, q]`.) -/
theorem exists_rank_factorization_gen {p q : ℕ} (B : Matrix (Fin p) (Fin q) ℝ) :
    ∃ (U : Matrix (Fin p) (Fin B.rank) ℝ) (V : Matrix (Fin B.rank) (Fin q) ℝ),
      B = U * V ∧ U.rank = B.rank ∧ V.rank = B.rank := by
  have := exists_rank_factorization (fun i => ![p, q, q] i) B.rank
    (B : Matrix (Fin (![p, q, q] 0)) (Fin (![p, q, q] (Fin.last 2))) ℝ) rfl
  simpa using this

/-! ## Right-multiplication by a fixed matrix, as a linear map, and its range/finrank -/

/-- Right-multiplication `δ ↦ δ * W` as an `ℝ`-linear map `Mat(a×b) →ₗ Mat(a×c)`. -/
noncomputable def rightMulLin {a b c : ℕ} (W : Matrix (Fin b) (Fin c) ℝ) :
    Matrix (Fin a) (Fin b) ℝ →ₗ[ℝ] Matrix (Fin a) (Fin c) ℝ where
  toFun δ := δ * W
  map_add' x y := Matrix.add_mul x y W
  map_smul' r x := by simp [Matrix.smul_mul]

@[simp] theorem rightMulLin_apply {a b c : ℕ} (W : Matrix (Fin b) (Fin c) ℝ)
    (δ : Matrix (Fin a) (Fin b) ℝ) : rightMulLin (a := a) W δ = δ * W := rfl

/-- Left-multiplication `δ ↦ U * δ` as an `ℝ`-linear map `Mat(b×c) →ₗ Mat(a×c)`. -/
noncomputable def leftMulLin {a b c : ℕ} (U : Matrix (Fin a) (Fin b) ℝ) :
    Matrix (Fin b) (Fin c) ℝ →ₗ[ℝ] Matrix (Fin a) (Fin c) ℝ where
  toFun δ := U * δ
  map_add' x y := Matrix.mul_add U x y
  map_smul' r x := by simp [Matrix.mul_smul]

@[simp] theorem leftMulLin_apply {a b c : ℕ} (U : Matrix (Fin a) (Fin b) ℝ)
    (δ : Matrix (Fin b) (Fin c) ℝ) : leftMulLin (c := c) U δ = U * δ := rfl

/-- **Right-mult by a full-row-rank `W` is injective.** `rank W = height` gives a right inverse `Ρ`
(`W·Ρ = 1`); then `Y·W = 0 ⟹ Y = Y·W·Ρ = 0`. -/
theorem rightMulLin_injective_of_rank_eq_height {a s c : ℕ} (W : Matrix (Fin s) (Fin c) ℝ)
    (hW : W.rank = s) : Function.Injective (rightMulLin (a := a) W) := by
  obtain ⟨Ρ, hΡ⟩ := exists_right_inverse_of_rank_eq_height W hW
  intro Y Z hYZ
  have h0 : Y * W = Z * W := hYZ
  have := congrArg (· * Ρ) h0
  simpa only [Matrix.mul_assoc, hΡ, Matrix.mul_one] using this

/-- **Left-mult by a full-col-rank `U` is injective.** `rank U = width` gives a left inverse `Λ`
(`Λ·U = 1`); then `U·Z = 0 ⟹ Z = Λ·U·Z = 0`. -/
theorem leftMulLin_injective_of_rank_eq_width {a p c : ℕ} (U : Matrix (Fin a) (Fin p) ℝ)
    (hU : U.rank = p) : Function.Injective (leftMulLin (c := c) U) := by
  obtain ⟨Λ, hΛ⟩ := exists_left_inverse_of_rank_eq_width U hU
  intro Y Z hYZ
  have h0 : U * Y = U * Z := hYZ
  have := congrArg (Λ * ·) h0
  simpa only [← Matrix.mul_assoc, hΛ, Matrix.one_mul] using this

/-! ## The range of `δ ↦ δ * v1` and its finrank -/

/-- **`range (δ⁰ ↦ δ⁰·v¹) = range (Y ↦ Y·W1)`** for `v¹ = U1·W1` (`U1` full col rank `s`). Both
inclusions from the one-sided inverse `Λ1·U1 = 1`. -/
theorem range_rightMul_eq_of_factor {a b c s : ℕ} (v1 : Matrix (Fin b) (Fin c) ℝ)
    (U1 : Matrix (Fin b) (Fin s) ℝ) (W1 : Matrix (Fin s) (Fin c) ℝ)
    (hv1 : v1 = U1 * W1) (hU1 : U1.rank = s) :
    LinearMap.range (rightMulLin (a := a) v1) = LinearMap.range (rightMulLin (a := a) W1) := by
  obtain ⟨Λ1, hΛ1⟩ := exists_left_inverse_of_rank_eq_width U1 hU1
  apply le_antisymm
  · rintro _ ⟨δ, rfl⟩
    refine ⟨δ * U1, ?_⟩
    simp only [rightMulLin_apply, hv1, Matrix.mul_assoc]
  · rintro _ ⟨Y, rfl⟩
    refine ⟨Y * Λ1, ?_⟩
    simp only [rightMulLin_apply, hv1]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Λ1 U1 W1, hΛ1, Matrix.one_mul]

/-- **`finrank (range (δ⁰ ↦ δ⁰·v¹)) = H0·rank(v¹)`.** Factor `v¹ = U1·W1`; the range equals
`range (Y ↦ Y·W1)`, and `Y ↦ Y·W1` is injective (full-row-rank `W1`), so its range-finrank is the
domain finrank `H0·s`. -/
theorem finrank_range_rightMul (H0 : ℕ) {b c : ℕ} (v1 : Matrix (Fin b) (Fin c) ℝ) :
    Module.finrank ℝ (LinearMap.range (rightMulLin (a := H0) v1)) = H0 * v1.rank := by
  obtain ⟨U1, W1, hUV, hU1, hW1⟩ := exists_rank_factorization_gen v1
  rw [range_rightMul_eq_of_factor (a := H0) v1 U1 W1 hUV hU1,
    LinearMap.finrank_range_of_inj (rightMulLin_injective_of_rank_eq_height W1 hW1),
    Module.finrank_matrix, Module.finrank_self]
  simp [Fintype.card_fin]

/-! ## The range of `δ ↦ v0 * δ` and its finrank (dual) -/

/-- **`range (δ¹ ↦ v⁰·δ¹) = range (Z ↦ U0·Z)`** for `v⁰ = U0·W0` (`W0` full row rank `p`). -/
theorem range_leftMul_eq_of_factor {a b c p : ℕ} (v0 : Matrix (Fin a) (Fin b) ℝ)
    (U0 : Matrix (Fin a) (Fin p) ℝ) (W0 : Matrix (Fin p) (Fin b) ℝ)
    (hv0 : v0 = U0 * W0) (hW0 : W0.rank = p) :
    LinearMap.range (leftMulLin (c := c) v0) = LinearMap.range (leftMulLin (c := c) U0) := by
  obtain ⟨Ρ0, hΡ0⟩ := exists_right_inverse_of_rank_eq_height W0 hW0
  apply le_antisymm
  · rintro _ ⟨δ, rfl⟩
    refine ⟨W0 * δ, ?_⟩
    simp only [leftMulLin_apply, hv0, Matrix.mul_assoc]
  · rintro _ ⟨Z, rfl⟩
    refine ⟨Ρ0 * Z, ?_⟩
    simp only [leftMulLin_apply, hv0]
    rw [← Matrix.mul_assoc, Matrix.mul_assoc U0 W0 Ρ0, hΡ0, Matrix.mul_one]

/-- **`finrank (range (δ¹ ↦ v⁰·δ¹)) = rank(v⁰)·H2`.** Factor `v⁰ = U0·W0`; the range equals
`range (Z ↦ U0·Z)`, injective (full-col-rank `U0`), range-finrank = domain finrank `p·H2`. -/
theorem finrank_range_leftMul (H2 : ℕ) {a b : ℕ} (v0 : Matrix (Fin a) (Fin b) ℝ) :
    Module.finrank ℝ (LinearMap.range (leftMulLin (c := H2) v0)) = v0.rank * H2 := by
  obtain ⟨U0, W0, hUV, hU0, hW0⟩ := exists_rank_factorization_gen v0
  rw [range_leftMul_eq_of_factor (c := H2) v0 U0 W0 hUV hW0,
    LinearMap.finrank_range_of_inj (leftMulLin_injective_of_rank_eq_width U0 hU0),
    Module.finrank_matrix, Module.finrank_self]
  simp [Fintype.card_fin]

/-! ## The intersection `R ⊓ C` and its finrank

`R ⊓ C = range (T ↦ U0·T·W1)` for `T : Mat(p×s)` (`p = rank v⁰`, `s = rank v¹`), which is injective,
so `finrank = p·s`. -/

/-- The sandwich map `T ↦ U0·T·W1 : Mat(p×s) →ₗ Mat(a×c)`. -/
noncomputable def sandwichLin {a p s c : ℕ} (U0 : Matrix (Fin a) (Fin p) ℝ)
    (W1 : Matrix (Fin s) (Fin c) ℝ) :
    Matrix (Fin p) (Fin s) ℝ →ₗ[ℝ] Matrix (Fin a) (Fin c) ℝ where
  toFun T := U0 * T * W1
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' r x := by simp [Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem sandwichLin_apply {a p s c : ℕ} (U0 : Matrix (Fin a) (Fin p) ℝ)
    (W1 : Matrix (Fin s) (Fin c) ℝ) (T : Matrix (Fin p) (Fin s) ℝ) :
    sandwichLin U0 W1 T = U0 * T * W1 := rfl

/-- **The sandwich map is injective** when `U0` full col rank (`Λ0·U0 = 1`) and `W1` full row rank
(`W1·Ρ1 = 1`): `Λ0·(U0·T·W1)·Ρ1 = T`. -/
theorem sandwichLin_injective {a p s c : ℕ} (U0 : Matrix (Fin a) (Fin p) ℝ)
    (W1 : Matrix (Fin s) (Fin c) ℝ) (hU0 : U0.rank = p) (hW1 : W1.rank = s) :
    Function.Injective (sandwichLin U0 W1) := by
  obtain ⟨Λ0, hΛ0⟩ := exists_left_inverse_of_rank_eq_width U0 hU0
  obtain ⟨Ρ1, hΡ1⟩ := exists_right_inverse_of_rank_eq_height W1 hW1
  intro X Y hXY
  have h0 : U0 * X * W1 = U0 * Y * W1 := hXY
  have hcancel : ∀ T : Matrix (Fin p) (Fin s) ℝ, Λ0 * (U0 * T * W1) * Ρ1 = T := fun T => by
    rw [Matrix.mul_assoc U0 T W1, ← Matrix.mul_assoc Λ0 U0 (T * W1), hΛ0, Matrix.one_mul,
      Matrix.mul_assoc T W1 Ρ1, hΡ1, Matrix.mul_one]
  have := congrArg (fun M => Λ0 * M * Ρ1) h0
  simp only at this
  rw [hcancel X, hcancel Y] at this
  exact this

/-- **`R ⊓ C = range (sandwichLin U0 W1)`.** With `v⁰ = U0·W0` (`U0`/`W0` rank `p`), `v¹ = U1·W1`
(`U1`/`W1` rank `s`):
  * `⊇`: `U0·T·W1 = (U0·T)·W1 ∈ R` and `= U0·(T·W1) ∈ C`.
  * `⊆`: `X ∈ R ⊓ C` ⟹ `X = Y·W1` (from `R = range(·W1)`) and `X = U0·Z` (from `C = range(U0·)`);
    then `Y = X·Ρ1 = U0·Z·Ρ1`, so `X = Y·W1 = U0·(Z·Ρ1)·W1` with `T = Z·Ρ1 : p×s`. -/
theorem inf_range_eq_range_sandwich {a b0 b1 c p s : ℕ} (v0 : Matrix (Fin a) (Fin b0) ℝ)
    (v1 : Matrix (Fin b1) (Fin c) ℝ)
    (U0 : Matrix (Fin a) (Fin p) ℝ) (W0 : Matrix (Fin p) (Fin b0) ℝ)
    (U1 : Matrix (Fin b1) (Fin s) ℝ) (W1 : Matrix (Fin s) (Fin c) ℝ)
    (hv0 : v0 = U0 * W0) (hU0 : U0.rank = p) (hW0 : W0.rank = p)
    (hv1 : v1 = U1 * W1) (hU1 : U1.rank = s) (hW1 : W1.rank = s) :
    (LinearMap.range (rightMulLin (a := a) v1) ⊓ LinearMap.range (leftMulLin (c := c) v0))
      = LinearMap.range (sandwichLin U0 W1) := by
  obtain ⟨Λ0, hΛ0⟩ := exists_left_inverse_of_rank_eq_width U0 hU0
  obtain ⟨Ρ1, hΡ1⟩ := exists_right_inverse_of_rank_eq_height W1 hW1
  have hR : LinearMap.range (rightMulLin (a := a) v1) = LinearMap.range (rightMulLin (a := a) W1) :=
    range_rightMul_eq_of_factor (a := a) v1 U1 W1 hv1 hU1
  have hC : LinearMap.range (leftMulLin (c := c) v0) = LinearMap.range (leftMulLin (c := c) U0) :=
    range_leftMul_eq_of_factor (c := c) v0 U0 W0 hv0 hW0
  rw [hR, hC]
  apply le_antisymm
  · rintro X ⟨hXR, hXC⟩
    -- `X = Y·W1` and `X = U0·Z`.
    obtain ⟨Y, hY⟩ := hXR
    obtain ⟨Z, hZ⟩ := hXC
    simp only [rightMulLin_apply] at hY
    simp only [leftMulLin_apply] at hZ
    refine ⟨Z * Ρ1, ?_⟩
    simp only [sandwichLin_apply]
    -- `X = Y·W1` ⟹ `Y = X·Ρ1` (since `W1·Ρ1 = 1`); then `U0·(Z·Ρ1)·W1 = X·Ρ1·W1 = Y·W1 = X`.
    have hYval : Y = X * Ρ1 := by
      rw [← hY, Matrix.mul_assoc, hΡ1, Matrix.mul_one]
    calc U0 * (Z * Ρ1) * W1
        = U0 * Z * Ρ1 * W1 := by rw [← Matrix.mul_assoc]
      _ = X * Ρ1 * W1 := by rw [hZ]
      _ = Y * W1 := by rw [← hYval]
      _ = X := hY
  · rintro _ ⟨T, rfl⟩
    refine ⟨⟨U0 * T, ?_⟩, ⟨T * W1, ?_⟩⟩
    · simp only [rightMulLin_apply, sandwichLin_apply, Matrix.mul_assoc]
    · simp only [leftMulLin_apply, sandwichLin_apply, Matrix.mul_assoc]

/-- **`finrank (R ⊓ C) = rank(v⁰)·rank(v¹)`.** Factor both `v⁰`, `v¹`; the inf is the range of the
injective sandwich map `T ↦ U0·T·W1` on `Mat(p×s)`. -/
theorem finrank_inf_range {a b0 b1 c : ℕ} (v0 : Matrix (Fin a) (Fin b0) ℝ)
    (v1 : Matrix (Fin b1) (Fin c) ℝ) :
    Module.finrank ℝ
        ↥(LinearMap.range (rightMulLin (a := a) v1) ⊓ LinearMap.range (leftMulLin (c := c) v0))
      = v0.rank * v1.rank := by
  obtain ⟨U0, W0, hv0, hU0, hW0⟩ := exists_rank_factorization_gen v0
  obtain ⟨U1, W1, hv1, hU1, hW1⟩ := exists_rank_factorization_gen v1
  rw [inf_range_eq_range_sandwich v0 v1 U0 W0 U1 W1 hv0 hU0 hW0 hv1 hU1 hW1,
    LinearMap.finrank_range_of_inj (sandwichLin_injective U0 W1 hU0 hW1),
    Module.finrank_matrix, Module.finrank_self]
  simp [Fintype.card_fin]

/-! ## `range (jointDiffL2 H v) = R ⊔ C` and the exact rank -/

/-- Reconstruct a `Params H` from a pair of layer matrices (`L = 2`): layer `0 ↦ m0`, `1 ↦ m1`.
Same dependent-`if` construction as `gaugeImage_mem_range`. -/
noncomputable def paramsOfLayers (H : Fin (2 + 1) → ℕ)
    (m0 : Matrix (Fin (H 0)) (Fin (H 1)) ℝ) (m1 : Matrix (Fin (H 1)) (Fin (H 2)) ℝ) :
    Params H := fun s =>
  if h : (s : ℕ) = 0 then (by rw [show s = 0 from Fin.ext h]; exact m0)
  else (by rw [show s = 1 from Fin.ext (by omega)]; exact m1)

@[simp] theorem layer0_paramsOfLayers (H : Fin (2 + 1) → ℕ)
    (m0 : Matrix (Fin (H 0)) (Fin (H 1)) ℝ) (m1 : Matrix (Fin (H 1)) (Fin (H 2)) ℝ) :
    layer0 H (paramsOfLayers H m0 m1) = m0 := rfl

@[simp] theorem layer1_paramsOfLayers (H : Fin (2 + 1) → ℕ)
    (m0 : Matrix (Fin (H 0)) (Fin (H 1)) ℝ) (m1 : Matrix (Fin (H 1)) (Fin (H 2)) ℝ) :
    layer1 H (paramsOfLayers H m0 m1) = m1 := rfl

/-- **The joint-differential range is the sup of the two single-argument ranges** (`L = 2`):
`range (jointDiffL2 H v) = range (rightMulLin (layer1 v)) ⊔ range (leftMulLin (layer0 v))`. The
`⊆` direction reads `jointDiffL2 δ = layer0 δ · v¹ + v⁰ · layer1 δ` as a sum of the two ranges; the
`⊇` direction reconstructs a `Params` witness via `paramsOfLayers`. -/
theorem range_jointDiffL2_eq_sup (H : Fin (2 + 1) → ℕ) (v : Params H) :
    LinearMap.range (jointDiffL2 H v)
      = LinearMap.range (rightMulLin (a := H 0) (layer1 H v))
        ⊔ LinearMap.range (leftMulLin (c := H 2) (layer0 H v)) := by
  apply le_antisymm
  · rintro _ ⟨δ, rfl⟩
    rw [Submodule.mem_sup]
    exact ⟨layer0 H δ * layer1 H v, ⟨layer0 H δ, rfl⟩, layer0 H v * layer1 H δ,
      ⟨layer1 H δ, rfl⟩, rfl⟩
  · rw [sup_le_iff]
    constructor
    · rintro _ ⟨m0, rfl⟩
      refine ⟨paramsOfLayers H m0 0, ?_⟩
      change layer0 H _ * layer1 H v + layer0 H v * layer1 H _ = _
      rw [layer0_paramsOfLayers, layer1_paramsOfLayers, Matrix.mul_zero, add_zero,
        rightMulLin_apply]
    · rintro _ ⟨m1, rfl⟩
      refine ⟨paramsOfLayers H 0 m1, ?_⟩
      change layer0 H _ * layer1 H v + layer0 H v * layer1 H _ = _
      rw [layer0_paramsOfLayers, layer1_paramsOfLayers, Matrix.zero_mul, zero_add, leftMulLin_apply]

/-- **The EXACT joint-differential rank (b3), UNCONDITIONAL in the two layer ranks.** At any `L = 2`
base point `v`, the joint differential `Dg(v) : δ ↦ δ⁰·v¹ + v⁰·δ¹` has

    finrank (range (jointDiffL2 H v)) = H0·rank(v¹) + rank(v⁰)·H2 − rank(v⁰)·rank(v¹).

Inclusion–exclusion `finrank(R ⊔ C) = finrank R + finrank C − finrank(R ⊓ C)` on the two
single-argument ranges (`finrank R = H0·rank(v¹)`, `finrank C = rank(v⁰)·H2`,
`finrank(R ⊓ C) = rank(v⁰)·rank(v¹)`), with honest ℕ subtraction. -/
theorem finrank_range_jointDiffL2_eq (H : Fin (2 + 1) → ℕ) (v : Params H) :
    Module.finrank ℝ (LinearMap.range (jointDiffL2 H v))
      = H 0 * (layer1 H v).rank + (layer0 H v).rank * H 2
        - (layer0 H v).rank * (layer1 H v).rank := by
  set R := LinearMap.range (rightMulLin (a := H 0) (layer1 H v)) with hR
  set C := LinearMap.range (leftMulLin (c := H 2) (layer0 H v)) with hC
  -- inclusion–exclusion: `finrank(R ⊔ C) + finrank(R ⊓ C) = finrank R + finrank C`.
  have hincl := Submodule.finrank_sup_add_finrank_inf_eq R C
  have hRfin : Module.finrank ℝ R = H 0 * (layer1 H v).rank := by
    rw [hR, finrank_range_rightMul]
  have hCfin : Module.finrank ℝ C = (layer0 H v).rank * H 2 := by
    rw [hC, finrank_range_leftMul]
  have hInffin : Module.finrank ℝ ↥(R ⊓ C) = (layer0 H v).rank * (layer1 H v).rank := by
    rw [hR, hC, finrank_inf_range]
  rw [range_jointDiffL2_eq_sup H v, ← hR, ← hC]
  omega

end DLNFibre.DLN.RLCT
