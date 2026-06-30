import DLNFibre.DLN.RLCT.Validate.D1HChartGrad
import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear
import DLNFibre.Core.RankLocusClosed
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# `DLNFibre.DLN.RLCT.Validate.D1HChartRank` — the H_indep rank lower bound (step 2b)

The joint differential `Dg(v)` of the DLN loss entries at an optimal `v` (`L = 2`), and its rank
lower bound `nReg ≤ finrank (range Dg(v))` — the H_indep core that makes the selected-minor chart's
derivative `f'` invertible (`det DΦ(v) ≠ 0` via the banked determinantal-minor engine
`Core.RankLocusClosed.exists_submatrix_det_ne_zero_of_le_rank`).

At `L = 2`, `prod A = A⁰·A¹` (layers `A 0 : Mat_{H0×H1}`, `A 1 : Mat_{H1×H2}`); the loss entry
gradients at `v` are the components of the linear map

    Dg(v) : Params H →ₗ[ℝ] Mat_{H0×H2},   δ ↦ δ⁰·(v 1) + (v 0)·δ¹

(`δ⁰ A²_v + A¹_v δ²` in the paper's notation). `rank Dg(v) ≥ nReg` at EVERY optimal `v`.

**Route (gauge-fixed injection, decorrelated Codex xhigh + ROUTE C, both PASS).** Factor the
rank-`r` target `B = U · W` (`U : H0×r` full column rank, `W : r×H2` full row rank, from the PUBLIC
`block_elimination`). Lift through `v`: `col B ⊆ col(v 0)` and `row B ⊆ row(v 1)` give
`U = (v 0)·C`, `W = K·(v 1)`. The gauge-slice map

    Ψ : {X : Mat_{H0×r} | Λ·X = 0} × Mat_{r×H2} →ₗ range Dg,   (X,Y) ↦ X·W + U·Y

(with `Λ` a LEFT inverse of `U`, `Ρ` a RIGHT inverse of `W`, from the Gram matrices) is INJECTIVE
(apply `Λ` left to kill `X·W`, get `Y = 0`; then `X·W = 0`, apply `Ρ` right to get `X = 0`). Its
domain has `finrank = (H0·r − r²) + r·H2 = nReg` (the slice `Λ·X = 0` is `ker (X ↦ Λ·X)`, a
surjection with right inverse `Z ↦ U·Z`). `Submodule.finrank_le` then gives the bound.
This sidesteps the (genuinely-Mathlib-absent) intersection-dim `colspace(v⁰)⊗rowspace(v¹) = a·b`.

STATUS: LANDED — the rank lower bound `nReg_le_finrank_range_jointDiffL2` is proved (no open goal),
and Step 1 ties the analytic flat-Jacobian gradient to `jointDiffL2 ∘ flatSymm`
(`prodAuxEntryDeriv_two_apply_eq_jointDiffL2`). Clean-three.
-/

open Matrix Module
open scoped Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The layer matrices of `A : Params H` at `L = 2`, cleanly typed as `Mat (H 0) (H 1)` and
`Mat (H 1) (H 2)` (the raw `A 0`, `A 1` carry `Fin.castSucc`/`Fin.succ` index forms that block
`HMul` unification; these ascriptions force the `rfl` defeq). -/
@[reducible] noncomputable def layer0 (H : Fin (2 + 1) → ℕ) (A : Params H) :
    Matrix (Fin (H 0)) (Fin (H 1)) ℝ := A 0
@[reducible] noncomputable def layer1 (H : Fin (2 + 1) → ℕ) (A : Params H) :
    Matrix (Fin (H 1)) (Fin (H 2)) ℝ := A 1

@[simp] theorem layer0_add (H : Fin (2 + 1) → ℕ) (A B : Params H) :
    layer0 H (A + B) = layer0 H A + layer0 H B := rfl
@[simp] theorem layer1_add (H : Fin (2 + 1) → ℕ) (A B : Params H) :
    layer1 H (A + B) = layer1 H A + layer1 H B := rfl
@[simp] theorem layer0_smul (H : Fin (2 + 1) → ℕ) (c : ℝ) (A : Params H) :
    layer0 H (c • A) = c • layer0 H A := rfl
@[simp] theorem layer1_smul (H : Fin (2 + 1) → ℕ) (c : ℝ) (A : Params H) :
    layer1 H (c • A) = c • layer1 H A := rfl

noncomputable def jointDiffL2 (H : Fin (2 + 1) → ℕ) (v : Params H) :
    Params H →ₗ[ℝ] Matrix (Fin (H 0)) (Fin (H 2)) ℝ where
  -- `δ⁰·(v¹) + (v⁰)·δ¹` with clean `Mat (H 0) (H 1)` / `Mat (H 1) (H 2)` layer types.
  toFun δ := layer0 H δ * layer1 H v + layer0 H v * layer1 H δ
  map_add' δ₁ δ₂ := by
    simp only [layer0_add, layer1_add, Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' c δ := by
    simp only [layer0_smul, layer1_smul, Matrix.smul_mul, Matrix.mul_smul, RingHom.id_apply,
      smul_add]

/-! ## A square full-rank matrix is a unit (re-stated, cf. `DeepestLeadingBlock`) -/

/-- **A square full-rank matrix over `ℝ` is a unit.** `rank A = n` ⟹ `range A.toLin' = ⊤` ⟹ unit.
(Local copy; `DeepestLeadingBlock` has a `private` version — kept self-contained here.) -/
private theorem isUnit_of_rank_eq_card {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h : A.rank = n) :
    IsUnit A := by
  rw [← Matrix.isUnit_toLin'_iff, LinearMap.isUnit_iff_range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  have hrange : Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) = A.rank := rfl
  rw [hrange, h, Module.finrank_fin_fun]

/-! ## One-sided inverses from full rank (Gram-matrix route) -/

/-- **Full column rank ⟹ a left inverse.** `U : p×r` with `rank U = r` (= number of columns) has a
left inverse `Λ : r×p`, `Λ·U = 1`. Via the Gram matrix `Uᵀ·U` (rank `r`, square, hence a unit):
`Λ := (UᵀU)⁻¹·Uᵀ`. -/
theorem exists_left_inverse_of_rank_eq_width {p r : ℕ} (U : Matrix (Fin p) (Fin r) ℝ)
    (h : U.rank = r) : ∃ Λ : Matrix (Fin r) (Fin p) ℝ, Λ * U = 1 := by
  classical
  have hg : (Uᵀ * U).rank = r := by rw [Matrix.rank_transpose_mul_self, h]
  have hunit : IsUnit (Uᵀ * U) := isUnit_of_rank_eq_card _ hg
  refine ⟨(Uᵀ * U)⁻¹ * Uᵀ, ?_⟩
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit)]

/-- **Full row rank ⟹ a right inverse.** `W : r×q` with `rank W = r` (= number of rows) has a right
inverse `Ρ : q×r`, `W·Ρ = 1`. Via the Gram matrix `W·Wᵀ` (rank `r`, square, hence a unit):
`Ρ := Wᵀ·(W·Wᵀ)⁻¹`. -/
theorem exists_right_inverse_of_rank_eq_height {r q : ℕ} (W : Matrix (Fin r) (Fin q) ℝ)
    (h : W.rank = r) : ∃ Ρ : Matrix (Fin q) (Fin r) ℝ, W * Ρ = 1 := by
  classical
  have hg : (W * Wᵀ).rank = r := by rw [Matrix.rank_self_mul_transpose, h]
  have hunit : IsUnit (W * Wᵀ) := isUnit_of_rank_eq_card _ hg
  refine ⟨Wᵀ * (W * Wᵀ)⁻¹, ?_⟩
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit)]

/-! ## The rank-`r` factorization (from the public `block_elimination`) -/

/-- The `[I_r ; 0]` embedding `Fin r → Fin N` and the `[I_r | 0]` projection `Fin N → Fin r`,
local copies (the `Skeleton` versions are `private`). -/
private def embR (N r : ℕ) : Matrix (Fin N) (Fin r) ℝ :=
  Matrix.of (fun (j : Fin N) (k : Fin r) => if (j : ℕ) = (k : ℕ) then (1 : ℝ) else 0)
private def projR (r N : ℕ) : Matrix (Fin r) (Fin N) ℝ :=
  Matrix.of (fun (k : Fin r) (j : Fin N) => if (k : ℕ) = (j : ℕ) then (1 : ℝ) else 0)

/-- The corner block `diag(I_r, 0)` factors as `embR · projR`. -/
private theorem corner_eq_embR_mul_projR (a c r : ℕ) :
    (Matrix.of (fun (i : Fin a) (j : Fin c) =>
        if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0))
      = embR a r * projR r c := by
  ext i j; simp only [embR, projR, Matrix.mul_apply, Matrix.of_apply]
  by_cases hi : (i : ℕ) < r
  · rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin r)]
    · simp only [if_true, one_mul]
      by_cases hij : (i : ℕ) = (j : ℕ)
      · rw [if_pos hij, if_pos ⟨hij, hi⟩]
      · rw [if_neg hij, if_neg (fun hc => hij hc.1)]
    · intro b _ hb
      rw [if_neg (by simpa [Fin.ext_iff] using fun h => hb (Fin.ext h.symm)), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg (by tauto)]; symm
    apply Finset.sum_eq_zero; intro k _; rw [if_neg (by intro h; omega), zero_mul]

/-- **The rank-`r` factorization** of a rank-`r` matrix, derived from the public `block_elimination`
normal form `P·B·Q = corner` (`P,Q` units). `B = U·V` with `U : H0×r`, `V : r×H2`, both rank `r`.
(The `Skeleton` helpers `factor_from_blockElim`/`rank_factor_{left,right}` are `private`; re-derived
here from the public `block_elimination` so this file stays self-contained.) -/
theorem exists_rank_factorization (H : Fin (2 + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r) :
    ∃ (U : Matrix (Fin (H 0)) (Fin r) ℝ) (V : Matrix (Fin r) (Fin (H (Fin.last 2))) ℝ),
      B = U * V ∧ U.rank = r ∧ V.rank = r := by
  classical
  obtain ⟨P, Q, hP, hQ, hPBQ⟩ := block_elimination H r B hB
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  set U : Matrix (Fin (H 0)) (Fin r) ℝ := P⁻¹ * embR (H 0) r with hU
  set V : Matrix (Fin r) (Fin (H (Fin.last 2))) ℝ := projR r (H (Fin.last 2)) * Q⁻¹ with hV
  have hfac : B = U * V := by
    have key : P⁻¹ * (P * B * Q) * Q⁻¹ = B := by
      rw [Matrix.mul_assoc P B Q, ← Matrix.mul_assoc P⁻¹ P (B * Q),
        Matrix.nonsing_inv_mul P hPd, Matrix.one_mul, Matrix.mul_assoc B Q Q⁻¹,
        Matrix.mul_nonsing_inv Q hQd, Matrix.mul_one]
    calc B = P⁻¹ * (P * B * Q) * Q⁻¹ := key.symm
      _ = P⁻¹ * (embR (H 0) r * projR r (H (Fin.last 2))) * Q⁻¹ := by
            rw [hPBQ, corner_eq_embR_mul_projR]
      _ = (P⁻¹ * embR (H 0) r) * (projR r (H (Fin.last 2)) * Q⁻¹) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  -- `U.rank = r`: from `B = U·V` and `rank B = r`, sandwich `rank U` between `r` and `r`.
  have hUr : U.rank = r := by
    have hle : U.rank ≤ r := le_trans (Matrix.rank_le_card_width _) (by rw [Fintype.card_fin])
    have hge : r ≤ U.rank := by
      have : B.rank ≤ U.rank := by rw [hfac]; exact Matrix.rank_mul_le_left _ _
      omega
    omega
  have hVr : V.rank = r := by
    have hle : V.rank ≤ r := Matrix.rank_le_height V
    have hge : r ≤ V.rank := by
      have : B.rank ≤ V.rank := by rw [hfac]; exact Matrix.rank_mul_le_right _ _
      omega
    omega
  exact ⟨U, V, hfac, hUr, hVr⟩

/-! ## `prod` at `L = 2` is the layer product -/

/-- The `(i,j)` entry of the `L = 2` product `prod A = A⁰·A¹` (cast-clean entry formula, cf.
`RouteMBoxThresholdRRP.prod_two_layer_rrp`). The `prodAux` fold's `1 *` and width-casts resolve
per-summand. -/
theorem prod_entry (H : Fin (2 + 1) → ℕ) (A : Params H) (i : Fin (H 0)) (j : Fin (H 2)) :
    prod H A i j = ∑ k : Fin (H 1), A 0 i k * A 1 k j := by
  unfold prod
  simp only [prodAux, Matrix.mul_apply, eq_mpr_eq_cast]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  convert congrFun (congrFun (Matrix.one_mul (cast (by rfl) (cast (by rfl) (A 0)))) i) k using 2

theorem prod_eq_layerMul (H : Fin (2 + 1) → ℕ) (v : Params H) :
    prod H v = layer0 H v * layer1 H v := by
  apply Matrix.ext; intro i j
  rw [prod_entry, Matrix.mul_apply]

/-! ## Factor-through-columns / -rows helpers -/

/-- **Factor through columns.** If every column of `U` lies in `range M.mulVecLin` (the column
space of `M`), then `U = M · C` for some `C` (the columns of `C` are the chosen preimages). -/
theorem exists_factor_left_of_col_mem {p m r : ℕ} (M : Matrix (Fin p) (Fin m) ℝ)
    (U : Matrix (Fin p) (Fin r) ℝ)
    (h : ∀ k : Fin r, (fun i => U i k) ∈ LinearMap.range M.mulVecLin) :
    ∃ C : Matrix (Fin m) (Fin r) ℝ, U = M * C := by
  classical
  choose c hc using h
  refine ⟨Matrix.of (fun i k => c k i), ?_⟩
  ext i k
  have hik := congrFun (hc k) i
  simp only [Matrix.mulVecLin_apply] at hik
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  rw [← hik, Matrix.mulVec]
  rfl

/-- **Column-space containment from a product factorization.** `B = M · N ⟹ col B ⊆ col M`
(`range B.mulVecLin ≤ range M.mulVecLin`). -/
theorem range_mulVecLin_le_of_eq_mul {p s q : ℕ} (M : Matrix (Fin p) (Fin s) ℝ)
    (N : Matrix (Fin s) (Fin q) ℝ) (B : Matrix (Fin p) (Fin q) ℝ) (hB : B = M * N) :
    LinearMap.range B.mulVecLin ≤ LinearMap.range M.mulVecLin := by
  rw [hB]; intro x hx
  rw [LinearMap.mem_range] at hx ⊢
  obtain ⟨c, hc⟩ := hx
  refine ⟨N.mulVec c, ?_⟩
  rw [Matrix.mulVecLin_apply] at hc ⊢
  rw [← hc, ← Matrix.mulVec_mulVec]

/-- `finrank (range B.mulVecLin) = B.rank` (definitional). -/
theorem finrank_range_mulVecLin (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℝ) :
    Module.finrank ℝ (LinearMap.range B.mulVecLin) = B.rank := rfl

/-- The `k`-th column of `M` is `M.mulVecLin (Pi.single k 1)`, hence lies in `range M.mulVecLin`. -/
theorem col_mem_range_mulVecLin {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (k : Fin q) :
    (fun i => M i k) ∈ LinearMap.range M.mulVecLin := by
  refine ⟨Pi.single k 1, ?_⟩
  funext i
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  rfl

/-! ## The lifts: `B = (v 0)·(v 1)` gives factors through `v` -/

/-- **Left lift through `v 0`.** From `prod v = (v 0)·(v 1) = U·V` (`U.rank = r = (U*V).rank`), the
columns of `U` lie in the column space of `v 0`, so `U = (v 0)·C` for some `C : H1×r`. (Column
space: `col B ⊆ col U` and `rank U = rank B = r` force `col U = col B ⊆ col (v 0)`.) -/
theorem exists_left_lift (H : Fin (2 + 1) → ℕ) (r : ℕ) (v : Params H)
    (U : Matrix (Fin (H 0)) (Fin r) ℝ) (V : Matrix (Fin r) (Fin (H (Fin.last 2))) ℝ)
    (hopt : prod H v = U * V) (hUr : U.rank = r) (hB : (U * V).rank = r) :
    ∃ C : Matrix (Fin (H 1)) (Fin r) ℝ, U = layer0 H v * C := by
  -- `col (U*V) ⊆ col U`, equal finrank ⟹ `col U = col (U*V)`.
  have hle1 : LinearMap.range (U * V).mulVecLin ≤ LinearMap.range U.mulVecLin :=
    range_mulVecLin_le_of_eq_mul U V _ rfl
  have heq : LinearMap.range U.mulVecLin = LinearMap.range (U * V).mulVecLin := by
    refine (Submodule.eq_of_le_of_finrank_le hle1 ?_).symm
    rw [finrank_range_mulVecLin, finrank_range_mulVecLin, hUr, hB]
  -- `col (U*V) = col (prod v) = col (layer0·layer1) ⊆ col (layer0)`.
  have hprod : prod H v = layer0 H v * layer1 H v := prod_eq_layerMul H v
  have hle2 : LinearMap.range (U * V).mulVecLin ≤ LinearMap.range (layer0 H v).mulVecLin := by
    rw [← hopt, hprod]
    exact range_mulVecLin_le_of_eq_mul (layer0 H v) (layer1 H v) _ rfl
  -- so `col U ⊆ col (layer0 v)`; each column of `U` is a column-space element.
  have hcol : ∀ k : Fin r, (fun i => U i k) ∈ LinearMap.range (layer0 H v).mulVecLin := by
    intro k
    apply hle2
    -- the `k`-th column of `U` ∈ col U = col (U*V)
    rw [← heq]; exact col_mem_range_mulVecLin U k
  exact exists_factor_left_of_col_mem (layer0 H v) U hcol

/-- **Right lift through `v 1`.** Dually, `V = K·(v 1)` for some `K : r×H1` — transpose of the left
lift (`rowᵀ = col`). -/
theorem exists_right_lift (H : Fin (2 + 1) → ℕ) (r : ℕ) (v : Params H)
    (U : Matrix (Fin (H 0)) (Fin r) ℝ) (V : Matrix (Fin r) (Fin (H (Fin.last 2))) ℝ)
    (hopt : prod H v = U * V) (hVr : V.rank = r) (hB : (U * V).rank = r) :
    ∃ K : Matrix (Fin r) (Fin (H 1)) ℝ, V = K * layer1 H v := by
  -- transpose: `Vᵀ = (layer1 v)ᵀ · Kᵀ` via the left lift applied to the transposed factorization.
  have hoptT : (prod H v)ᵀ = Vᵀ * Uᵀ := by rw [hopt, Matrix.transpose_mul]
  have hVrT : Vᵀ.rank = r := by rw [Matrix.rank_transpose, hVr]
  have hBT : (Vᵀ * Uᵀ).rank = r := by rw [← Matrix.transpose_mul, Matrix.rank_transpose, hB]
  have hprod : prod H v = layer0 H v * layer1 H v := prod_eq_layerMul H v
  -- `col Vᵀ ⊆ col Vᵀ`, equal finrank route mirrored.
  have hle1 : LinearMap.range (Vᵀ * Uᵀ).mulVecLin ≤ LinearMap.range Vᵀ.mulVecLin :=
    range_mulVecLin_le_of_eq_mul Vᵀ Uᵀ _ rfl
  have heq : LinearMap.range Vᵀ.mulVecLin = LinearMap.range (Vᵀ * Uᵀ).mulVecLin := by
    refine (Submodule.eq_of_le_of_finrank_le hle1 ?_).symm
    rw [finrank_range_mulVecLin, finrank_range_mulVecLin, hVrT, hBT]
  have hfacT : (Vᵀ * Uᵀ) = (layer1 H v)ᵀ * (layer0 H v)ᵀ := by
    rw [← hoptT, hprod]; exact Matrix.transpose_mul _ _
  have hle2 : LinearMap.range (Vᵀ * Uᵀ).mulVecLin
      ≤ LinearMap.range (layer1 H v)ᵀ.mulVecLin :=
    range_mulVecLin_le_of_eq_mul (layer1 H v)ᵀ (layer0 H v)ᵀ _ hfacT
  have hcol : ∀ k : Fin r, (fun i => Vᵀ i k) ∈ LinearMap.range (layer1 H v)ᵀ.mulVecLin := by
    intro k
    apply hle2
    rw [← heq]; exact col_mem_range_mulVecLin Vᵀ k
  obtain ⟨Kt, hKt⟩ := exists_factor_left_of_col_mem (layer1 H v)ᵀ Vᵀ hcol
  refine ⟨Ktᵀ, ?_⟩
  have := congrArg Matrix.transpose hKt
  rw [Matrix.transpose_transpose, Matrix.transpose_mul, Matrix.transpose_transpose] at this
  exact this

/-! ## The gauge-fixed injection and its finrank -/

/-- **A range membership for the gauge map.** With `U = layer0·C`, `V = K·layer1`, every
`X·V + U·Y` lies in `range (jointDiffL2 H v)` — it is `jointDiffL2 δ` for the `δ` whose layers are
`δ⁰ = X·K`, `δ¹ = C·Y` (so `δ⁰·v¹ + v⁰·δ¹ = (X·K)·layer1 + layer0·(C·Y) = X·V + U·Y`). -/
theorem gaugeImage_mem_range (H : Fin (2 + 1) → ℕ) (v : Params H) {r : ℕ}
    (C : Matrix (Fin (H 1)) (Fin r) ℝ) (K : Matrix (Fin r) (Fin (H 1)) ℝ)
    (U : Matrix (Fin (H 0)) (Fin r) ℝ) (V : Matrix (Fin r) (Fin (H 2)) ℝ)
    (hU : U = layer0 H v * C) (hV : V = K * layer1 H v)
    (X : Matrix (Fin (H 0)) (Fin r) ℝ) (Y : Matrix (Fin r) (Fin (H 2)) ℝ) :
    X * V + U * Y ∈ LinearMap.range (jointDiffL2 H v) := by
  classical
  refine ⟨fun s => if h : (s : ℕ) = 0 then (by
      rw [show s = 0 from Fin.ext h]; exact X * K)
    else (by rw [show s = 1 from Fin.ext (by omega)]; exact C * Y), ?_⟩
  show layer0 H _ * layer1 H v + layer0 H v * layer1 H _ = X * V + U * Y
  have hl0 : layer0 H (fun s => if h : (s : ℕ) = 0 then (by
        rw [show s = 0 from Fin.ext h]; exact X * K)
      else (by rw [show s = 1 from Fin.ext (by omega)]; exact C * Y)) = X * K := rfl
  have hl1 : layer1 H (fun s => if h : (s : ℕ) = 0 then (by
        rw [show s = 0 from Fin.ext h]; exact X * K)
      else (by rw [show s = 1 from Fin.ext (by omega)]; exact C * Y)) = C * Y := rfl
  rw [hl0, hl1, hU, hV, Matrix.mul_assoc, Matrix.mul_assoc]

/-- **The H_indep rank lower bound** (step 2b). At an optimal `v` (`prod v = B`, `rank B = r`), the
joint differential `Dg(v)` has rank at least `nReg = r(H0 + H2 − r)`. The gauge-fixed injection (see
file header) embeds an `nReg`-dimensional space into `range (jointDiffL2 H v)`; `finrank_le`
gives the bound. Consumed by the banked determinantal-minor engine to produce the invertible
`nReg`-minor, hence `det DΦ(v) ≠ 0`. -/
theorem nReg_le_finrank_range_jointDiffL2 (H : Fin (2 + 1) → ℕ) (r : ℕ) (v : Params H)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ)
    (hopt : prod H v = B) (hr : B.rank = r) :
    r * (H 0 + H (Fin.last 2) - r) ≤ finrank ℝ (LinearMap.range (jointDiffL2 H v)) := by
  classical
  -- Normalize the goal codomain `H (Fin.last 2)` to `H 2` (defeq, `Fin.last 2 = 2`).
  rw [show H (Fin.last 2) = H 2 from rfl]
  -- factorization `B = U·V`, `U.rank = V.rank = r`; retype `V` to the `H 2` codomain (defeq).
  obtain ⟨U, V0, hUV, hUr, hV0r⟩ := exists_rank_factorization H r B hr
  set V : Matrix (Fin r) (Fin (H 2)) ℝ := V0 with hVdef
  have hVr : V.rank = r := hV0r
  have hUVeq : (U * V0).rank = r := by rw [← hUV, hr]
  -- the lifts `U = layer0·C`, `V = K·layer1`.
  have hopt' : prod H v = U * V := hopt.trans hUV
  obtain ⟨C, hC⟩ := exists_left_lift H r v U V hopt' hUr hUVeq
  obtain ⟨K, hK⟩ := exists_right_lift H r v U V hopt' hVr hUVeq
  -- the one-sided inverses `Λ·U = 1`, `V·Ρ = 1`.
  obtain ⟨Λ, hΛ⟩ := exists_left_inverse_of_rank_eq_width U hUr
  obtain ⟨Ρ, hΡ⟩ := exists_right_inverse_of_rank_eq_height V hVr
  -- `ΛL : Mat(H0×r) →ₗ Mat(r×r)`, `X ↦ Λ·X`, surjective (right inverse `Z ↦ U·Z`).
  set ΛL : Matrix (Fin (H 0)) (Fin r) ℝ →ₗ[ℝ] Matrix (Fin r) (Fin r) ℝ :=
    { toFun := fun X => Λ * X
      map_add' := fun a b => Matrix.mul_add Λ a b
      map_smul' := fun c a => by simp [Matrix.mul_smul] } with hΛL
  have hΛLapp : ∀ X, ΛL X = Λ * X := fun X => rfl
  have hΛLsurj : Function.Surjective ΛL := by
    intro Z
    exact ⟨U * Z, by rw [hΛLapp, ← Matrix.mul_assoc, hΛ, Matrix.one_mul]⟩
  -- the gauge map `Ψ : ker ΛL × Mat(r×H2) →ₗ Mat(H0×H2)`, `(⟨X,_⟩, Y) ↦ X·V + U·Y`, built from
  -- `coprod` of `(· * V) ∘ ker-subtype` and `(U * ·)`.
  set Ψ : (LinearMap.ker ΛL) × Matrix (Fin r) (Fin (H 2)) ℝ →ₗ[ℝ]
      Matrix (Fin (H 0)) (Fin (H 2)) ℝ :=
    LinearMap.coprod
      (({ toFun := fun X => X * V
          map_add' := fun a b => Matrix.add_mul a b V
          map_smul' := fun c a => by simp [Matrix.smul_mul] } :
          Matrix (Fin (H 0)) (Fin r) ℝ →ₗ[ℝ] Matrix (Fin (H 0)) (Fin (H 2)) ℝ).comp
        (LinearMap.ker ΛL).subtype)
      ({ toFun := fun Y => U * Y
         map_add' := fun a b => Matrix.mul_add U a b
         map_smul' := fun c a => by simp [Matrix.mul_smul] } :
          Matrix (Fin r) (Fin (H 2)) ℝ →ₗ[ℝ] Matrix (Fin (H 0)) (Fin (H 2)) ℝ) with hΨ
  have hΨapp : ∀ (p : (LinearMap.ker ΛL) × Matrix (Fin r) (Fin (H 2)) ℝ),
      Ψ p = (p.1 : Matrix (Fin (H 0)) (Fin r) ℝ) * V + U * p.2 := fun p => rfl
  -- `Ψ` is injective: `X·V + U·Y = 0` ⟹ (apply Λ left, `ΛX = 0`) `Y = 0`, then `X·V = 0`,
  -- (apply Ρ right) `X = 0`.
  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨⟨X, hXker⟩, Y⟩ hzero
    rw [LinearMap.mem_ker] at hzero
    have hXY : X * V + U * Y = 0 := (hΨapp ⟨⟨X, hXker⟩, Y⟩).symm.trans hzero
    have hX0 : Λ * X = 0 := by
      have : ΛL X = 0 := hXker
      rw [hΛLapp] at this; exact this
    -- apply Λ on the left: `Λ·(X·V) + Λ·(U·Y) = 0`, i.e. `(Λ·X)·V + (Λ·U)·Y = 0`.
    have hY : Y = 0 := by
      have := congrArg (fun M => Λ * M) hXY
      simp only [Matrix.mul_add, ← Matrix.mul_assoc, hX0, Matrix.zero_mul, hΛ,
        Matrix.one_mul, zero_add, Matrix.mul_zero] at this
      exact this
    have hXV : X * V = 0 := by rw [hY, Matrix.mul_zero, add_zero] at hXY; exact hXY
    have hX : X = 0 := by
      have := congrArg (fun M => M * Ρ) hXV
      simp only [Matrix.mul_assoc, hΡ, Matrix.mul_one, Matrix.zero_mul] at this
      exact this
    -- conclude the pair is zero
    apply Prod.ext
    · exact Subtype.ext hX
    · exact hY
  -- `range Ψ ≤ range (jointDiffL2 H v)`.
  have hrange : LinearMap.range Ψ ≤ LinearMap.range (jointDiffL2 H v) := by
    rintro _ ⟨⟨⟨X, _⟩, Y⟩, rfl⟩
    rw [hΨapp]
    exact gaugeImage_mem_range H v C K U V hC hK X Y
  -- domain finrank: `finrank (ker ΛL) + finrank Mat(r×H2) = (H0·r − r²) + r·H2 = nReg`.
  have hkerfin : finrank ℝ (LinearMap.ker ΛL) = H 0 * r - r * r := by
    have hrn := LinearMap.finrank_range_add_finrank_ker ΛL
    have hrangefull : finrank ℝ (LinearMap.range ΛL) = r * r := by
      rw [LinearMap.range_eq_top.mpr hΛLsurj, finrank_top]
      simp [Module.finrank_matrix, Module.finrank_self]
    have hdom : finrank ℝ (Matrix (Fin (H 0)) (Fin r) ℝ) = H 0 * r := by
      simp [Module.finrank_matrix, Module.finrank_self]
    omega
  -- `nReg = finrank (ker ΛL × Mat(r×H2)) ≤ finrank (range Ψ) ≤ finrank (range jointDiffL2)`.
  have hrH0 : r ≤ H 0 := by
    rw [← hUr]; exact le_trans (Matrix.rank_le_card_height U) (by rw [Fintype.card_fin])
  have hdomfin : finrank ℝ ((LinearMap.ker ΛL) × Matrix (Fin r) (Fin (H 2)) ℝ)
      = r * (H 0 + H 2 - r) := by
    rw [Module.finrank_prod, hkerfin]
    simp only [Module.finrank_matrix, Module.finrank_self, Fintype.card_fin, mul_one]
    -- `(H0·r − r²) + r·H2 = r·(H0 + H2 − r)`; `r ≤ H0` so the nat subtractions distribute.
    have h2 : r * r ≤ r * H 0 := Nat.mul_le_mul_left r hrH0
    have hc : H 0 * r = r * H 0 := mul_comm _ _
    rw [Nat.mul_sub, Nat.mul_add]; omega
  calc r * (H 0 + H 2 - r)
      = finrank ℝ ((LinearMap.ker ΛL) × Matrix (Fin r) (Fin (H 2)) ℝ) := hdomfin.symm
    _ ≤ finrank ℝ (LinearMap.range Ψ) := by
        rw [← LinearMap.finrank_range_of_inj hΨinj]
    _ ≤ finrank ℝ (LinearMap.range (jointDiffL2 H v)) := Submodule.finrank_mono hrange

/-! ## Step 1: the analytic flat-Jacobian gradient IS `jointDiffL2 ∘ flatSymm` (entry-wise)

The chart's first-block derivative `DG(0)` reads the banked analytic gradient
`prodAuxEntryDeriv … 2 i j` (`hasStrictFDerivAt_lossEntry`). To carry step 2b's rank bound onto the
chart, identify that gradient (applied to a flat tangent `δ`) with the `(i,j)` entry of
`jointDiffL2 H v (flatSymm δ)`. The `prodAuxEntryDeriv` fold is unrolled by the `rfl`-stated `_succ`
equation (a `rw`, not a `show`-unfold — the latter times out on the dependent-`Fin`-cast term). -/

/-- **The `prodAuxEntryDeriv` `succ` unfold** as a `rfl`-equation `rw` can fire (dodging the
`show`-elaboration timeout on the dependent-`Fin`-cast fold term). Local to the D1HChart lane. -/
theorem prodAuxEntryDeriv_succ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H) (x : X)
    (g' : ∀ (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)), X →L[ℝ] ℝ)
    (k : ℕ) (hk : k + 1 < L + 1) (i : Fin (H 0)) (j : Fin (H ⟨k + 1, hk⟩))
    (hk' : k < L + 1) (hkL : k < L)
    (e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc)
    (e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ) :
    prodAuxEntryDeriv H g x g' (k + 1) hk i j
      = ∑ m : Fin (H ⟨k, hk'⟩),
        ((prodAux H (g x) k hk' i m) • g' ⟨k, hkL⟩ (e1 ▸ m) (e2 ▸ j)
          + ((by rw [e1, e2]; exact g x ⟨k, hkL⟩ :
              Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ) m j)
            • prodAuxEntryDeriv H g x g' k hk' i m) := rfl

/-- `paramsEquivFlatLinear.symm` agrees with `paramsEquivFlat.symm` as a function. -/
theorem paramsEquivFlatLinear_symm_coe (H : Fin (2 + 1) → ℕ) :
    ⇑(paramsEquivFlatLinear H).symm = ⇑(paramsEquivFlat H).symm := by
  funext x; apply (paramsEquivFlat H).injective
  rw [(paramsEquivFlat H).apply_symm_apply]
  have : (paramsEquivFlat H) ((paramsEquivFlatLinear H).symm x)
      = (paramsEquivFlatLinear H) ((paramsEquivFlatLinear H).symm x) := by
    rw [paramsEquivFlatLinear_coe]
  rw [this, (paramsEquivFlatLinear H).apply_symm_apply]

/-- `gmapDeriv H s a b` applied to `δ` reads the `(s,a,b)` layer entry of the linear
flatten-inverse `(paramsEquivFlatLinear H).symm δ`. -/
theorem gmapDeriv_apply_symm (H : Fin (2 + 1) → ℕ) (s : Fin 2) (a : Fin (H s.castSucc))
    (b : Fin (H s.succ)) (δ : Fin (flatDim H) → ℝ) :
    (gmapDeriv H s a b) δ = ((paramsEquivFlatLinear H).symm δ) s a b := by
  have hL : (gmapDeriv H s a b) δ = δ (flatIdx H s a b) := rfl
  have hR : ((paramsEquivFlatLinear H).symm δ) s a b = δ (flatIdx H s a b) := by
    rw [paramsEquivFlatLinear_symm_coe, paramsEquivFlat_symm_entry]; rfl
  rw [hL, hR]

/-! ## Step 1 — the analytic flat-Jacobian gradient IS `jointDiffL2 ∘ flatSymm` (entry-wise)

The chart's first-block derivative reads the banked analytic gradient
`prodAuxEntryDeriv H (gmapAt H v) 0 gmapDeriv 2 i j` (`hasStrictFDerivAt_lossEntry` at `L = 2`,
`w₀ = 0`). To carry step 2b's rank bound onto the chart, identify that gradient (applied to a flat
tangent `δ`) with the `(i,j)` entry of `jointDiffL2 H v (flatSymm δ)` — the keystone `Dg(v)` of the
rank bound. The `prodAuxEntryDeriv` `L = 2` fold is unrolled by `prodAuxEntryDeriv_succ` (`rw` on a
`rfl`-equation, dodging the `show`-elaboration timeout): outer peel at `k = 1` then inner at `k = 0`
(`prodAux 0 = 1`, `prodAuxEntryDeriv 0 = 0`), giving `∑ x (v⁰ᵢₓ · δ¹ₓⱼ + v¹ₓⱼ · δ⁰ᵢₓ)` which is the
`jointDiffL2` entry `(δ⁰·v¹ + v⁰·δ¹)ᵢⱼ` after `Finset.sum_add_distrib` + `mul_comm`. -/

/-- `gmapAt H v 0 = v`: the flat-shift reconstruction at the origin recovers the base point. -/
theorem gmapAt_zero (H : Fin (L + 1) → ℕ) (v : Params H) : gmapAt H v 0 = v := by
  unfold gmapAt; rw [zero_add]; exact (paramsEquivFlat H).symm_apply_apply v

/-- The inner `k = 1` analytic gradient applied to `δ` reads a single `layer0` entry of the
flatten-inverse: `prodAuxEntryDeriv … 1 i m δ = (flatSymm δ)⁰ᵢₘ`. (`prodAux 0 = 1` collapses the
inner sum to the `i`-th term, `prodAuxEntryDeriv 0 = 0` kills the recursion, leaving the
`gmapDeriv 0` coordinate.) -/
theorem prodAuxEntryDeriv_one_apply_symm (H : Fin (2 + 1) → ℕ) (v : Params H) (i : Fin (H 0))
    (m : Fin (H 1)) (δ : Fin (flatDim H) → ℝ) :
    (prodAuxEntryDeriv H (gmapAt H v) 0 (fun s a b => gmapDeriv H s a b) 1
        (by norm_num) i m) δ = ((paramsEquivFlatLinear H).symm δ) 0 i m := by
  rw [prodAuxEntryDeriv_succ H (gmapAt H v) 0 (fun s a b => gmapDeriv H s a b) 0
        (by norm_num) i m (by norm_num) (by norm_num) (by apply Fin.ext; simp [Fin.castSucc])
        (by apply Fin.ext; simp [Fin.succ])]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, prodAuxEntryDeriv,
    ContinuousLinearMap.zero_apply, mul_zero, add_zero]
  have h0 : ∀ x : Fin (H 0),
      prodAux H (gmapAt H v 0) 0 (by norm_num) i x = (if i = x then 1 else 0) := fun x => rfl
  rw [Finset.sum_congr rfl (fun x _ => by rw [h0 x])]
  refine (Finset.sum_eq_single i ?_ ?_).trans ?_
  · intro b _ hb; rw [if_neg (fun h => hb h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h
  · rw [if_pos rfl, one_mul, gmapDeriv_apply_symm]; congr 1

/-- `prodAux H v 1 = layer0 H v`: the one-layer prefix product is the first layer (the
`prodAux_succ` reindex collapses to identity at the `rfl`-true width — `finCongr_refl` idiom). -/
theorem prodAux_one_eq_layer0 (H : Fin (2 + 1) → ℕ) (v : Params H) :
    prodAux H v 1 (by norm_num) = layer0 H v := by
  have e1 : H (⟨0, by norm_num⟩ : Fin (2 + 1)) = H ((⟨0, by norm_num⟩ : Fin 2).castSucc) := rfl
  have e2 : H (⟨0 + 1, by norm_num⟩ : Fin (2 + 1)) = H ((⟨0, by norm_num⟩ : Fin 2).succ) := rfl
  rw [prodAux_succ H v 0 (by norm_num) e1 e2]
  rw [show (finCongr e1.symm) = Equiv.refl _ from finCongr_refl _,
      show (finCongr e2.symm) = Equiv.refl _ from finCongr_refl _]
  erw [Matrix.reindex_refl_refl, Matrix.one_mul]
  rfl

/-- **The flat-analytic-Jacobian bridge** (Step 1). At an optimal base point `v` (`L = 2`), the
banked analytic loss-entry gradient `prodAuxEntryDeriv H (gmapAt H v) 0 gmapDeriv 2 i j` (the strict
derivative of `w ↦ (prod (gmapAt H v w))ᵢⱼ` at the flat origin, `hasStrictFDerivAt_lossEntry`),
applied to a flat tangent `δ`, equals the `(i,j)` entry of `jointDiffL2 H v` evaluated at the linear
flatten-inverse `(paramsEquivFlatLinear H).symm δ`. This ties the chart's first-block derivative to
the keystone `Dg(v)` whose rank ≥ `nReg` (`nReg_le_finrank_range_jointDiffL2`), so the flat Jacobian
inherits that rank bound (compose with the surjective flatten iso). -/
theorem prodAuxEntryDeriv_two_apply_eq_jointDiffL2 (H : Fin (2 + 1) → ℕ) (v : Params H)
    (i : Fin (H 0)) (j : Fin (H (Fin.last 2))) (δ : Fin (flatDim H) → ℝ) :
    (prodAuxEntryDeriv H (gmapAt H v) 0 (fun s a b => gmapDeriv H s a b) 2
        (Nat.lt_succ_self 2) i j) δ
      = (jointDiffL2 H v ((paramsEquivFlatLinear H).symm δ)) i j := by
  rw [prodAuxEntryDeriv_succ H (gmapAt H v) 0 (fun s a b => gmapDeriv H s a b) 1
        (Nat.lt_succ_self 2) i j (by norm_num) (by norm_num) (by apply Fin.ext; simp [Fin.castSucc])
        (by apply Fin.ext; simp [Fin.succ])]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  -- substitute the base point and the inner gradients
  rw [Finset.sum_congr rfl (fun x _ => by
    rw [gmapAt_zero, prodAuxEntryDeriv_one_apply_symm, gmapDeriv_apply_symm])]
  -- unfold the `jointDiffL2` entry and split the sum
  change _ = (layer0 H _ * layer1 H v + layer0 H v * layer1 H _) i j
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [show prodAux H v 1 (by norm_num) i x = layer0 H v i x from
    congrFun (congrFun (prodAux_one_eq_layer0 H v) i) x]
  -- the cast-layer is `layer1 v`, the `⟨1,_⟩`/`1` indices are defeq; match by `ring`
  change layer0 H v i x * (paramsEquivFlatLinear H).symm δ 1 x j
      + layer1 H v x j * (paramsEquivFlatLinear H).symm δ 0 i x
    = (paramsEquivFlatLinear H).symm δ 0 i x * layer1 H v x j
      + layer0 H v i x * (paramsEquivFlatLinear H).symm δ 1 x j
  ring

/-! ## #229 — the invertible `nReg`-minor of the flat Jacobian

The flat-Jacobian matrix `jacFlatL2 H v` represents the linear map `jointDiffL2 H v ∘ flatSymm`
(rows = loss entries `Fin H0 × Fin H2`, columns = flat coords `Fin (flatDim H)`). Its `(i,j)`-th row
is the analytic gradient `∇gᵢⱼ(0)` read off the flat tangents
(`jacFlatL2_apply_eq_lossEntryDeriv`, via Step 1). By the keystone rank bound
(`nReg_le_finrank_range_jointDiffL2`, transported through the
surjective flatten iso), `nReg ≤ jacFlatL2.rank`, so the banked determinantal-minor engine extracts
an invertible `nReg × nReg` minor (`exists_jacFlatL2_minor`). Its columns `ec` are the
**existentially-chosen** complement `W` of #230 (NEVER a fixed coordinate complement — the gate-4
trap), its rows `er` the selected loss entries. -/

/-- **The flat Jacobian matrix** `Dg(v) ∘ flatSymm` of the loss entries in flat coordinates: rows
indexed by loss entries `(i,j) : Fin H0 × Fin H2`, columns by flat input coords `Fin (flatDim H)`.
Defined as the `LinearMap.toMatrix` of `jointDiffL2 H v` precomposed with the linear flatten-inverse
(`Pi.basisFun` domain basis, `Matrix.stdBasis` codomain basis). -/
noncomputable def jacFlatL2 (H : Fin (2 + 1) → ℕ) (v : Params H) :
    Matrix (Fin (H 0) × Fin (H 2)) (Fin (flatDim H)) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin (flatDim H)))
    (Matrix.stdBasis ℝ (Fin (H 0)) (Fin (H 2)))
    ((jointDiffL2 H v).comp ((paramsEquivFlatLinear H).symm.toLinearMap))

/-- The `(ij, c)` entry of `jacFlatL2` is `jointDiffL2 H v` at the `c`-th flat basis tangent. -/
theorem jacFlatL2_apply (H : Fin (2 + 1) → ℕ) (v : Params H) (ij : Fin (H 0) × Fin (H 2))
    (c : Fin (flatDim H)) :
    jacFlatL2 H v ij c
      = (jointDiffL2 H v ((paramsEquivFlatLinear H).symm (Pi.single c 1))) ij.1 ij.2 := by
  rw [jacFlatL2, LinearMap.toMatrix_apply]
  simp only [Pi.basisFun_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rfl

/-- **The flat-Jacobian entry IS the analytic loss-entry gradient** (Step-1 tie). The `(i,j)`-th row
of `jacFlatL2`, read at the `c`-th flat basis tangent, equals the banked analytic gradient
`prodAuxEntryDeriv … 2 i j` applied there — so the minor of `jacFlatL2` and the chart's first-block
derivative agree (the bridge #230 consumes). -/
theorem jacFlatL2_apply_eq_lossEntryDeriv (H : Fin (2 + 1) → ℕ) (v : Params H)
    (i : Fin (H 0)) (j : Fin (H (Fin.last 2))) (c : Fin (flatDim H)) :
    jacFlatL2 H v (i, j) c
      = (prodAuxEntryDeriv H (gmapAt H v) 0 (fun s a b => gmapDeriv H s a b) 2
          (Nat.lt_succ_self 2) i j) (Pi.single c 1) := by
  rw [jacFlatL2_apply, ← prodAuxEntryDeriv_two_apply_eq_jointDiffL2 H v i j (Pi.single c 1)]

/-- **`nReg ≤ jacFlatL2.rank`.** The flat-Jacobian rank equals
`finrank (range (jointDiffL2 ∘ flatSymm)) = finrank (range jointDiffL2)` (precompose the surjective
flatten iso; `rank_eq_finrank_range_toLin` + `toLin_toMatrix`), so the keystone bound transfers. -/
theorem nReg_le_jacFlatL2_rank (H : Fin (2 + 1) → ℕ) (r : ℕ) (v : Params H)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ)
    (hopt : prod H v = B) (hr : B.rank = r) :
    r * (H 0 + H 2 - r) ≤ (jacFlatL2 H v).rank := by
  classical
  have hbridge : (jacFlatL2 H v).rank
      = finrank ℝ (LinearMap.range ((jointDiffL2 H v).comp
          ((paramsEquivFlatLinear H).symm.toLinearMap))) := by
    rw [jacFlatL2, Matrix.rank_eq_finrank_range_toLin _
      (Matrix.stdBasis ℝ (Fin (H 0)) (Fin (H 2)))
      (Pi.basisFun ℝ (Fin (flatDim H))), Matrix.toLin_toMatrix]
  have hrangeeq : LinearMap.range ((jointDiffL2 H v).comp
        ((paramsEquivFlatLinear H).symm.toLinearMap))
      = LinearMap.range (jointDiffL2 H v) := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  rw [hbridge, hrangeeq]
  have hkey := nReg_le_finrank_range_jointDiffL2 H r v B hopt hr
  rw [show H (Fin.last 2) = H 2 from rfl] at hkey
  exact hkey

/-- From `m ≤ A.rank`, an invertible `m × m` minor of `A` (index maps `er, ec` injective). Wraps the
banked engine `exists_submatrix_det_ne_zero_of_le_rank` and handles `m = 0` (the empty minor has
`det = 1`). Generic over a real matrix; lifted to the flat Jacobian below. -/
theorem exists_minor_of_le_rank {p q m : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) (hm : m ≤ A.rank) :
    ∃ (er : Fin m → Fin p) (ec : Fin m → Fin q),
      Function.Injective er ∧ Function.Injective ec ∧ (A.submatrix er ec).det ≠ 0 := by
  classical
  cases m with
  | zero =>
      refine ⟨Fin.elim0, Fin.elim0, fun a => a.elim0, fun a => a.elim0, ?_⟩
      rw [Matrix.det_eq_one_of_card_eq_zero (by simp)]; exact one_ne_zero
  | succ k => exact DLNFibre.Core.exists_submatrix_det_ne_zero_of_le_rank A hm

/-- **#229 — the invertible `nReg`-minor of the flat Jacobian.** At an optimal `v` (`prod v = B`,
`rank B = r`), there are injective index maps `er` (selected loss entries) and `ec` (selected flat
input coords) with `det (jacFlatL2.submatrix er ec) ≠ 0`. The `nReg` columns `ec` are the
existentially-chosen complement `W` for the #230 chart (NEVER a fixed coordinate complement). -/
theorem exists_jacFlatL2_minor (H : Fin (2 + 1) → ℕ) (r : ℕ) (v : Params H)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ)
    (hopt : prod H v = B) (hr : B.rank = r) :
    ∃ (er : Fin (r * (H 0 + H 2 - r)) → Fin (H 0) × Fin (H 2))
      (ec : Fin (r * (H 0 + H 2 - r)) → Fin (flatDim H)),
      Function.Injective er ∧ Function.Injective ec ∧
      ((jacFlatL2 H v).submatrix er ec).det ≠ 0 := by
  classical
  set ι := Fin (H 0) × Fin (H 2) with hι
  set eι : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with heι
  set A' : Matrix (Fin (Fintype.card ι)) (Fin (flatDim H)) ℝ :=
    (jacFlatL2 H v).submatrix eι id with hA'
  have hrankA' : (jacFlatL2 H v).rank ≤ A'.rank := by
    rw [hA', show ((jacFlatL2 H v).submatrix eι id)
        = (jacFlatL2 H v).submatrix eι (Equiv.refl _) from rfl,
      Matrix.rank_submatrix (jacFlatL2 H v) eι (Equiv.refl _)]
  have hbound : r * (H 0 + H 2 - r) ≤ A'.rank :=
    le_trans (nReg_le_jacFlatL2_rank H r v B hopt hr) hrankA'
  obtain ⟨er, ec, her, hec, hdet⟩ := exists_minor_of_le_rank A' hbound
  refine ⟨eι ∘ er, ec, eι.injective.comp her, hec, ?_⟩
  have hsub : A'.submatrix er ec = (jacFlatL2 H v).submatrix (eι ∘ er) ec := by
    rw [hA', Matrix.submatrix_submatrix]; rfl
  rw [← hsub]; exact hdet

end DLNFibre.DLN.RLCT
