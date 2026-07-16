import DLNFibre.DLN.RLCT.Validate.RouteMSJRankRCodim
import DLNFibre.DLN.RLCT.Validate.RouteMSJGoodChart

set_option linter.style.longLine false

/-!
# `RouteMSJInteriorLoss` — the interior-cell per-`p` loss finiteness (rank lemma + box-RLCT instantiation)

**Thread `genm-intloss` (aoyagi-full Stage 2/3a) — the INTERIOR loss side of the (□) discharge.**
After arch1build's front-charge factorization, the interior arm's loss factor is the per-`p` integral
`I_loss(p) = ∫_x (E_top(x) + E_tr(x))^{−q}`, `q = c'−ab/2`, over the outer box. On the interior cell the
loss DECOUPLES (couplerad §w3-interior): `E_top = frobSq(P·Q_inl + B₁₂·Q_inr) = frobSq([P|B₁₂]·S)`
(`S = [Q_inl;Q_inr]`) and `E_tr = frobSq(C·Q_inl·(1−Π)) = frobSq(C·K)` (`K = Q_inl·(1−Π)`, `Π` the
row-projector of `Q_inr`, using `Q_inr·(1−Π) = 0`). As a PSD quadratic in `(W=[P|B₁₂], C)` the loss has
rank `u·rank S + a·rank K`, so the banked box-RLCT atom
(`RouteMSJRankRCodim.lintegral_cube_frobSq_neg_of_finrank_range` / `twoMatBox_rankR_lintegral_lt_top`)
gives finiteness for `2q < u·rank S + a·rank K`.

## What lands here (network-free)

* **`matMulRight`** (`X ↦ X * A`) as a `LinearMap` on the raw matrix (pi) type, `= compLeft (mulVecLin Aᵀ)`.
* **`finrank_pi_submodule_const`** — `finrank (Submodule.pi univ (fun _:ι => W)) = card ι · finrank W`
  (via the explicit product equiv). The `Submodule.pi` finrank Mathlib v4.29 lacks.
* **`finrank_range_matMulRight`** — the CRUX (genuinely new; Mathlib v4.29 has NO `rank_kronecker`):
  `finrank (range (X ↦ X * A)) = (#rows) · A.rank`, `X : Matrix (Fin r) (Fin c)`, `A : Matrix (Fin c) (Fin d)`.
  Route: `X↦X*A = compLeft (mulVecLin Aᵀ) (Fin r)`; `range_compLeft` = `Submodule.pi univ (fun _ => range)`;
  `finrank_pi_submodule_const` + `Matrix.rank Aᵀ = rank A`.
* **`lossMapₗ` / `finrank_range_lossMapₗ`** — the block-diagonal loss map `(W, C) ↦ (W·S, C·K)` and its
  rank `rW·rank S + rC·rank K` (via `range_prodMap` + `finrank_prodSubmodule` + the crux, twice).
* **`sum_sq_matFlatL` / `sum_sq_twoMatFlatL`** — the flatten preserves the squared-sum:
  `∑ (twoMatFlatL (M₁,M₂))² = frobSq M₁ + frobSq M₂` (entry reindex `finProdFinEquiv`/`finSumFinEquiv`).
* **`interiorLoss_twoMat_lt_top`** — the deliverable: `∫_{box} (frobSq(W·S)+frobSq(C·K))^{−q} < ⊤` for
  `2q < rW·rank S + rC·rank K`, the box-RLCT of the interior loss PSD quadratic. Pure instantiation of the
  banked `twoMatBox_rankR_lintegral_lt_top` at `L = interiorLossL S K`. The PER-`p` finiteness brick:
  the value is NOT p-uniform (it blows up as `[Q_inl;Q_inr]` degenerates); the coupled `∫_p charge·loss`
  is the separate boundary estimate (couplerad's joint resolution), NOT this file.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory Set
open scoped ENNReal BigOperators

/-! ## `Submodule.pi` finrank (constant fibre) -/

/-- **The constant-fibre `Submodule.pi` product equiv** `Submodule.pi univ (fun _ => W) ≃ₗ (ι → W)`. -/
noncomputable def piSubmoduleConstEquiv {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {ι : Type*} (W : Submodule R M) :
    (Submodule.pi (Set.univ : Set ι) (fun _ => W)) ≃ₗ[R] (ι → W) where
  toFun x i := ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
  map_add' x y := rfl
  map_smul' c x := rfl
  invFun y := ⟨fun i => (y i : M), fun i _ => (y i).2⟩
  left_inv x := by ext i; rfl
  right_inv y := by ext i; rfl

/-- **The constant-fibre `Submodule.pi` finrank** `finrank (Submodule.pi univ (fun _ => W)) = card ι · finrank W`. -/
theorem finrank_pi_submodule_const {R M : Type*} [Ring R] [StrongRankCondition R]
    [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι] (W : Submodule R M)
    [Module.Free R W] [Module.Finite R W] :
    Module.finrank R (Submodule.pi (Set.univ : Set ι) (fun _ => W)) = Fintype.card ι * Module.finrank R W := by
  rw [(piSubmoduleConstEquiv (ι := ι) W).finrank_eq, Module.finrank_pi_fintype,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **The submodule-product equiv** `↥(V.prod W) ≃ₗ ↥V × ↥W`. -/
noncomputable def prodSubmoduleEquiv {R M M' : Type*} [Ring R] [AddCommGroup M] [AddCommGroup M']
    [Module R M] [Module R M'] (V : Submodule R M) (W : Submodule R M') :
    (V.prod W) ≃ₗ[R] (V × W) where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨(y.1.1, y.2.1), y.1.2, y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The submodule-product finrank** `finrank ↥(V.prod W) = finrank ↥V + finrank ↥W` (over `ℝ`). -/
theorem finrank_prodSubmodule {M M' : Type*}
    [AddCommGroup M] [AddCommGroup M'] [Module ℝ M] [Module ℝ M']
    (V : Submodule ℝ M) (W : Submodule ℝ M') [Module.Finite ℝ V] [Module.Finite ℝ W] :
    Module.finrank ℝ (V.prod W) = Module.finrank ℝ V + Module.finrank ℝ W := by
  rw [(prodSubmoduleEquiv V W).finrank_eq, Module.finrank_prod]

/-! ## The `X ↦ X * A` linear map and its range rank -/

/-- **Right-multiplication by `A`** as a linear map on the raw matrix (pi) type. -/
noncomputable def matMulRight {r c d : ℕ} (A : Matrix (Fin c) (Fin d) ℝ) :
    (Fin r → Fin c → ℝ) →ₗ[ℝ] (Fin r → Fin d → ℝ) :=
  LinearMap.compLeft (Matrix.mulVecLin Aᵀ) (Fin r)

/-- **Entrywise form** `(matMulRight A X) i j = ∑ₖ X i k · A k j` (the `X * A` product, entrywise). -/
theorem matMulRight_apply {r c d : ℕ} (A : Matrix (Fin c) (Fin d) ℝ) (X : Fin r → Fin c → ℝ)
    (i : Fin r) (j : Fin d) :
    matMulRight (r := r) A X i j = ∑ k, X i k * A k j := by
  have hcoe : matMulRight (r := r) A X i = Matrix.mulVecLin Aᵀ (X i) := rfl
  rw [hcoe, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl (fun k _ => by rw [Matrix.transpose_apply]; ring)

/-- **The crux rank identity** `finrank (range (X ↦ X * A)) = r · A.rank`
(`X : Matrix (Fin r) (Fin c)`, `A : Matrix (Fin c) (Fin d)`). Genuinely new — Mathlib v4.29 lacks
`rank_kronecker`. -/
theorem finrank_range_matMulRight {r c d : ℕ} (A : Matrix (Fin c) (Fin d) ℝ) :
    Module.finrank ℝ (LinearMap.range (matMulRight (r := r) A)) = r * A.rank := by
  rw [matMulRight, LinearMap.range_compLeft, finrank_pi_submodule_const, Fintype.card_fin]
  congr 1
  exact Matrix.rank_transpose A

/-- **The block-diagonal loss-map** `(W, C) ↦ (W * S, C * K)` — right-mult by `S` on the first block,
by `K` on the second (the interior-cell loss as a linear map in `(W, C)`). -/
noncomputable def lossMapₗ {rW cW rC cC n : ℕ}
    (S : Matrix (Fin cW) (Fin n) ℝ) (K : Matrix (Fin cC) (Fin n) ℝ) :
    ((Fin rW → Fin cW → ℝ) × (Fin rC → Fin cC → ℝ)) →ₗ[ℝ]
      ((Fin rW → Fin n → ℝ) × (Fin rC → Fin n → ℝ)) :=
  (matMulRight (r := rW) S).prodMap (matMulRight (r := rC) K)

/-- **The loss-map rank** `finrank (range (lossMapₗ S K)) = rW · rank S + rC · rank K` — the interior-cell
loss quadratic's rank as a PSD form in `(W, C)`. Block-diagonal ⟹ `range = prod`, `finrank = sum`; each
block via `finrank_range_matMulRight`. -/
theorem finrank_range_lossMapₗ {rW cW rC cC n : ℕ}
    (S : Matrix (Fin cW) (Fin n) ℝ) (K : Matrix (Fin cC) (Fin n) ℝ) :
    Module.finrank ℝ (LinearMap.range (lossMapₗ (rW := rW) (rC := rC) S K))
      = rW * S.rank + rC * K.rank := by
  rw [lossMapₗ, LinearMap.range_prodMap, finrank_prodSubmodule,
    finrank_range_matMulRight, finrank_range_matMulRight]

/-- `matMulRight A X = (Matrix.of X) * A` (the pi-form right-mult IS the matrix product). -/
theorem matMulRight_eq_mul {r c d : ℕ} (A : Matrix (Fin c) (Fin d) ℝ) (X : Fin r → Fin c → ℝ) :
    matMulRight (r := r) A X = (Matrix.of X) * A := by
  funext i j
  rw [matMulRight_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl (fun k _ => by rw [Matrix.of_apply])

/-! ## The flatten sum-of-squares identities -/

/-- **`∑ (matFlatL M)² = frobSq M`** — the flatten is an entry reindex, so the squared-sum is preserved. -/
theorem sum_sq_matFlatL (p q : ℕ) (M : Fin p → Fin q → ℝ) :
    ∑ i, (matFlatL p q M i) ^ 2 = frobSq M := by
  simp_rw [matFlatL_apply]
  rw [Equiv.sum_comp (finProdFinEquiv (m := p) (n := q)).symm
      (fun ab : Fin p × Fin q => (M ab.1 ab.2) ^ 2)]
  rw [Fintype.sum_prod_type]
  rfl

/-- **`∑ (twoMatFlatL (M₁,M₂))² = frobSq M₁ + frobSq M₂`** — the two-block flatten preserves the total
squared-sum, splitting it into the two per-block Frobenius norms. -/
theorem sum_sq_twoMatFlatL (p q r s : ℕ) (x : (Fin p → Fin q → ℝ) × (Fin r → Fin s → ℝ)) :
    ∑ j, (twoMatFlatL p q r s x j) ^ 2 = frobSq x.1 + frobSq x.2 := by
  simp_rw [twoMatFlatL_apply]
  rw [Equiv.sum_comp (finSumFinEquiv (m := p * q) (n := r * s)).symm
      (fun k => (Sum.elim (matFlatL p q x.1) (matFlatL r s x.2) k) ^ 2)]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [sum_sq_matFlatL, sum_sq_matFlatL]

/-! ## The interior-cell per-`p` loss finiteness -/

/-- **The interior-cell loss linear map on the flat cube coordinates** `L = outFlat ∘ lossMapₗ ∘ inFlat⁻¹`
(`inFlat`, `outFlat` the input/output two-matrix flattens), so `∑ⱼ (L (inFlat (W,C)) j)² = frobSq(W·S)+frobSq(C·K)`
and `finrank(range L) = rW·rank S + rC·rank K`. -/
noncomputable def interiorLossL {rW cW rC cC n : ℕ}
    (S : Matrix (Fin cW) (Fin n) ℝ) (K : Matrix (Fin cC) (Fin n) ℝ) :
    (Fin (rW * cW + rC * cC) → ℝ) →ₗ[ℝ] (Fin (rW * n + rC * n) → ℝ) :=
  (twoMatFlatL rW n rC n).toLinearMap ∘ₗ (lossMapₗ (rW := rW) (rC := rC) S K) ∘ₗ
    ((twoMatFlatL rW cW rC cC).symm : (Fin (rW * cW + rC * cC) → ℝ) →ₗ[ℝ] _)

/-- **The interior-cell per-`p` loss finiteness (box-RLCT instantiation).** For the interior loss
`frobSq(W·S) + frobSq(C·K)` (`W`, `C` over the unit box), the integral of its `−q` power is finite below
the sharp rank threshold `2q < rW·rank S + rC·rank K` — the box-RLCT of the loss PSD quadratic. Pure
instantiation of the banked `twoMatBox_rankR_lintegral_lt_top` at `L = interiorLossL S K`
(rank `finrank_range_lossMapₗ`, integrand identity `sum_sq_twoMatFlatL`). -/
theorem interiorLoss_twoMat_lt_top {rW cW rC cC n : ℕ} [NeZero (rW * cW + rC * cC)]
    (S : Matrix (Fin cW) (Fin n) ℝ) (K : Matrix (Fin cC) (Fin n) ℝ)
    {q : ℝ} (hq0 : 0 ≤ q) (hq : 2 * q < (rW * S.rank + rC * K.rank : ℕ)) :
    ∫⁻ x in matBox rW cW 1 ×ˢ matBox rC cC 1,
        ENNReal.ofReal ((frobSq (Matrix.of x.1 * S) + frobSq (Matrix.of x.2 * K)) ^ (-q)) < ⊤ := by
  classical
  set E := (twoMatFlatL rW cW rC cC).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv with hE_def
  have hEcoe : (E : ((Fin rW → Fin cW → ℝ) × (Fin rC → Fin cC → ℝ)) → (Fin (rW * cW + rC * cC) → ℝ))
      = ⇑(twoMatFlatL rW cW rC cC) := rfl
  have hEmp : MeasurePreserving E
      (volume : Measure ((Fin rW → Fin cW → ℝ) × (Fin rC → Fin cC → ℝ)))
      (volume : Measure (Fin (rW * cW + rC * cC) → ℝ)) := by
    refine ⟨E.measurable, ?_⟩
    have := (measurePreserving_twoMatFlatL rW cW rC cC).map_eq
    rwa [← hEcoe] at this
  have hbox : matBox rW cW 1 ×ˢ matBox rC cC 1
      = E ⁻¹' Set.univ.pi (fun _ : Fin (rW * cW + rC * cC) => Set.Icc (-1 : ℝ) 1) := by
    rw [hEcoe]; exact twoMatFlatL_box_preimage rW cW rC cC
  set L := interiorLossL (rW := rW) (rC := rC) S K with hL_def
  -- the rank of `L` equals the loss quadratic's rank
  have hLrank : Module.finrank ℝ (LinearMap.range L) = rW * S.rank + rC * K.rank := by
    rw [hL_def, interiorLossL, LinearMap.range_comp, LinearMap.range_comp,
      LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq, finrank_range_lossMapₗ]
  -- the integrand identity `∑ⱼ (L (E x) j)² = frobSq(W·S) + frobSq(C·K)`
  have hpt : ∀ x : (Fin rW → Fin cW → ℝ) × (Fin rC → Fin cC → ℝ),
      ∑ j, (L (E x) j) ^ 2
        = frobSq (Matrix.of x.1 * S) + frobSq (Matrix.of x.2 * K) := by
    intro x
    have hEx : (E x : Fin (rW * cW + rC * cC) → ℝ) = twoMatFlatL rW cW rC cC x := congrFun hEcoe x
    have hLEx : L (E x) = twoMatFlatL rW n rC n (matMulRight S x.1, matMulRight K x.2) := by
      rw [hEx, hL_def, interiorLossL]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        lossMapₗ, LinearMap.prodMap_apply]
    rw [hLEx, sum_sq_twoMatFlatL, matMulRight_eq_mul, matMulRight_eq_mul]
  -- assemble
  have hc' : q < (rW * S.rank + rC * K.rank : ℕ) / 2 := by
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]; linarith
  have hmeas : MeasurableSet (matBox rW cW 1 ×ˢ matBox rC cC 1) :=
    (matBox_measurableSet rW cW 1).prod (matBox_measurableSet rC cC 1)
  have hEqOn : Set.EqOn
      (fun x : (Fin rW → Fin cW → ℝ) × (Fin rC → Fin cC → ℝ) =>
        ENNReal.ofReal ((frobSq (Matrix.of x.1 * S) + frobSq (Matrix.of x.2 * K)) ^ (-q)))
      (fun x => ENNReal.ofReal ((∑ j, (L (E x) j) ^ 2) ^ (-q)))
      (matBox rW cW 1 ×ˢ matBox rC cC 1) :=
    fun x _ => by simp only [hpt x]
  rw [setLIntegral_congr_fun hmeas hEqOn]
  exact twoMatBox_rankR_lintegral_lt_top E hEmp hbox L hLrank hq0 hc'

/-- **Non-vacuity witness.** At unit widths with identity `S = K = 1` (rank `1` each, threshold `2q < 2`)
and `q = 0`, the hypotheses of `interiorLoss_twoMat_lt_top` are jointly satisfiable — not vacuous. -/
example : True := by
  haveI : NeZero (1 * 1 + 1 * 1) := ⟨by norm_num⟩
  have _ := interiorLoss_twoMat_lt_top (rW := 1) (cW := 1) (rC := 1) (cC := 1) (n := 1)
    (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) (q := 0) (le_refl 0)
    (by simp [Matrix.rank_one])
  trivial

end DLNFibre.DLN.RLCT
