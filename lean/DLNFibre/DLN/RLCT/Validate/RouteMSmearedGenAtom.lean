import DLNFibre.DLN.RLCT.Validate.RouteMSmearedChartL2
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedProjCancel

/-!
# `RouteMSmearedGenAtom` — the general-`L` smeared chart-eval `prod M chart = z•(P₁·H̄)`

The general-`L` (`0 < L`, arbitrary depth) discharge of the chart-eval, generalizing the L=2
`prod_chartL2Params` (`RouteMSmearedChartL2`) to a front PRODUCT of layers rather than a single `A⁰`.
(At `L = 1` the front product is definitionally `prodAux M A 0 = 1`, so the collapse still holds;
the SMEARED branch it feeds is gated on `2 ≤ L`, but the algebra here needs only `0 < L`.)

The deepest factor `A^{L−1}` (size `M_{L−1} × M_L`) is row-split via `deepWidthEquiv (r + s = M_{L−1})`
exactly as at L=2 (top `r` rows the radial-minus-shear `z·H̄ − Λ₀·S_bot`, bottom `s` rows the residual
`S_bot`). The ONLY thing `L ≥ 3` adds over L=2: the front factor is `frontProd M A := prodAux M A (L−1)`
(the prefix product `A⁰·…·A^{L−2}`, size `M 0 × M_{L−1}`), a PRODUCT of several layers, not the single
free `A⁰`. The last-layer peel `prod M A = frontProd M A · A^{L−1}` (native, `prodAux_succ` at `k = L−1`)
plus the SAME single `deepWidthEquiv` sum-reindex + `deepBlock_collapse` collapse gives the identical rate.

* `frontProd M A` — the prefix product `prodAux M A (L−1)`, size `M 0 × M ⟨L−1,_⟩`.
* `prod_eq_frontProd_mul_deep` — the last-layer peel `prod M A = frontProd M A · (reindex … (A ⟨L−1⟩))`.
* `chartGenDeep` / `chartGenParamsFrom` — the deepest factor row-split + the chart `Params` from a given
  free front product `A⁰..A^{L−2}` and the deep-factor data (`z`, `H̄`, `S_bot`, `Λ₀`).
* `prod_chartGen_collapse` — the general-`L` chart-eval `prod M chart = z • (P₁·H̄)`, off the shear
  cancellation `P₁·Λ₀ = P₂`, with `P₁ = frontProd[:, top r]`, `P₂ = frontProd[:, residual s]`.

This is the pure-algebra heart; the flat-coordinate decode (the `slotEquiv`/`packM`/`shearMBody`
transport at `L` layers) and the det-nondegeneracy are the downstream steps.
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The front product `frontProd = prodAux (L−1)` + the last-layer peel -/

/-- **The front product** `frontProd M A := prodAux M A (L−1)`, the prefix product `A⁰·A¹·…·A^{L−2}` of
size `M 0 × M ⟨L−1,_⟩`. At `L = 2` (`L−1 = 1`) this is the single free `A⁰` (`prodAux M A 1`). -/
noncomputable def frontProd (M : Fin (L + 1) → ℕ) (A : Params M) (hL : 0 < L) :
    Matrix (Fin (M 0)) (Fin (M ⟨L - 1, by omega⟩)) ℝ :=
  prodAux M A (L - 1) (by omega)

/-- `prodAux` transports across a nat-index equality `k = k'` as a `HEq` (the value depends only on the
nat; the `< L + 1` proof is irrelevant, but the result TYPE `Fin (M ⟨k, _⟩)` shifts with `k`). By `subst`
on the nat equality. -/
theorem prodAux_nat_hcongr (M : Fin (L + 1) → ℕ) (A : Params M) {k k' : ℕ} (hkk : k = k')
    (hk : k < L + 1) (hk' : k' < L + 1) :
    HEq (prodAux M A k hk) (prodAux M A k' hk') := by
  subst hkk; rw [Subsingleton.elim hk hk']

/-- **The last-layer peel** `prod M A = frontProd M A · (reindex … (A ⟨L−1⟩))`. The native
`prodAux_succ` at `k = L−1` (`prod = prodAux L`, `frontProd = prodAux (L−1)`), with the width casts
`e1 : M ⟨L−1⟩ = M (⟨L−1⟩ : Fin L).castSucc` and `e2 : M (last L) = M (⟨L−1⟩ : Fin L).succ`. -/
theorem prod_eq_frontProd_mul_deep (M : Fin (L + 1) → ℕ) (A : Params M) (hL : 0 < L)
    (e1 : M (⟨L - 1, Nat.sub_lt_succ L 1⟩ : Fin (L + 1))
        = M ((⟨L - 1, Nat.sub_lt hL Nat.one_pos⟩ : Fin L).castSucc))
    (e2 : M (Fin.last L) = M ((⟨L - 1, Nat.sub_lt hL Nat.one_pos⟩ : Fin L).succ)) :
    prod M A = frontProd M A hL
      * Matrix.reindex (finCongr e1.symm) (finCongr e2.symm)
          (A (⟨L - 1, Nat.sub_lt hL Nat.one_pos⟩ : Fin L)) := by
  -- destructure `L = n + 1` so `L − 1 = n` reduces syntactically (`(L−1)+1 = L`, no propositional cast)
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at e1 e2 ⊢
  -- now `frontProd = prodAux M A n`, `prod = prodAux M A (n+1)`; peel at `k = n` (`(n+1)−1 = n` defeq)
  rw [prod, prodAux_succ M A n (Nat.lt_succ_self (n + 1)) e1 e2, frontProd]
  rfl

/-! ## The general-`L` chart `Params` (front layers free, deepest factor row-split) -/

/-- **The general-`L` chart deepest factor** `A^{L−1} : Matrix (Fin (M ⟨L−1⟩)) (Fin (M (last L))) ℝ`,
row-split via `deepWidthEquiv (r + s = M ⟨L−1⟩)`: a row lands in the top `r` block (radial-minus-shear
`z·H̄ − Λ₀·S_bot`) or the bottom `s` block (residual `S_bot`). The `L`-indexed analog of `chartL2Deep`
(there the deepest width is `M 1`; here `M ⟨L−1⟩`). -/
noncomputable def chartGenDeep (M : Fin (L + 1) → ℕ) (hL : 0 < L) {r s : ℕ}
    (hrs : r + s = M (⟨L - 1, by omega⟩ : Fin (L + 1)))
    (z : ℝ) (Hbar : Matrix (Fin r) (Fin (M (Fin.last L))) ℝ)
    (Sbot : Matrix (Fin s) (Fin (M (Fin.last L))) ℝ) (Λ₀ : Matrix (Fin r) (Fin s) ℝ) :
    Matrix (Fin (M (⟨L - 1, by omega⟩ : Fin (L + 1)))) (Fin (M (Fin.last L))) ℝ :=
  fun k j => deepBlock z Hbar Sbot Λ₀ ((deepWidthEquiv hrs).symm k) j

/-- **The general-`L` chart `Params`** from a free front tuple `A` (only layers `0..L−2` are read) with
its deepest layer `L−1` overridden by `chartGenDeep`. Reindexes `chartGenDeep` (at widths
`M ⟨L−1⟩ × M (last L)`) into the layer `L−1` type `M (⟨L−1⟩:Fin L).castSucc × M (⟨L−1⟩:Fin L).succ` via
the `rfl`-true width equalities `e1`/`e2`. -/
noncomputable def chartGenParams (M : Fin (L + 1) → ℕ) (A : Params M) (hL : 0 < L) {r s : ℕ}
    (hrs : r + s = M (⟨L - 1, by omega⟩ : Fin (L + 1)))
    (z : ℝ) (Hbar : Matrix (Fin r) (Fin (M (Fin.last L))) ℝ)
    (Sbot : Matrix (Fin s) (Fin (M (Fin.last L))) ℝ) (Λ₀ : Matrix (Fin r) (Fin s) ℝ)
    (e1 : M (⟨L - 1, by omega⟩ : Fin (L + 1)) = M ((⟨L - 1, by omega⟩ : Fin L).castSucc))
    (e2 : M (Fin.last L) = M ((⟨L - 1, by omega⟩ : Fin L).succ)) : Params M :=
  Function.update A (⟨L - 1, by omega⟩ : Fin L)
    (Matrix.reindex (finCongr e1) (finCongr e2) (chartGenDeep M hL hrs z Hbar Sbot Λ₀))

/-- **`prodAux` reads only layers `< k`.** If `A t = A' t` for every layer `t : Fin L` with `t.val < k`,
then `prodAux M A k = prodAux M A' k`. By induction on `k` (the `prodAux_succ` step reads only layer `k`,
which is `< k+1`). -/
theorem prodAux_congr_lt (M : Fin (L + 1) → ℕ) (A A' : Params M) :
    ∀ (k : ℕ) (hk : k < L + 1),
      (∀ t : Fin L, t.val < k → A t = A' t) → prodAux M A k hk = prodAux M A' k hk := by
  intro k
  induction k with
  | zero => intro hk _; rfl
  | succ k ih =>
      intro hk hagree
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : M (⟨k, hk'⟩ : Fin (L + 1)) = M ((⟨k, hkL⟩ : Fin L).castSucc) := by
        apply congrArg; apply Fin.ext; simp [Fin.castSucc]
      have e2 : M (⟨k + 1, hk⟩ : Fin (L + 1)) = M ((⟨k, hkL⟩ : Fin L).succ) := by
        apply congrArg; apply Fin.ext; simp [Fin.succ]
      rw [prodAux_succ M A k hk e1 e2, prodAux_succ M A' k hk e1 e2]
      rw [ih hk' (fun t ht => hagree t (by omega))]
      rw [hagree ⟨k, hkL⟩ (by simp)]

/-- The front product of the chart equals the front product of `A` (the chart only overrides layer
`L−1`, which `frontProd = prodAux (L−1)` never reads). -/
theorem frontProd_chartGenParams (M : Fin (L + 1) → ℕ) (A : Params M) (hL : 0 < L) {r s : ℕ}
    (hrs : r + s = M (⟨L - 1, by omega⟩ : Fin (L + 1)))
    (z : ℝ) (Hbar : Matrix (Fin r) (Fin (M (Fin.last L))) ℝ)
    (Sbot : Matrix (Fin s) (Fin (M (Fin.last L))) ℝ) (Λ₀ : Matrix (Fin r) (Fin s) ℝ)
    (e1 : M (⟨L - 1, by omega⟩ : Fin (L + 1)) = M ((⟨L - 1, by omega⟩ : Fin L).castSucc))
    (e2 : M (Fin.last L) = M ((⟨L - 1, by omega⟩ : Fin L).succ)) :
    frontProd M (chartGenParams M A hL hrs z Hbar Sbot Λ₀ e1 e2) hL = frontProd M A hL := by
  rw [frontProd, frontProd]
  -- `prodAux M · (L−1)` reads only layers `0..L−2`; the chart overrides only layer `L−1`.
  refine prodAux_congr_lt M _ A (L - 1) (by omega) (fun t ht => ?_)
  rw [chartGenParams, Function.update_of_ne]
  intro h; rw [h] at ht; simp only at ht; omega

/-- The chart's deepest layer, transported through the peel's reindex, is `chartGenDeep` (the double
`reindex e.symm ∘ reindex e` collapse). -/
theorem chartGenParams_deep_layer (M : Fin (L + 1) → ℕ) (A : Params M) (hL : 0 < L) {r s : ℕ}
    (hrs : r + s = M (⟨L - 1, by omega⟩ : Fin (L + 1)))
    (z : ℝ) (Hbar : Matrix (Fin r) (Fin (M (Fin.last L))) ℝ)
    (Sbot : Matrix (Fin s) (Fin (M (Fin.last L))) ℝ) (Λ₀ : Matrix (Fin r) (Fin s) ℝ)
    (e1 : M (⟨L - 1, by omega⟩ : Fin (L + 1)) = M ((⟨L - 1, by omega⟩ : Fin L).castSucc))
    (e2 : M (Fin.last L) = M ((⟨L - 1, by omega⟩ : Fin L).succ)) :
    Matrix.reindex (finCongr e1.symm) (finCongr e2.symm)
        ((chartGenParams M A hL hrs z Hbar Sbot Λ₀ e1 e2) (⟨L - 1, by omega⟩ : Fin L))
      = chartGenDeep M hL hrs z Hbar Sbot Λ₀ := by
  rw [chartGenParams, Function.update_self]
  -- entrywise: `reindex e.symm (reindex e X) = X` (the `submatrix` round-trip)
  funext a b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply,
    Fin.cast_cast, Fin.cast_eq_self]

/-! ## The general-`L` chart-eval collapse `prod M chart = z • (P₁·H̄)` -/

/-- **The general-`L` chart-eval collapse** `prod M (chartGenParams …) = z • (P₁·H̄)`. With the front
product `frontProd` column-split into the rank block `P₁ = frontProd[:, top r]` and the residual
`P₂ = frontProd[:, residual s]` (selected via `deepWidthEquiv` on `Fin (M ⟨L−1⟩)`), off the shear
cancellation `P₁·Λ₀ = P₂`, the deepest product collapses to the pure radial. The `L`-generalization of
`prod_chartL2Params`: the last-layer peel `prod = frontProd · A^{L−1}`, then the SAME single
`deepWidthEquiv` sum-reindex + `deepBlock_collapse`. -/
theorem prod_chartGen_collapse (M : Fin (L + 1) → ℕ) (A : Params M) (hL : 0 < L) {r s : ℕ}
    (hrs : r + s = M (⟨L - 1, by omega⟩ : Fin (L + 1)))
    (z : ℝ) (Hbar : Matrix (Fin r) (Fin (M (Fin.last L))) ℝ)
    (Sbot : Matrix (Fin s) (Fin (M (Fin.last L))) ℝ) (Λ₀ : Matrix (Fin r) (Fin s) ℝ)
    (e1 : M (⟨L - 1, by omega⟩ : Fin (L + 1)) = M ((⟨L - 1, by omega⟩ : Fin L).castSucc))
    (e2 : M (Fin.last L) = M ((⟨L - 1, by omega⟩ : Fin L).succ))
    (P₁ : Matrix (Fin (M 0)) (Fin r) ℝ) (P₂ : Matrix (Fin (M 0)) (Fin s) ℝ)
    (hP₁ : ∀ i k, P₁ i k = frontProd M A hL i (deepWidthEquiv hrs (Sum.inl k)))
    (hP₂ : ∀ i k, P₂ i k = frontProd M A hL i (deepWidthEquiv hrs (Sum.inr k)))
    (hcancel : P₁ * Λ₀ = P₂) :
    prod M (chartGenParams M A hL hrs z Hbar Sbot Λ₀ e1 e2) = z • (P₁ * Hbar) := by
  set chart := chartGenParams M A hL hrs z Hbar Sbot Λ₀ e1 e2 with hchart
  -- the last-layer peel of the chart
  rw [prod_eq_frontProd_mul_deep M chart hL e1 e2]
  -- the front product of the chart = frontProd of A; the deep layer = chartGenDeep
  rw [hchart, frontProd_chartGenParams M A hL hrs z Hbar Sbot Λ₀ e1 e2]
  rw [chartGenParams_deep_layer M A hL hrs z Hbar Sbot Λ₀ e1 e2]
  -- now: `frontProd M A hL * chartGenDeep = z • (P₁·H̄)`; entrywise
  funext i j
  rw [Matrix.mul_apply]
  -- reindex the `Fin (M ⟨L−1⟩)` sum by `deepWidthEquiv`
  rw [← Equiv.sum_comp (deepWidthEquiv hrs)
    (fun k1 => frontProd M A hL i k1 * chartGenDeep M hL hrs z Hbar Sbot Λ₀ k1 j)]
  have hdeep : ∀ x, chartGenDeep M hL hrs z Hbar Sbot Λ₀ (deepWidthEquiv hrs x) j
      = deepBlock z Hbar Sbot Λ₀ x j := by
    intro x; rw [chartGenDeep, Equiv.symm_apply_apply]
  simp only [hdeep]
  rw [Fintype.sum_sum_type]
  -- match the `(i,j)` entry of `Pfront · deepBlock` with `Pfront := frontProd ∘ deepWidthEquiv`
  have hcollapse := deepBlock_collapse z (fun i' x => frontProd M A hL i' (deepWidthEquiv hrs x))
    Hbar Sbot Λ₀ P₁ P₂ hP₁ hP₂ hcancel
  have hij := congrFun (congrFun hcollapse i) j
  rw [Matrix.mul_apply, Fintype.sum_sum_type] at hij
  simp only [deepBlock, Sum.elim_inl, Sum.elim_inr] at hij
  rw [Matrix.smul_apply, smul_eq_mul] at hij
  rw [Matrix.smul_apply, smul_eq_mul]
  convert hij using 2

/-! ## The rank-`r` bottleneck front factorization `frontProd = C · [I_r | K]` (de-risk (b))

The abstract matrix core of the general-`L` smeared front construction (Codex-reviewed, sympy-certified
exact L=2..5). To force `rank(frontProd) = r` (so `col(P₂) ⊆ col(P₁)`) with `P₁` a FREE block — the
`M 0 > r` rectangular case the L=2 square chart hides — the front factors as `frontProd = C · G` with
`C : M 0 × r` free and `G = [I_r | K] : r × m₁`. Then the column split gives `P₁ = C` (free, so
`det(P₁ᵀP₁) = det(CᵀC)` reduces to the SAME free-block diagonal dominance as L=2) and `P₂ = C · K =
P₁ · K` (`col(P₂) ⊆ col(P₁)`), and the banked `proj_cancel_of_factorsThrough` fires off `det(CᵀC) ≠ 0`.

Stated at the matrix level (a `C · G` factorization with `G`'s left `r×r` block the identity): the
`prodAux` staircase-chain realization (`A⁰=[C|0]`, interiors `carry_r`, `A^{L−2}=[I_r|K;0]`) is a
downstream instantiation; the column-split algebra + cancellation is width-generic and lives here. -/

/-- **The identity-block row-join** `G := [I_r | K] : Matrix (Fin r) (Fin r ⊕ Fin s)`, `Sum.inl a ↦
δ`, `Sum.inr b ↦ K a b`. The `r × m₁` front "gate" whose first `r` columns are the identity (so the
front product's first `r` columns are exactly the free `C`). -/
def idKGate {r s : ℕ} (K : Matrix (Fin r) (Fin s) ℝ) : Matrix (Fin r) (Fin r ⊕ Fin s) ℝ :=
  fun a => Sum.elim (fun a' => if a = a' then 1 else 0) (fun b => K a b)

/-- **The `idKGate` column split of a `C · [I_r|K]` front.** For `frontProd = C · idKGate K` (`C` the
free `M 0 × r` rank block), the `Sum.inl a` columns recover `C` (`(C · G)[:, inl a] = C[:, a]`) and the
`Sum.inr b` columns are `(C · K)[:, b]`. So `P₁ := (C·G)∘inl = C` and `P₂ := (C·G)∘inr = C · K = P₁·K`
— `col(P₂) ⊆ col(P₁)` structurally, with `P₁ = C` free. -/
theorem mul_idKGate_split {m0 r s : ℕ} (C : Matrix (Fin m0) (Fin r) ℝ) (K : Matrix (Fin r) (Fin s) ℝ) :
    (∀ i a, (C * idKGate K) i (Sum.inl a) = C i a)
      ∧ (∀ i b, (C * idKGate K) i (Sum.inr b) = (C * K) i b) := by
  refine ⟨fun i a => ?_, fun i b => ?_⟩
  · -- `(C·G)[i, inl a] = ∑_a' C[i,a']·(idKGate a' (inl a)) = ∑_a' C[i,a']·δ_{a' a} = C[i,a]`
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · simp only [idKGate, Sum.elim_inl, ite_true, mul_one]
    · intro a' _ hne
      simp only [idKGate, Sum.elim_inl]
      rw [if_neg hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  · -- `(C·G)[i, inr b] = ∑_a C[i,a]·K[a,b] = (C·K)[i,b]`
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun a _ => by simp only [idKGate, Sum.elim_inr])

/-- **The rank-`r` bottleneck cancellation** `P₁·Λ₀ = P₂` for a `C·[I_r|K]` front, off `det(CᵀC) ≠ 0`.
With `P₁ = C` (the free rank block) and `P₂ = C·K`, the factoring `P₂ = P₁·K` is structural
(`mul_idKGate_split`), and `proj_cancel_of_factorsThrough` gives the shear cancellation off the free-block
Gram pole `det(CᵀC) ≠ 0` — the SAME diagonal dominance as the L=2 `subBox_det_ne`. This is the de-risk
(b) reduction made precise: the tall-`P₁` cancellation the smeared chart needs, on a FREE `P₁`. -/
theorem staircase_cancel {m0 r s : ℕ} (C : Matrix (Fin m0) (Fin r) ℝ) (K : Matrix (Fin r) (Fin s) ℝ)
    (P₁ : Matrix (Fin m0) (Fin r) ℝ) (P₂ : Matrix (Fin m0) (Fin s) ℝ)
    (hP₁ : ∀ i a, P₁ i a = (C * idKGate K) i (Sum.inl a))
    (hP₂ : ∀ i b, P₂ i b = (C * idKGate K) i (Sum.inr b))
    (hdet : ((C.transpose * C).det ≠ 0)) :
    P₁ * ((P₁.transpose * P₁)⁻¹ * P₁.transpose * P₂) = P₂ := by
  obtain ⟨hsl, hsr⟩ := mul_idKGate_split C K
  -- `P₁ = C` and `P₂ = C·K` (read off the split)
  have hP1C : P₁ = C := by funext i a; rw [hP₁ i a, hsl i a]
  have hP2CK : P₂ = C * K := by funext i b; rw [hP₂ i b, hsr i b]
  -- the factoring `P₂ = P₁·K`, then the banked general projection cancellation
  rw [hP1C]
  refine proj_cancel_of_factorsThrough C P₂ K ?_ hdet
  rw [hP2CK]
end DLNFibre.DLN.RLCT
