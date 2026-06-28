import DLNFibre.DLN.RLCT.Validate.RouteMSmearedGenRate
import DLNFibre.DLN.RLCT.Validate.RouteMFrontPeel

/-!
# `RouteMFrontBottleneck` — the front-bottleneck → rank-one-columns bridge

The ∀M-(1,1)-smeared front fact feeding the landed `scalarGram_cancel_of_rankOneColumns`: in the
`(1,1)`-smeared regime the front product `P = prodAux M A (L−1)` factors through a width-1 inner
dimension at the first width-1 layer `p*`, so its columns are scalar multiples of column `0` off the
pole `‖col 0‖² ≠ 0`. Three pieces:

* `rankOneColumns_of_factorsThroughOne` (§3a) — GENERIC pure linear algebra (rank-free): a matrix
  that factors `P = U * V` through `Fin 1` has, off `‖col 0‖² ≠ 0`, rank-one columns normalized to
  column 0 (`P i j = μ j · c₀ i`, `c₀ = P.col 0`, `μ 0 = 1`). The mechanism is the LITERAL `Fin 1`
  outer product `(U·V) i j = U i 0 · V 0 j` (`Matrix.mul_apply` + `Fin.sum_univ_one`), NOT rank theory.

* `prodAux_factorsThroughOne` (§3b) — the cast-heavy specialization to `P = prodAux M A`: split the
  left-associated dependent-width `prodAux` at the width-1 layer `p*` (an existential right-factor
  split, `prodAux_split_exists`), collapsing the `Fin (M_{p*})` inner type to `Fin 1` via `finCongr`
  at the equiv level, reusing the `RouteMFrontPeel` cast kernel.

* `frontScalarShear_cancel_of_factorsThroughOne` / `prodAux_frontScalarShear_cancel` (§3c) — the
  wired front fact `P₁ · Λ₀ = P₂` (the scalar shear cancels off the pole).

**Caveat (next to the claim, Codex's load-bearing correction):** "every column of `P` is a multiple
of column 0" is FALSE without the off-pole hypothesis (counterexample `P = [0 1]`: it factors through
`Fin 1` but column 1 is not a scalar multiple of column 0 = 0). The unconditional factorization gives
columns as multiples of the HIDDEN column `U`; normalizing to `c₀ = P.col 0` needs `V 0 0 ≠ 0`, which
the consumer's `‖c₀‖² ≠ 0` supplies exactly (`‖c₀‖² = (V 0 0)² · ‖U‖²`).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

/-! ## §3a. The generic bridge (rank-free) -/

/-- **Rank-one columns from a `Fin 1` factorization.** A matrix `P = U * V` that factors through a
`Fin 1` inner dimension has, off the pole `‖col 0‖² = ∑ᵢ (P i 0)² ≠ 0`, rank-one columns normalized
to column 0: `P i j = μ j · c₀ i` with `c₀ = P.col 0` and `μ ⟨0,_⟩ = 1`. The mechanism is the LITERAL
outer product `(U·V) i j = U i 0 · V 0 j` (`Matrix.mul_apply` + `Fin.sum_univ_one`), normalized via
`V 0 0 ≠ 0` extracted from `hc`. -/
theorem rankOneColumns_of_factorsThroughOne
    {rows : Type*} [Fintype rows] {m1 : ℕ} (hm1 : 0 < m1)
    (P : Matrix rows (Fin m1) ℝ)
    (U : Matrix rows (Fin 1) ℝ) (V : Matrix (Fin 1) (Fin m1) ℝ)
    (hP : P = U * V)
    (hc : (∑ i, (P i ⟨0, hm1⟩) ^ 2) ≠ 0) :
    ∃ (c₀ : rows → ℝ) (μ : Fin m1 → ℝ),
      c₀ = (fun i => P i ⟨0, hm1⟩) ∧ μ ⟨0, hm1⟩ = 1 ∧
      ∀ i j, P i j = μ j * c₀ i := by
  -- The literal `Fin 1` outer product: `P i j = U i 0 · V 0 j`.
  have hpij : ∀ i j, P i j = U i 0 * V 0 j := by
    intro i j
    rw [hP, Matrix.mul_apply, Fin.sum_univ_one]
  -- Off-pole: `V 0 ⟨0,_⟩ ≠ 0` (else column 0 is identically zero and the Gram vanishes).
  have hV : V 0 ⟨0, hm1⟩ ≠ 0 := by
    intro h0
    apply hc
    apply Finset.sum_eq_zero
    intro i _
    rw [hpij i ⟨0, hm1⟩, h0, mul_zero, zero_pow (by norm_num)]
  refine ⟨fun i => P i ⟨0, hm1⟩, fun j => V 0 j / V 0 ⟨0, hm1⟩, rfl, ?_, ?_⟩
  · -- `μ ⟨0,_⟩ = (V 0 0)/(V 0 0) = 1`.
    exact div_self hV
  · -- `P i j = (V 0 j / V 0 0) · (U i 0 · V 0 0) = U i 0 · V 0 j`.
    intro i j
    simp only []
    rw [hpij i j, hpij i ⟨0, hm1⟩]
    field_simp

/-! ## §3b. The interior split of `prodAux` + the front-product factorization -/

variable {L : ℕ}

/-- **The interior split of `prodAux` (existence form).** The prefix product through `k` layers
factors at any earlier position `p ≤ k`: `prodAux M A k = prodAux M A p * Y` for some
`Y : Matrix (Fin (M ⟨p,_⟩)) (Fin (M ⟨k,_⟩))` (the suffix product over layers `p..k−1`). Only the
existence of `Y` is needed (the downstream `Fin 1` factorization consumes `P = U * V` generically).
Proved by `Nat.le_induction` on the right endpoint `k ≥ p`, reusing `prodAux_succ` + the fully-applied
`mul_three_reassoc` to push the new layer into `Y`; no entrywise `ext`, no shifted-chain reindex. -/
theorem prodAux_split_exists (M : Fin (L + 1) → ℕ) (A : Params M) (p : ℕ) (hp : p < L + 1) :
    ∀ (k : ℕ) (hpk : p ≤ k) (hk : k < L + 1),
      ∃ (Y : Matrix (Fin (M ⟨p, hp⟩)) (Fin (M ⟨k, hk⟩)) ℝ),
        prodAux M A k hk = prodAux M A p hp * Y := by
  intro k hpk
  induction k, hpk using Nat.le_induction with
  | base =>
      intro hk
      obtain rfl : hk = hp := Subsingleton.elim _ _
      exact ⟨1, (Matrix.mul_one _).symm⟩
  | succ k hpk ih =>
      intro hk
      obtain ⟨Y, hY⟩ := ih (Nat.lt_of_succ_lt hk)
      -- last-layer peel of the parent at index `k`.
      have e1 : M (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L + 1))
          = M ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc) := rfl
      have e2 : M (⟨k + 1, hk⟩ : Fin (L + 1))
          = M ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).succ) := rfl
      rw [prodAux_succ M A k hk e1 e2, hY]
      refine ⟨Y * (Matrix.reindex (finCongr e1.symm) (finCongr e2.symm)
        (A ⟨k, Nat.lt_of_succ_lt_succ hk⟩)), ?_⟩
      exact mul_three_reassoc (prodAux M A p hp) Y _

/-- **The front product factors through a width-1 layer.** With `M ⟨p,_⟩ = 1`, the prefix product
through `k ≥ p` layers `prodAux M A k` factors as `U * V` with `U : Matrix (Fin (M 0)) (Fin 1) ℝ`
(the prefix `A⁰···A^{p−1}`, collapsed at the width-1 interface) and `V : Matrix (Fin 1) (Fin (M ⟨k,_⟩)) ℝ`
(the suffix `A^p···A^{k−1}`). The `Fin (M ⟨p,_⟩) → Fin 1` collapse is `finCongr hp1` at the equiv
level (`reindex (finCongr hp1) (finCongr rfl)` of each factor, `reindex_finCongr_mul` distributing the
collapse over the product). -/
theorem prodAux_factorsThroughOne (M : Fin (L + 1) → ℕ) (A : Params M)
    (p : ℕ) (hp : p < L + 1) (hp1 : M ⟨p, hp⟩ = 1)
    (k : ℕ) (hpk : p ≤ k) (hk : k < L + 1) :
    ∃ (U : Matrix (Fin (M 0)) (Fin 1) ℝ) (V : Matrix (Fin 1) (Fin (M ⟨k, hk⟩)) ℝ),
      prodAux M A k hk = U * V := by
  obtain ⟨Y, hY⟩ := prodAux_split_exists M A p hp k hpk hk
  -- Collapse the middle width `M ⟨p,_⟩ = 1` to `Fin 1` via `finCongr hp1`.
  refine ⟨Matrix.reindex (finCongr (rfl : M 0 = M 0)) (finCongr hp1) (prodAux M A p hp),
          Matrix.reindex (finCongr hp1) (finCongr (rfl : M ⟨k, hk⟩ = M ⟨k, hk⟩)) Y, ?_⟩
  rw [hY, ← reindex_finCongr_mul (rfl : M 0 = M 0) hp1 (rfl : M ⟨k, hk⟩ = M ⟨k, hk⟩)]
  rw [show (finCongr (rfl : M 0 = M 0)) = Equiv.refl _ from finCongr_refl _,
      show (finCongr (rfl : M ⟨k, hk⟩ = M ⟨k, hk⟩)) = Equiv.refl _ from finCongr_refl _]
  erw [Matrix.reindex_refl_refl]

/-! ## §3c. The wired front fact `P₁·Λ₀ = P₂` (the ∀M-(1,1)-smeared scalar shear cancels) -/

/-- **The front-bottleneck scalar-shear cancellation** (the wired front fact). For a matrix `P` that
factors through a `Fin 1` inner dimension (`P = U * V`), off the pole `‖col 0‖² ≠ 0`, ANY column split
into the pivot column `P₁ = P[:,0:1]` (`hP₁ : ∀ i, P₁ i 0 = P i ⟨0,_⟩`) and a residual block
`P₂` whose columns are columns of `P` (`hP₂ : ∀ i j, P₂ i j = P i (σ j)`) satisfies the scalar-Gram
cancellation `P₁ · (P₁ᵀP₁)⁻¹P₁ᵀP₂ = P₂`. Combines §3a (`P` rank-one-columns from the factorization)
with the landed `scalarGram_cancel_of_rankOneColumns`. The residual selector `σ : s → Fin m1` is
arbitrary (in the chart, `σ j = ⟨j+1,_⟩`, the `r..m1−1` residual columns). -/
theorem frontScalarShear_cancel_of_factorsThroughOne
    {n : ℕ} {m1 : ℕ} (hm1 : 0 < m1) {s : Type*} [Fintype s] [DecidableEq s]
    (P : Matrix (Fin n) (Fin m1) ℝ)
    (U : Matrix (Fin n) (Fin 1) ℝ) (V : Matrix (Fin 1) (Fin m1) ℝ)
    (hP : P = U * V)
    (hc : (∑ i, (P i ⟨0, hm1⟩) ^ 2) ≠ 0)
    (σ : s → Fin m1)
    (P₁ : Matrix (Fin n) (Fin 1) ℝ) (P₂ : Matrix (Fin n) s ℝ)
    (hP₁ : ∀ i, P₁ i 0 = P i ⟨0, hm1⟩) (hP₂ : ∀ i j, P₂ i j = P i (σ j)) :
    P₁ * ((P₁.transpose * P₁)⁻¹ * P₁.transpose * P₂) = P₂ := by
  obtain ⟨c₀, μ, hc₀, _, hcol⟩ := rankOneColumns_of_factorsThroughOne hm1 P U V hP hc
  refine scalarGram_cancel_of_rankOneColumns c₀ (fun j => μ (σ j)) ?_ P₁ P₂ ?_ ?_
  · rw [hc₀]; exact hc
  · intro i; rw [hP₁ i, hc₀]
  · intro i j; rw [hP₂ i j, hcol i (σ j)]

/-- **The ∀M-(1,1)-smeared front fact** (the chart consumer): the front product `P = prodAux M A k`
through `k ≥ p` layers, with a width-1 layer at `p` (`M ⟨p,_⟩ = 1` — the front bottleneck `r = 1`), has
its scalar-Gram shear cancel `P₁ · Λ₀ = P₂` off the pole, for the pivot column `P₁ = P[:,0:1]` and any
residual block `P₂` selecting columns of `P`. Combines §3b's `Fin 1` factorization with §3c. -/
theorem prodAux_frontScalarShear_cancel
    (M : Fin (L + 1) → ℕ) (A : Params M)
    (p : ℕ) (hp : p < L + 1) (hp1 : M ⟨p, hp⟩ = 1)
    (k : ℕ) (hpk : p ≤ k) (hk : k < L + 1) (hm1 : 0 < M ⟨k, hk⟩)
    (hc : (∑ i, (prodAux M A k hk i ⟨0, hm1⟩) ^ 2) ≠ 0)
    {s : Type*} [Fintype s] [DecidableEq s]
    (σ : s → Fin (M ⟨k, hk⟩))
    (P₁ : Matrix (Fin (M 0)) (Fin 1) ℝ) (P₂ : Matrix (Fin (M 0)) s ℝ)
    (hP₁ : ∀ i, P₁ i 0 = prodAux M A k hk i ⟨0, hm1⟩)
    (hP₂ : ∀ i j, P₂ i j = prodAux M A k hk i (σ j)) :
    P₁ * ((P₁.transpose * P₁)⁻¹ * P₁.transpose * P₂) = P₂ := by
  obtain ⟨U, V, hUV⟩ := prodAux_factorsThroughOne M A p hp hp1 k hpk hk
  exact frontScalarShear_cancel_of_factorsThroughOne hm1 (prodAux M A k hk) U V hUV hc σ
    P₁ P₂ hP₁ hP₂

end DLNFibre.DLN.RLCT
