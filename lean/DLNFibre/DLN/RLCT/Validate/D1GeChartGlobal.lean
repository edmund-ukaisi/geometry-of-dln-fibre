import DLNFibre.DLN.RLCT.Validate.D1GeChart
import DLNFibre.DLN.RLCT.Foundations.S1InverseDerivEquiv

/-!
# `DLNFibre.DLN.RLCT.Validate.D1GeChartGlobal` — invertible derivative from a LEFT inverse (rung 8)

The general-`L` chart's globalisation needs an invertible derivative at the base point. The L = 2
route (`derivEquiv_of_eventual_inverse`, `S1InverseDerivEquiv`) used BOTH inverse germs `Ψ∘Φ =ᶠ id`
and `Φ∘Ψ =ᶠ id`. Here we observe that the LEFT inverse alone suffices in finite dimensions: from
`Ψ∘Φ =ᶠ id` the chain rule gives `DΨ ∘ DΦ = id`, so `DΦ` is injective, hence (finite-dimensional
`injective_iff_surjective`) bijective — a `ContinuousLinearEquiv`. This avoids proving the reverse
`Ψ∘Φ =ᶠ id` the chain rule gives `DΨ ∘ DΦ = id`, so `DΦ` is injective, hence (finite-dim
`Ψ∘Φ = id` is already established (`schurChartRawInvGen_schurChartRawGen`).
-/

open Filter
open scoped Topology

namespace DLNFibre.DLN.RLCT

/-- **An invertible chart derivative from a LEFT inverse germ** (finite-dim). If `Φ, Ψ : E → E` have
named derivatives `A` at `wstar`, `Bd` at `Φ wstar`, and `Ψ ∘ Φ =ᶠ id` near `wstar`, then `A`
underlies a continuous linear equivalence with `HasFDerivAt Φ (f' : E →L[ℝ] E) wstar`. The
finite-dimensional strengthening of `derivEquiv_of_eventual_inverse` needing only the left germ
(`Bd ∘ A = id` ⟹ `A` injective ⟹ bijective). -/
theorem derivEquiv_of_left_inverse {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Φ Ψ : E → E) (wstar : E) (A Bd : E →L[ℝ] E)
    (hΦ' : HasFDerivAt Φ A wstar) (hΨ' : HasFDerivAt Ψ Bd (Φ wstar))
    (hΨΦ : (Ψ ∘ Φ) =ᶠ[𝓝 wstar] id) :
    ∃ f' : E ≃L[ℝ] E, HasFDerivAt Φ (f' : E →L[ℝ] E) wstar := by
  -- `Bd ∘ A = id` from `Ψ ∘ Φ =ᶠ id`.
  have hcomp1 : HasFDerivAt (Ψ ∘ Φ) (Bd.comp A) wstar := hΨ'.comp wstar hΦ'
  have hid1 : HasFDerivAt (Ψ ∘ Φ) (ContinuousLinearMap.id ℝ E) wstar :=
    (hasFDerivAt_id (𝕜 := ℝ) wstar).congr_of_eventuallyEq hΨΦ
  have hBA : Bd.comp A = ContinuousLinearMap.id ℝ E := hcomp1.unique hid1
  -- `A` injective (left inverse `Bd`), hence bijective in finite dimensions.
  have hinj : Function.Injective (A : E →ₗ[ℝ] E) := by
    have hL : Function.LeftInverse Bd A := fun x => by
      have := ContinuousLinearMap.ext_iff.mp hBA x; simpa using this
    exact hL.injective
  have hbij : Function.Bijective (A : E →ₗ[ℝ] E) :=
    ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩
  refine ⟨(LinearEquiv.ofBijective (A : E →ₗ[ℝ] E) hbij).toContinuousLinearEquiv, ?_⟩
  have hcoe : ((LinearEquiv.ofBijective (A : E →ₗ[ℝ] E) hbij).toContinuousLinearEquiv
      : E →L[ℝ] E) = A := by ext x; rfl
  rw [hcoe]; exact hΦ'

/-! ## Rung 7 prep — ContDiff of the partial products -/

/-- **Each `partProd` entry is `ContDiff`**, given each layer entry is. Induction on
`k`, peeling the last factor with the banked entrywise matrix-mult `ContDiff`
(`SchurChartC2.contDiff_matrix_mul_entry`). The core of the chart's smoothness: `schurChartRawGen`'s
output blocks are `+`/`∗`/`⁻¹` combinations of `partProd` entries. -/
theorem contDiff_gen_partProd_entry {𝕏 : Type*} [NormedAddCommGroup 𝕏] [NormedSpace ℝ 𝕏]
    {r₀ : ℕ} {n : ℕ → ℕ}
    (C : 𝕏 → (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ)
    (hC : ∀ s i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => C x s i j)) :
    ∀ (k : ℕ) (i j), ContDiff ℝ (⊤ : ℕ∞) (fun x => (partProd (C x) k) i j) := by
  intro k
  induction k with
  | zero => intro i j; simp only [partProd]; exact contDiff_const
  | succ k ih =>
      intro i j
      change ContDiff ℝ (⊤ : ℕ∞) (fun x => (partProd (C x) k * C x k) i j)
      exact SchurChartC2.contDiff_matrix_mul_entry (fun a b => ih a b) (fun a b => hC k a b) i j

/-- **Each `redFactorGen` entry is `ContDiffAt`** on the prefix-pivot domain. `R_s = (C_s)₂₂ −
(C_s)₂₁·(P_{s+1})₁₁⁻¹·(P_{s+1})₁₂`: the `⁻¹` entries are `ContDiffAt` where `det (P_{s+1})₁₁ ≠ 0`
(`SchurChartC2.contDiffAt_matrix_inv_entry_of_det_ne_zero`, after `nonsing_inv_eq_ringInverse`), the
rest via entrywise mul/`partProd` `ContDiff`. -/
theorem contDiffAt_redFactorGen_entry {𝕏 : Type*} [NormedAddCommGroup 𝕏] [NormedSpace ℝ 𝕏]
    {r₀ : ℕ} {n : ℕ → ℕ}
    (C : 𝕏 → (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ)
    (hC : ∀ s i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => C x s i j)) (s : ℕ) {x₀ : 𝕏}
    (hpiv : ((partProd (C x₀) (s + 1)).toBlocks₁₁).det ≠ 0)
    (a : Fin (n s)) (b : Fin (n (s + 1))) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x => (redFactorGen (C x) s) a b) x₀ := by
  have hpp := contDiff_gen_partProd_entry C hC
  have hinv : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => ((partProd (C x) (s + 1)).toBlocks₁₁)⁻¹ i j) x₀ := fun i j =>
    SchurChartC2.contDiffAt_matrix_inv_entry_of_det_ne_zero
      (fun i' j' => hpp (s + 1) (Sum.inl i') (Sum.inl j')) hpiv i j
  -- `redFactorGen (C x) s` entrywise: `(C_s)₂₂ − ((C_s)₂₁ · (P_{s+1})₁₁⁻¹ · (P_{s+1})₁₂)`.
  have hentry : (fun x => (redFactorGen (C x) s) a b)
      = fun x => (C x s) (Sum.inr a) (Sum.inr b)
        - ((C x s).toBlocks₂₁ * ((partProd (C x) (s + 1)).toBlocks₁₁)⁻¹
            * (partProd (C x) (s + 1)).toBlocks₁₂) a b := by
    funext x
    rw [redFactorGen, Matrix.nonsing_inv_eq_ringInverse]
    rfl
  rw [hentry]
  refine ContDiffAt.sub ((hC s (Sum.inr a) (Sum.inr b)).contDiffAt) ?_
  -- the triple product entry: `((C_s)₂₁ · inv) · (P_{s+1})₁₂`.
  refine SchurChartC2.contDiffAt_matrix_mul_entry
    (fun i k => SchurChartC2.contDiffAt_matrix_mul_entry
      (fun i' k' => (hC s (Sum.inr i') (Sum.inl k')).contDiffAt) hinv i k)
    (fun k j => (hpp (s + 1) (Sum.inl k) (Sum.inr j)).contDiffAt) a b

/-- **Rung 7 — each chart output-block entry is `ContDiffAt`** on the prefix-pivot domain (`det
(P_{s+1})₁₁ ≠ 0`). Case on the `Fin r₀ ⊕ Fin (·−r)` block position: the `(1,1)`/`(1,2)` corners are
`partProd` entries; `(2,1)` is `(P_L)₂₁` (slot 0) or `(C_s)₂₁`; `(2,2)` is `redFactorGen`. Reuses
`contDiff_gen_partProd_entry`, `contDiffAt_redFactorGen_entry`, `hC`. -/
theorem contDiffAt_schurChartRawGen_entry {𝕏 : Type*} [NormedAddCommGroup 𝕏] [NormedSpace ℝ 𝕏]
    {r₀ : ℕ} {n : ℕ → ℕ}
    (C : 𝕏 → (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ)
    (hC : ∀ s i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => C x s i j)) (last : ℕ) (s : ℕ) {x₀ : 𝕏}
    (hpiv : ((partProd (C x₀) (s + 1)).toBlocks₁₁).det ≠ 0)
    (a : Fin r₀ ⊕ Fin (n s)) (b : Fin r₀ ⊕ Fin (n (s + 1))) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x => (schurChartRawGen (C x) (last + 1) s) a b) x₀ := by
  have hpp := contDiff_gen_partProd_entry C hC
  rcases a with a | a <;> rcases b with b | b
  · -- (1,1): `(P_{s+1})₁₁`.
    exact (hpp (s + 1) (Sum.inl a) (Sum.inl b)).contDiffAt
  · -- (1,2): `(P_{s+1})₁₂`.
    exact (hpp (s + 1) (Sum.inl a) (Sum.inr b)).contDiffAt
  · -- (2,1): `(P_L)₂₁` at `s = 0`, else `(C_s)₂₁`.
    by_cases hs0 : s = 0
    · subst hs0
      have heq : (fun x => (schurChartRawGen (C x) (last + 1) 0) (Sum.inr a) (Sum.inl b))
          = fun x => (partProd (C x) (last + 1)) (Sum.inr a) (Sum.inl b) := by
        funext x
        exact congrFun₂ (schurChartRawGen_toBlocks₂₁_zero (C x) (last + 1)) a b
      rw [heq]; exact (hpp (last + 1) (Sum.inr a) (Sum.inl b)).contDiffAt
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs0
      have heq : (fun x => (schurChartRawGen (C x) (last + 1) (t + 1)) (Sum.inr a) (Sum.inl b))
          = fun x => (C x (t + 1)) (Sum.inr a) (Sum.inl b) := by
        funext x
        exact congrFun₂ (schurChartRawGen_toBlocks₂₁_succ (C x) (last + 1) t) a b
      rw [heq]; exact (hC (t + 1) (Sum.inr a) (Sum.inl b)).contDiffAt
  · -- (2,2): `redFactorGen`.
    exact contDiffAt_redFactorGen_entry C hC s hpiv a b

end DLNFibre.DLN.RLCT
