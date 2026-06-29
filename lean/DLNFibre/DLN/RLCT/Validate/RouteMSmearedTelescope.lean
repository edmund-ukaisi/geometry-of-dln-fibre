import DLNFibre.DLN.RLCT.Validate.RouteMSmearedFrontFactor

/-!
# `RouteMSmearedTelescope` — the abstract telescoping deep-product collapse + Frobenius rate

The reusable, cast-free **algebraic heart** of the boundary-SMEARED rate `F = z²·U`
(`certificate-genM-smeared.md` §2). Stated over abstract matrices (no `routeMCore`, no opaque
dependent-`Fin` widths, no chart) so the dependent-width transport is pushed entirely into the chart
bridge (Codex `scope-answer` §2: state the rate over an abstract front-factorization, instantiate the
widths only once).

The deepest product, in the smeared chart, telescopes:

    D := P₁·(z·H̄ − Λ₀·S_bot) + P₂·S_bot
       = z·(P₁·H̄) + (P₂ − P₁·Λ₀)·S_bot
       = z·(P₁·H̄)                          (the shear-cancellation `P₁·Λ₀ = P₂` kills the `S_bot` term).

`telescope_collapse` proves `D = z·(P₁·H̄)` from `P₁·Λ₀ = P₂` alone (pure ring algebra on matrices).
`frobeniusSq_smul` then pulls the scalar out of the square-Frobenius sum:
`∑ᵢⱼ (z•X)ᵢⱼ² = z²·∑ᵢⱼ Xᵢⱼ²`. Together: `frobeniusSq D = z²·frobeniusSq (P₁·H̄)` — the rate `F = z²·U`
with `U = ‖P₁·H̄‖²_F` (manifestly `≥ 0`, and `z`-free since `Λ₀` has cancelled out: a genuine polynomial).

The cancellation `P₁·Λ₀ = P₂` is supplied by the banked `frontShear_cancel_general` (this file's sibling),
off the two null poles. This file is the consumer-facing rate; the chart bridge supplies `D = …` and the
`P₁·Λ₀ = P₂` instance.
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {m0 r c s : Type*} [Fintype m0] [Fintype r] [Fintype s] [Fintype c]

/-- **The deep-product telescoping collapse.** If `P₁·Λ₀ = P₂` (the shear cancellation), then the
shear-absorbed deep product `P₁·(z·H̄ − Λ₀·S_bot) + P₂·S_bot` collapses to the pure radial `z·(P₁·H̄)`:
the `S_bot`-coupled term `(P₂ − P₁·Λ₀)·S_bot` vanishes. Pure matrix ring algebra. -/
theorem telescope_collapse
    (z : ℝ) (P₁ : Matrix m0 r ℝ) (P₂ : Matrix m0 s ℝ)
    (Hbar : Matrix r c ℝ) (Sbot : Matrix s c ℝ) (Λ₀ : Matrix r s ℝ)
    (hcancel : P₁ * Λ₀ = P₂) :
    P₁ * (z • Hbar - Λ₀ * Sbot) + P₂ * Sbot = z • (P₁ * Hbar) := by
  rw [Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, hcancel]
  -- `z•(P₁H̄) − P₂·S_bot + P₂·S_bot = z•(P₁H̄)`
  abel

/-- **The Frobenius square pulls the scalar out** (`∑ᵢⱼ (z•X)ᵢⱼ² = z²·∑ᵢⱼ Xᵢⱼ²`). The square-Frobenius
loss against `0` of a scaled matrix is `z²` times that of the matrix. -/
theorem frobeniusSq_smul (z : ℝ) (X : Matrix m0 c ℝ) :
    (∑ i, ∑ j, ((z • X) i j) ^ 2) = z ^ 2 * ∑ i, ∑ j, (X i j) ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.smul_apply, smul_eq_mul, mul_pow]

/-- **The abstract smeared rate** `∑ᵢⱼ Dᵢⱼ² = z²·‖P₁·H̄‖²_F`. The square-Frobenius loss of the
shear-absorbed deep product `D = P₁·(z·H̄ − Λ₀·S_bot) + P₂·S_bot` is `z²` times the `z`-free unit
`U = ‖P₁·H̄‖²_F`, given the shear cancellation `P₁·Λ₀ = P₂`. Combines `telescope_collapse` (`D = z•(P₁H̄)`)
with `frobeniusSq_smul`. The cast-free heart of `F = z²·U`. -/
theorem smeared_rate_of_cancel
    (z : ℝ) (P₁ : Matrix m0 r ℝ) (P₂ : Matrix m0 s ℝ)
    (Hbar : Matrix r c ℝ) (Sbot : Matrix s c ℝ) (Λ₀ : Matrix r s ℝ)
    (hcancel : P₁ * Λ₀ = P₂) :
    (∑ i, ∑ j, ((P₁ * (z • Hbar - Λ₀ * Sbot) + P₂ * Sbot) i j) ^ 2)
      = z ^ 2 * ∑ i, ∑ j, ((P₁ * Hbar) i j) ^ 2 := by
  rw [telescope_collapse z P₁ P₂ Hbar Sbot Λ₀ hcancel, frobeniusSq_smul]

/-- **The unit `U = ‖P₁·H̄‖²_F` is nonnegative** (a sum of squares). The `Ufun`-nonneg fact the chart's
`Ubound`/`leaf_integrand` consume. -/
theorem frobeniusSq_nonneg (X : Matrix m0 c ℝ) : (0 : ℝ) ≤ ∑ i, ∑ j, (X i j) ^ 2 :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ## The block-indexed deep-product collapse (the `Fin r ⊕ Fin s` chart-eval heart)

The smeared chart's deepest factor is row-split: rows `r ⊕ s`, the TOP `r` rows the radial-minus-shear
`z·H̄ − Λ₀·S_bot`, the BOTTOM `s` rows the residual `S_bot`. Working at the `r ⊕ s` index level (NOT the
opaque `Fin (M ⟨L−1⟩)`) keeps the product collapse cast-free; the flat chart instantiates this via ONE
`finSumFinEquiv`/`finCongr` reindex of the deepest-width axis. -/

/-- **The block deepest factor** `deepBlock z H̄ S_bot Λ₀ : Matrix (r ⊕ s) c`: `Sum.inl k ↦
(z·H̄ − Λ₀·S_bot) k`, `Sum.inr k ↦ S_bot k`. The `r ⊕ s`-indexed deepest factor `A^{L−1}`. -/
def deepBlock (z : ℝ) (Hbar : Matrix r c ℝ) (Sbot : Matrix s c ℝ) (Λ₀ : Matrix r s ℝ) :
    Matrix (r ⊕ s) c ℝ :=
  Sum.elim (z • Hbar - Λ₀ * Sbot) Sbot

/-- **The block deep-product collapse** `Pfront · deepBlock = z • (P₁·H̄)`. The front factor
`Pfront : Matrix m0 (r ⊕ s)` column-splits as `P₁ = Pfront∘inl` (rank block) and `P₂ = Pfront∘inr`
(residual); off the shear cancellation `P₁·Λ₀ = P₂`, the product over `r ⊕ s` collapses to the pure
radial. Combines `Fintype.sum_sum_type` (the `r ⊕ s` sum split) with `telescope_collapse`. The cast-free
`Fin r ⊕ Fin s`-level chart-eval; the consumer of `frontShear_cancel_general`. -/
theorem deepBlock_collapse
    (z : ℝ) (Pfront : Matrix m0 (r ⊕ s) ℝ)
    (Hbar : Matrix r c ℝ) (Sbot : Matrix s c ℝ) (Λ₀ : Matrix r s ℝ)
    (P₁ : Matrix m0 r ℝ) (P₂ : Matrix m0 s ℝ)
    (hP₁ : ∀ i k, P₁ i k = Pfront i (Sum.inl k)) (hP₂ : ∀ i k, P₂ i k = Pfront i (Sum.inr k))
    (hcancel : P₁ * Λ₀ = P₂) :
    Pfront * deepBlock z Hbar Sbot Λ₀ = z • (P₁ * Hbar) := by
  -- `Pfront = fromCols P₁ P₂` (column split), so `Pfront · deepBlock = P₁·(top) + P₂·(bottom)`
  have hsplit : Pfront * deepBlock z Hbar Sbot Λ₀
      = P₁ * (z • Hbar - Λ₀ * Sbot) + P₂ * Sbot := by
    funext i j
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [deepBlock, Sum.elim_inl, Sum.elim_inr, Matrix.add_apply, Matrix.mul_apply]
    refine congrArg₂ (· + ·) ?_ ?_
    · exact Finset.sum_congr rfl (fun k _ => by rw [hP₁ i k])
    · exact Finset.sum_congr rfl (fun k _ => by rw [hP₂ i k])
  rw [hsplit, telescope_collapse z P₁ P₂ Hbar Sbot Λ₀ hcancel]

end DLNFibre.DLN.RLCT
