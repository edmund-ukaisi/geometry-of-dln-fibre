import DLNFibre.DLN.RLCT.Validate.RouteMSmearedProjCancel
import DLNFibre.DLN.RLCT.Validate.RouteMFrontBottleneck

/-!
# `RouteMSmearedFrontFactor` — the GENERAL-`r` front factoring `P₂ = P₁·K` (col(P₂) ⊆ col(P₁))

The general-`r` (`r = deepRank ≥ 1`, not just `r = 1`) bridge feeding the new
`proj_cancel_of_factorsThrough`: in the boundary-smeared regime the front product
`P = prodAux M A (L−1)` factors through the width-`r` BOTTLENECK layer (`certificate-genM-smeared.md`
§1, front-bottleneck `= r`, validated 652/652), `P = U·V` with inner width `r`. Splitting the columns
of `P` into the rank-carrying block `P₁ = P[:, ρ]` (`r` columns) and the residual `P₂ = P[:, σ]`, both
factor through `U`: `P₁ = U·Vρ`, `P₂ = U·Vσ`. Off the pole `{det Vρ ≠ 0}` (the `r×r` left block
invertible — `P₁` then full column rank), `U = P₁·Vρ⁻¹`, so

    P₂ = U·Vσ = P₁·(Vρ⁻¹·Vσ) = P₁·K,   K := Vρ⁻¹·Vσ,

i.e. `col(P₂) ⊆ col(P₁)`. This is the FACTORING hypothesis of `proj_cancel_of_factorsThrough`, so the
two compose to the wired general front fact `P₁·Λ₀ = P₂` (this file's `frontShear_cancel_general`).

The `r = 1` specialization recovers `RouteMFrontBottleneck`'s rank-one route
(`frontScalarShear_cancel_of_factorsThroughOne`): there `Vρ` is the `1×1` block `[V 0 0]`, `Vρ ≠ 0`
is the pole condition, and the rank-one-columns normalization is the same `U·V` outer product.

**Numerically VERIFY-REAL'd** (decorrelated, sympy exact, random rational points): the factoring
`P₂ = P₁·(Vρ⁻¹·Vσ)` AND the proj routing `P₁·Λ₀ = P₂` hold off both poles, 0/40 fails, for `r ≥ 2`
tall `P₁` (the genuinely-general case the `(2,3,1)` square and the `r=1` rank-one route both miss).

**Caveat (next to the claim):** BOTH poles are load-bearing and are (distinct) null sets — the factoring
needs `det Vρ ≠ 0` (full column rank of `P₁`), the proj cancellation needs `det(P₁ᵀP₁) ≠ 0`. The chart
evaluates off the union (still null); the box-divergence lower bound is unaffected.
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {rows : Type*} [Fintype rows]
variable {cols : Type*} [Fintype cols]
variable {r : Type*} [Fintype r] [DecidableEq r]
variable {s : Type*}

/-- **The general-`r` column factoring `P₂ = P₁·K`.** Let `P = U·V` (inner width `r`), and pick column
selectors `ρ : r → cols` (the rank block) and `σ : s → cols` (the residual). Write `Vρ := V·(col-pick ρ)`
(the `r×r` selected block of `V`) and `Vσ := V·(col-pick σ)`. With `P₁ i k = P i (ρ k)`,
`P₂ i j = P i (σ j)`, and `det Vρ ≠ 0`, we have `P₂ = P₁·K` with `K = Vρ⁻¹·Vσ`. The factoring form of
`col(P₂) ⊆ col(P₁)`. -/
theorem front_factorsThrough_general
    (P : Matrix rows cols ℝ) (U : Matrix rows r ℝ) (V : Matrix r cols ℝ)
    (hP : P = U * V)
    (ρ : r → cols) (σ : s → cols)
    (P₁ : Matrix rows r ℝ) (P₂ : Matrix rows s ℝ)
    (hP₁ : ∀ i k, P₁ i k = P i (ρ k)) (hP₂ : ∀ i j, P₂ i j = P i (σ j))
    (hVρ : (V.submatrix (id : r → r) ρ).det ≠ 0) :
    ∃ K : Matrix r s ℝ, P₂ = P₁ * K := by
  set Vρ : Matrix r r ℝ := V.submatrix (id : r → r) ρ with hVρdef
  set Vσ : Matrix r s ℝ := V.submatrix (id : r → r) σ with hVσdef
  -- `P₁ = U·Vρ` and `P₂ = U·Vσ` (column-select the factorization)
  have hP1 : P₁ = U * Vρ := by
    funext i k
    rw [hP₁ i k, hP, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun a _ => by rw [hVρdef, Matrix.submatrix_apply]; rfl)
  have hP2 : P₂ = U * Vσ := by
    funext i j
    rw [hP₂ i j, hP, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun a _ => by rw [hVσdef, Matrix.submatrix_apply]; rfl)
  -- `K := Vρ⁻¹·Vσ`; then `P₂ = U·Vσ = U·Vρ·Vρ⁻¹·Vσ = P₁·K`
  refine ⟨Vρ⁻¹ * Vσ, ?_⟩
  have hunit : IsUnit Vρ.det := isUnit_iff_ne_zero.mpr hVρ
  rw [hP2, hP1]
  calc U * Vσ
      = U * (1 : Matrix r r ℝ) * Vσ := by rw [Matrix.mul_one]
    _ = U * (Vρ * Vρ⁻¹) * Vσ := by rw [Matrix.mul_nonsing_inv _ hunit]
    _ = U * Vρ * (Vρ⁻¹ * Vσ) := by simp only [Matrix.mul_assoc]

/-- **The wired general-`r` front shear cancellation** `P₁·Λ₀ = P₂`. Combines the column factoring
(`front_factorsThrough_general`, `col(P₂) ⊆ col(P₁)` off `{det Vρ ≠ 0}`) with the projection
cancellation (`proj_cancel_of_factorsThrough`, off `{det(P₁ᵀP₁) ≠ 0}`). The general-`r` analog of
`frontScalarShear_cancel_of_factorsThroughOne` — the boundary-smeared chart's deepest-product
telescoping `(P₂ − P₁·Λ₀)·S_bot = 0` for ANY rank `r ≥ 1`. -/
theorem frontShear_cancel_general
    (P : Matrix rows cols ℝ) (U : Matrix rows r ℝ) (V : Matrix r cols ℝ)
    (hP : P = U * V)
    (ρ : r → cols) (σ : s → cols)
    (P₁ : Matrix rows r ℝ) (P₂ : Matrix rows s ℝ)
    (hP₁ : ∀ i k, P₁ i k = P i (ρ k)) (hP₂ : ∀ i j, P₂ i j = P i (σ j))
    (hVρ : (V.submatrix (id : r → r) ρ).det ≠ 0)
    (hdet : (P₁.transpose * P₁).det ≠ 0) :
    P₁ * ((P₁.transpose * P₁)⁻¹ * P₁.transpose * P₂) = P₂ := by
  obtain ⟨K, hK⟩ := front_factorsThrough_general P U V hP ρ σ P₁ P₂ hP₁ hP₂ hVρ
  exact proj_cancel_of_factorsThrough P₁ P₂ K hK hdet

/-! ## The wired front-bottleneck bridge — `prodAux` factors through the width-`r` BOTTLENECK layer

The structural fact (`certificate-genM-smeared.md` §1, front-bottleneck `= r`, validated 652/652): the
smeared front product `P = prodAux M A (L−1)` factors through ANY earlier layer `p` (`prodAux_split_exists`
gives `P = prodAux M A p · Y`). At the width-`r` bottleneck layer the inner width is exactly `r`, so this
is the `U·V` factorization the general-`r` cancellation consumes. (The inner width here is the abstract
`Fin (M ⟨p,_⟩)`; the chart instantiates it as the `r` rank-block.) -/

variable {L : ℕ}

/-- **The general-`r` `prodAux` front shear cancellation** (the chart consumer): the front product
`P = prodAux M A (L−1)` through the split at layer `p`, with column selectors `ρ`/`σ` into the deepest
width `Fin (M ⟨L−1,_⟩)`, has its shear cancel `P₁·Λ₀ = P₂` off the two poles. Combines the prefix split
(`prodAux_split_exists`, `P = U·Y`) with `frontShear_cancel_general`. The general-`r` analog of
`prodAux_frontScalarShear_cancel` (which is the `M ⟨p,_⟩ = 1`, rank-one, special case). -/
theorem prodAux_frontShear_cancel_general
    (M : Fin (L + 1) → ℕ) (A : Params M)
    (p : ℕ) (hp : p < L + 1) (k : ℕ) (hpk : p ≤ k) (hk : k < L + 1)
    {s : Type*}
    (ρ : Fin (M ⟨p, hp⟩) → Fin (M ⟨k, hk⟩)) (σ : s → Fin (M ⟨k, hk⟩))
    (P₁ : Matrix (Fin (M 0)) (Fin (M ⟨p, hp⟩)) ℝ) (P₂ : Matrix (Fin (M 0)) s ℝ)
    (hP₁ : ∀ i kk, P₁ i kk = prodAux M A k hk i (ρ kk))
    (hP₂ : ∀ i j, P₂ i j = prodAux M A k hk i (σ j))
    (hVρ : ∀ (Y : Matrix (Fin (M ⟨p, hp⟩)) (Fin (M ⟨k, hk⟩)) ℝ),
      prodAux M A k hk = prodAux M A p hp * Y → (Y.submatrix (id : _ → _) ρ).det ≠ 0)
    (hdet : (P₁.transpose * P₁).det ≠ 0) :
    P₁ * ((P₁.transpose * P₁)⁻¹ * P₁.transpose * P₂) = P₂ := by
  obtain ⟨Y, hY⟩ := prodAux_split_exists M A p hp k hpk hk
  exact frontShear_cancel_general (prodAux M A k hk) (prodAux M A p hp) Y hY ρ σ P₁ P₂
    hP₁ hP₂ (hVρ Y hY) hdet

end DLNFibre.DLN.RLCT
