import DLNFibre.DLN.RLCT.Validate.RouteMSmearedGenRate

/-!
# `RouteMSmearedProjCancel` — the GENERAL projection cancellation `P₁·Λ₀ = P₂` (any tall `P₁`)

The load-bearing algebraic fact for the family-parametric ∀M boundary-SMEARED rate, **in the general
stratum where the rank-carrying block `P₁` is genuinely TALL** (`rows ≥ r` columns, `r = deepRank`).
This is the generalization of `scalarGram_cancel_of_rankOneColumns` (the `r = 1` / rank-one-columns case)
and of the `(2,3,1)` `P1_lam231` (the SQUARE `P₁`, which holds trivially for any `P₂` because a square
invertible `P₁` gives the full projection `P₁(P₁ᵀP₁)⁻¹P₁ᵀ = I`).

The honest content the square case hid: for a TALL `P₁`, the normal-equations routing
`Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂` satisfies `P₁·Λ₀ = P₂` **iff `col(P₂) ⊆ col(P₁)`** — the projection
`P₁(P₁ᵀP₁)⁻¹P₁ᵀ` is onto `col(P₁)`, and fixes `P₂` only there. The clean hypothesis is the FACTORING
form `P₂ = P₁·K` (which is exactly `col(P₂) ⊆ col(P₁)`); then the Gram-cancellation gives `Λ₀ = K`
directly, with **no SQUARE inverse of `P₁`** needed (`(P₁ᵀP₁)⁻¹·P₁ᵀ` is itself the rectangular
Moore–Penrose left-inverse — what is avoided is inverting the tall `P₁` directly):

    Λ₀ = (P₁ᵀP₁)⁻¹·P₁ᵀ·P₂ = (P₁ᵀP₁)⁻¹·P₁ᵀ·(P₁·K) = (P₁ᵀP₁)⁻¹·(P₁ᵀP₁)·K = I·K = K,

using only `(P₁ᵀP₁)⁻¹·(P₁ᵀP₁) = I` (`Matrix.nonsing_inv_mul`, the `r×r` Gram invertible off the pole
`{det(P₁ᵀP₁) = 0}`). Hence `P₁·Λ₀ = P₁·K = P₂`.

**Numerically VERIFY-REAL'd before building** (decorrelated from the design GATE, direct projection
identity, sympy exact at random rational points): all 26 boundary-smeared `M` with a genuinely-tall `P₁`
(`m0 > r`, `s > 0`; 5 distinct shapes incl `3×2`) satisfy the identity, 0 failures; a NEGATIVE control
(a generic `P₂ ∉ col(P₁)`) FAILS — so the identity is load-bearing on the front-bottleneck structural
fact `rank(P) = rank(P₁) = r` (⟺ `col(P₂) ⊆ col(P₁)`), not vacuously true.

**Caveat (carried next to the claim):** BOTH `P₂ = P₁·K` (`col(P₂) ⊆ col(P₁)`, supplied for the smeared
chart by the front-bottleneck `= r` structural fact) AND `det(P₁ᵀP₁) ≠ 0` (the off-pole condition,
forcing `P₁` full column rank) are load-bearing — neither alone gives `P₁·Λ₀ = P₂`.
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {rows : Type*} [Fintype rows]
variable {r : Type*} [Fintype r] [DecidableEq r]
variable {s : Type*}

/-- **The Gram routing collapses to the factor** `Λ₀ = K`. If `P₂ = P₁·K` (`col(P₂) ⊆ col(P₁)`) and
the `r×r` Gram `P₁ᵀP₁` is invertible (`det ≠ 0`), then the normal-equations routing
`Λ₀ = (P₁ᵀP₁)⁻¹·P₁ᵀ·P₂` equals `K`. The single step is `(P₁ᵀP₁)⁻¹·(P₁ᵀP₁) = I`
(`Matrix.nonsing_inv_mul`); no SQUARE inverse of the tall `P₁`. -/
theorem gram_routing_eq_factor
    (P₁ : Matrix rows r ℝ) (K : Matrix r s ℝ)
    (hdet : (P₁.transpose * P₁).det ≠ 0) :
    (P₁.transpose * P₁)⁻¹ * P₁.transpose * (P₁ * K) = K := by
  have hunit : IsUnit (P₁.transpose * P₁).det := isUnit_iff_ne_zero.mpr hdet
  -- regroup: ((P₁ᵀP₁)⁻¹ · (P₁ᵀ · P₁)) · K, collapse the Gram inverse, then `1 · K = K`
  calc (P₁.transpose * P₁)⁻¹ * P₁.transpose * (P₁ * K)
      = ((P₁.transpose * P₁)⁻¹ * (P₁.transpose * P₁)) * K := by
        simp only [Matrix.mul_assoc]
    _ = (1 : Matrix r r ℝ) * K := by rw [Matrix.nonsing_inv_mul _ hunit]
    _ = K := Matrix.one_mul K

/-- **The general projection cancellation** `P₁·Λ₀ = P₂` for a (possibly TALL) `P₁`. If
`col(P₂) ⊆ col(P₁)` in the factoring form `P₂ = P₁·K`, and the `r×r` Gram `P₁ᵀP₁` is invertible off
the pole (`det ≠ 0`), then the rational routing `Λ₀ = (P₁ᵀP₁)⁻¹·P₁ᵀ·P₂` satisfies `P₁·Λ₀ = P₂`. The
generalization of `scalarGram_cancel_of_rankOneColumns` (no rank-one / square restriction) — the
honest content for the boundary-smeared chart's shear-cancellation `(P₂ − P₁·Λ₀)·S_bot = 0`. -/
theorem proj_cancel_of_factorsThrough
    (P₁ : Matrix rows r ℝ) (P₂ : Matrix rows s ℝ) (K : Matrix r s ℝ)
    (hfac : P₂ = P₁ * K) (hdet : (P₁.transpose * P₁).det ≠ 0) :
    P₁ * ((P₁.transpose * P₁)⁻¹ * P₁.transpose * P₂) = P₂ := by
  rw [hfac, gram_routing_eq_factor P₁ K hdet]

/-! ## Non-vacuity: a genuinely-TALL `P₁` satisfies both hypotheses (the square case did not) -/

/-- **In-file witness that the antecedents are jointly inhabited at a TALL `P₁`** — the case the
`(2,3,1)` square `P₁` hid. `P₁ = !![1; 0; 0]` (`3×1`, full column rank, Gram `= [1] ≠ 0`),
`K = !![2, 3]` (a `1×2`, so `s = Fin 2`), and `P₂ = P₁·K = !![2,3; 0,0; 0,0]` genuinely lies in
`col(P₁)`. The cancellation fires: `P₁·Λ₀ = P₂`. -/
example :
    (!![(1 : ℝ); 0; 0] : Matrix (Fin 3) (Fin 1) ℝ) *
      (((!![(1 : ℝ); 0; 0] : Matrix (Fin 3) (Fin 1) ℝ).transpose
            * !![(1 : ℝ); 0; 0])⁻¹
          * (!![(1 : ℝ); 0; 0] : Matrix (Fin 3) (Fin 1) ℝ).transpose
          * ((!![(1 : ℝ); 0; 0] : Matrix (Fin 3) (Fin 1) ℝ) * !![(2 : ℝ), 3]))
      = (!![(1 : ℝ); 0; 0] : Matrix (Fin 3) (Fin 1) ℝ) * !![(2 : ℝ), 3] := by
  refine proj_cancel_of_factorsThrough _ _ !![(2 : ℝ), 3] rfl ?_
  -- the `1×1` Gram is `[1]`, det `= 1 ≠ 0`
  norm_num [Matrix.det_fin_one, Matrix.mul_apply, Fin.sum_univ_succ]

end DLNFibre.DLN.RLCT
