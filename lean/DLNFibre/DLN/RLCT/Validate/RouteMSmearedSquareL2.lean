import DLNFibre.DLN.RLCT.Validate.RouteMSmearedDecodeL2
import DLNFibre.Core.Matrix.DiagDominance

/-!
# `RouteMSmearedSquareL2` — discharging the two analytic hypotheses on the smeared L=2 stratum

The smeared L=2 stratum (`certificate-smeared-l2-two-facts.md`, decorrelated p&p + Codex) is exactly
`M0 < M1` with the front-bottleneck split `r = min(M0,M1) = M0`, so the rank-block front matrix `P₁` is
**square** (`M0 × M0`). This file discharges, on the square slice `r = M0`, the two genuinely-analytic
hypotheses the chart assembly `routeMCore_smearedL2` left open:

* **`hcancel` (Fact 1, off-pole cancellation)** — `P₁·Λ₀ = P₂`. For a square invertible `P₁`,
  `K := P₁⁻¹·P₂` factors `P₂ = P₁·K`, and `det(P₁ᵀP₁) = (det P₁)² ≠ 0`; the banked
  `Lam0u_cancel_of_factoring` then fires. The single input is `det P₁ ≠ 0`.

The invertibility input `det P₁ ≠ 0` is supplied UNCONDITIONALLY on a conditioned box via strict row
diagonal dominance (`Core.Matrix.StrictRowDominant.det_ne_zero`, Levy–Desplanques) — not merely a.e.
The per-`r` off-diagonal box width `η = δ/(4(r−1))` (Codex scope catch: a fixed `δ/8` is singular for
`r ≥ 5`) gives the margin `γ = δ/4 > 0`.

SCOPE (load-bearing, honored): Fact 1 is FALSE for the free front `A0u` at `r < M0` (the cancellation
needs `col(P₂) ⊆ col(P₁)`, which a free tall `P₁` does not give). So the cancellation here is proved on
the SQUARE slice `r = M0` only, which is the ENTIRE genuine smeared L=2 stratum — there is no smeared
L=2 configuration with `s > 0` and a tall `P₁`.
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {M : Fin 3 → ℕ} {r s : ℕ}

/-! ## Fact 1: the off-pole cancellation from a square invertible `P₁` (stratum `r = M 0`)

`det P1u` is well-typed only when `P1u` is square (`r = M 0`). Since the statement is elaborated before
any `subst`, the input is supplied as `hr0 : r = M 0` plus the Gram det `det(P1uᵀP1u) ≠ 0` (the Gram is
square `Fin r` for any `r`) — the unconditional-on-the-box dominance lemma will produce both. -/

/-- **The square-slice column factoring `∃ K, P₂ = P₁·K`.** On `r = M 0` the front rank block `P1u` is
square; given the Gram `det(P1uᵀP1u) ≠ 0`, `P1u` is invertible (`det(P1uᵀP1u) = (det P1u)²`), so
`K := P1u⁻¹·P2u` factors `P₂ = P₁·K` (the column space of `P₁` is everything). -/
theorem P2u_factorsThrough_P1u_of_gram (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0)
    (u : Fin (routeMAmbient M) → ℝ)
    (hgram : ((P1u M hrs u).transpose * P1u M hrs u).det ≠ 0) :
    ∃ K : Matrix (Fin r) (Fin s) ℝ, P2u M hrs u = P1u M hrs u * K := by
  -- `r = M 0` makes `P1u` genuinely square; `subst` so `det`/`⁻¹` apply directly
  subst hr0
  -- `det P1u ≠ 0` from `det(P1uᵀP1u) = (det P1u)² ≠ 0`
  have hdet : (P1u M hrs u).det ≠ 0 := by
    intro h0
    apply hgram
    rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero]
  have hunit : IsUnit (P1u M hrs u).det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨(P1u M hrs u)⁻¹ * P2u M hrs u, ?_⟩
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul]

/-- **The square-slice off-pole cancellation `P₁·Λ₀ = P₂`.** Combines the column factoring
(`P2u_factorsThrough_P1u_of_gram`, needs `r = M 0` + Gram invertible) with the banked
`Lam0u_cancel_of_factoring`. The genuinely-analytic Fact 1 of `routeMCore_smearedL2`, on the stratum. -/
theorem Lam0u_cancel_of_gram_square (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0)
    (u : Fin (routeMAmbient M) → ℝ)
    (hgram : ((P1u M hrs u).transpose * P1u M hrs u).det ≠ 0) :
    P1u M hrs u * Lam0u M hrs u = P2u M hrs u := by
  obtain ⟨K, hK⟩ := P2u_factorsThrough_P1u_of_gram M hrs hr0 u hgram
  exact Lam0u_cancel_of_factoring M hrs u K hK hgram

/-! ## The Gram det from strict row diagonal dominance of `P₁` (the box-unconditional off-pole input)

`det(P1uᵀP1u) = (det P1u)²`, and on the square slice a strictly-row-diagonally-dominant `P1u` has
`det P1u ≠ 0` (Levy–Desplanques, `Core.Matrix.StrictRowDominant.det_ne_zero`). The dominance hypothesis
is the box-membership readoff (the conditioning `|P1u_ii| ≥ δ/2`, off-diagonals `≤ η = δ/(4(r−1))`,
margin `γ = δ/4`). The dominance condition is phrased entrywise, well-typed for any `r`, and `subst hr0`
makes `P1u` genuinely square so `StrictRowDominant` applies. -/

open DLNFibre.Core.Matrix in
/-- **Square `P₁` diagonal dominance ⟹ Gram det `≠ 0`.** Given `r = M 0` (square `P1u`) and the strict
row-diagonal-dominance margin (`∑_{a≠i}|P1u i a| + γ ≤ |P1u i i|`, `γ > 0`), the Gram `det(P1uᵀP1u) ≠ 0`.
`det(P1uᵀP1u) = (det P1u)²`, `det P1u ≠ 0` by Levy–Desplanques. -/
theorem gram_det_ne_of_diagDominant (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0)
    (u : Fin (routeMAmbient M) → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hdom : ∀ i : Fin (M 0),
      (∑ a ∈ Finset.univ.erase (Fin.cast hr0.symm i), |P1u M hrs u i a|) + γ
        ≤ |P1u M hrs u i (Fin.cast hr0.symm i)|) :
    ((P1u M hrs u).transpose * P1u M hrs u).det ≠ 0 := by
  -- eliminate `r` in favour of `M 0` (`subst` the variable `r`); `Fin.cast rfl` collapses to `id`
  subst hr0
  simp only [Fin.cast_eq_self] at hdom
  -- assemble `StrictRowDominant (P1u) γ`, get `det P1u ≠ 0`, then the Gram
  have hdd : StrictRowDominant (P1u M hrs u) γ := ⟨hγ, hdom⟩
  have hdet : (P1u M hrs u).det ≠ 0 := hdd.det_ne_zero
  rw [Matrix.det_mul, Matrix.det_transpose]
  exact mul_ne_zero hdet hdet

/-! ## `hUpos`: the `z`-free unit `U = ‖P₁·H̄_unit‖²` is positive (stratum `r = M 0`)

`Uunit = ∑ᵢⱼ ((P₁·H̄_unit) i j)²` is `> 0` iff the matrix `P₁·H̄_unit ≠ 0`. The angular unit `H̄_unit`
has its pivot entry `(⟨0⟩,⟨0⟩) = 1`, so `H̄_unit ≠ 0`; and on the square stratum a `det P₁ ≠ 0` `P₁`
gives `P₁·H̄_unit ≠ 0` (left-mult by an invertible matrix is injective, `P₁·0 = 0`). -/

/-- A finite double sum of squares is positive once one entry is nonzero. -/
theorem frobeniusSq_pos_of_entry_ne {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → κ → ℝ) {i₀ : ι} {j₀ : κ} (h : X i₀ j₀ ≠ 0) :
    (0 : ℝ) < ∑ i, ∑ j, (X i j) ^ 2 := by
  refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) ?_
  exact ⟨i₀, Finset.mem_univ _, Finset.sum_pos' (fun j _ => sq_nonneg _)
    ⟨j₀, Finset.mem_univ _, by positivity⟩⟩

/-- **`Uunit > 0` on the square stratum from `det P₁ ≠ 0`.** `H̄_unit` has pivot entry `1`, so it is a
nonzero matrix; left-multiplication by the invertible `P₁` keeps it nonzero, so some entry of
`P₁·H̄_unit` is nonzero and the sum of squares is positive. -/
theorem Uunit_pos_of_det_ne (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2)
    (hr0 : r = M 0) (u : Fin (routeMAmbient M) → ℝ)
    (hdet : ((P1u M hrs u).transpose * P1u M hrs u).det ≠ 0) :
    0 < Uunit M hrs hr hc u := by
  subst hr0
  -- `det P₁ ≠ 0` from the Gram
  have hdetP1 : (P1u M hrs u).det ≠ 0 := by
    intro h0; apply hdet; rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero]
  have hunit : IsUnit (P1u M hrs u).det := isUnit_iff_ne_zero.mpr hdetP1
  -- `H̄_unit ≠ 0`: its pivot entry is `1`
  have hHne : HbarUnit M hrs hr hc u ≠ 0 := by
    intro h0
    have hpiv : HbarUnit M hrs hr hc u ⟨0, hr⟩ ⟨0, hc⟩ = 1 := by
      simp only [HbarUnit]
      rw [if_pos]
      rfl
    rw [h0] at hpiv
    exact one_ne_zero hpiv.symm
  -- `P₁·H̄_unit ≠ 0` (left-mult by invertible is injective)
  have hprodne : P1u M hrs u * HbarUnit M hrs hr hc u ≠ 0 := by
    intro h0
    letI := Matrix.invertibleOfIsUnitDet (P1u M hrs u) hunit
    apply hHne
    have hz : P1u M hrs u * HbarUnit M hrs hr hc u
        = P1u M hrs u * (0 : Matrix (Fin (M 0)) (Fin (M 2)) ℝ) := by
      rw [Matrix.mul_zero]; exact h0
    exact (Matrix.mul_right_injective_of_invertible (P1u M hrs u)) hz
  -- some entry is nonzero
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hprodne
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
  rw [Uunit]
  exact frobeniusSq_pos_of_entry_ne _ (by simpa using hj)

end DLNFibre.DLN.RLCT
