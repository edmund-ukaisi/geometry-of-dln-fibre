import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.style.longLine false

/-!
# `RouteMSJEdgeAtoms` — the two network-free atoms of the (D) corank-one edge brick

Thread `genm-tideD-joint` (aoyagi-full Stage 2), the joint corank-one / rank-sector resolution (D).
This file isolates the **two genuinely-new elementary atoms** the corank-one edge argument rests on
(D-cert v3 §3, edgebrick's corank-one analysis). Both are network-free (`Mathlib`-only, no `DLNFibre`
dependency) and reusable:

* **The C-non-degeneracy (surjectivity).** `C ↦ (of C).mulVec v` (`ℝ^{a×u} → ℝ^a`) is **surjective**
  whenever `v ≠ 0`. This is the enabling lemma for the C-integration to absorb the corank-one log:
  at a rank-`(b−1)` point of `K = A_cor·Zf` the morse residual carries `‖C·Q̃ₚ·η‖²` with the fragile
  direction `v = Q̃ₚ·η` (nonzero generically, `Q̃ₚ` full rank), and the map `C ↦ C·v` being **onto**
  is what lets the C-integral supply the missing direction. It is a property of the **map** (full-rank
  Jacobian), NOT a uniform lower bound `‖C·v‖ ≥ c` (which is FALSE at `C = 0 ∈ box`) — the KILL-guard
  in satred's D-cert. The witness is `C = (y ⊗ v) / ‖v‖²`.

* **The δ-slack log fold.** For `τ ∈ (0,1]` and `δ > 0`, `1 + log(1/τ) ≤ (1 + 1/δ)·τ^{−δ}` — a
  logarithm is beaten by every negative power. This folds the corank-one **log** (the `s = 0/1` rank
  tie at the edge; scalar model `∫(w+x²y²)^{−p} ≍ w^{1/2−p}·log(1/w)`) into an arbitrarily-small
  power `τ^{−δ}`, so the arity-IH on the **open** exponent range `c' − ab/2 + δ < ½·minAdm(redChain)`
  closes finiteness at the true value `½·minAdm`. The deliverable is the δ-slack per-exponent bound,
  NEVER a multiplicity `m` and NEVER "uniform-C removes the log" (both wrong, satred/edgebrick).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

/-! ## Atom 1 — the C-non-degeneracy surjectivity -/

/-- **The corank-one C-non-degeneracy.** For a nonzero `v : Fin u → ℝ`, the linear map
`C ↦ (Matrix.of C).mulVec v` from `a×u` matrices to `ℝ^a` is **surjective**: every target `y : Fin a → ℝ`
is hit, by the explicit witness `C i j = y i · v j / ‖v‖²` (rank-one `y ⊗ v` scaled by `1/‖v‖²`). This is
the enabling non-degeneracy for the edge C-integration (`v = Q̃ₚ·η`, the lost row-direction of the
rank-`(b−1)` corank block); it is surjectivity of the MAP, not a uniform bound (false at `C = 0`). -/
theorem mulVec_of_surjective {u a : ℕ} (v : Fin u → ℝ) (hv : v ≠ 0) :
    Function.Surjective
      (fun C : Fin a → Fin u → ℝ => (Matrix.of C).mulVec v) := by
  classical
  -- `S = ‖v‖² > 0`
  set S : ℝ := ∑ k, (v k) ^ 2 with hS
  have hSpos : 0 < S := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
    refine Finset.sum_pos' (fun i _ => by positivity) ⟨j, Finset.mem_univ j, ?_⟩
    have hj0 : v j ≠ (0 : Fin u → ℝ) j := hj
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj0))
  intro y
  refine ⟨fun i j => y i * v j / S, ?_⟩
  funext i
  -- `(of C).mulVec v i = ∑ j, (y i * v j / S) * v j = (y i / S)·∑ j v j² = y i`
  simp only [Matrix.mulVec, Matrix.of_apply, dotProduct]
  have hterm : ∀ j, y i * v j / S * v j = (y i / S) * (v j) ^ 2 := fun j => by ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, ← hS,
    div_mul_cancel₀ _ (ne_of_gt hSpos)]

/-! ## Atom 2 — the δ-slack log fold -/

/-- **The δ-slack log fold.** For `τ ∈ (0,1]` and `δ > 0`,
`1 + log(1/τ) ≤ (1 + 1/δ)·τ^{−δ}`. A logarithm is dominated by every negative power of `τ`; this folds
the corank-one rank-tie **log** into an arbitrarily-small extra power `τ^{−δ}`, which the arity-IH's open
exponent headroom absorbs. Via `Real.log_le_rpow_div` (`log x ≤ x^δ/δ`) at `x = τ⁻¹`, plus
`1 ≤ τ^{−δ}` on `(0,1]`. -/
theorem one_add_log_inv_le_rpow {τ δ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hδ : 0 < δ) :
    1 + Real.log τ⁻¹ ≤ (1 + 1 / δ) * τ ^ (-δ) := by
  have hτ0' : (0 : ℝ) ≤ τ := le_of_lt hτ0
  have hinv0 : (0 : ℝ) ≤ τ⁻¹ := le_of_lt (inv_pos.mpr hτ0)
  have h1le : (1 : ℝ) ≤ τ⁻¹ := (one_le_inv₀ hτ0).mpr hτ1
  -- `τ^{−δ} = (τ⁻¹)^δ ≥ 1`
  have hpow_eq : τ ^ (-δ) = τ⁻¹ ^ δ := by
    rw [Real.rpow_neg hτ0', ← Real.inv_rpow hτ0']
  have hpow_ge1 : (1 : ℝ) ≤ τ ^ (-δ) := by
    rw [hpow_eq]; exact Real.one_le_rpow h1le (le_of_lt hδ)
  -- `log(1/τ) ≤ (τ⁻¹)^δ/δ = τ^{−δ}/δ`
  have hlog : Real.log τ⁻¹ ≤ τ ^ (-δ) / δ := by
    have := Real.log_le_rpow_div hinv0 hδ
    rwa [← hpow_eq] at this
  -- assemble: `1 + log(1/τ) ≤ τ^{−δ} + τ^{−δ}/δ = (1 + 1/δ)·τ^{−δ}`
  have : 1 + Real.log τ⁻¹ ≤ τ ^ (-δ) + τ ^ (-δ) / δ := by linarith
  calc 1 + Real.log τ⁻¹ ≤ τ ^ (-δ) + τ ^ (-δ) / δ := this
    _ = (1 + 1 / δ) * τ ^ (-δ) := by ring

/-- One-le helper needed inline (kept as a lemma for reuse): on `(0,1]` the negative power `τ^{−δ}`
(`δ ≥ 0`) is `≥ 1`. -/
theorem one_le_rpow_neg_of_le_one {τ δ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hδ : 0 ≤ δ) :
    (1 : ℝ) ≤ τ ^ (-δ) := by
  have hτ0' : (0 : ℝ) ≤ τ := le_of_lt hτ0
  rw [Real.rpow_neg hτ0', ← Real.inv_rpow hτ0']
  exact Real.one_le_rpow ((one_le_inv₀ hτ0).mpr hτ1) hδ

end DLNFibre.DLN.RLCT
