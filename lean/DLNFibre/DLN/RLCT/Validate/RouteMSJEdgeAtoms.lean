import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

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

open MeasureTheory
open scoped BigOperators ENNReal

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

/-! ## Atom 2 — the 1D radial `∫(1+t²)^{−p}` (the coupled radial leaf after the `u = xy` sub) -/

/-- **The 1D radial integral is finite for `p > 1/2`.** `∫⁻_ℝ (1+t²)^{−p} dt < ⊤`. This is the single
coupled radial variable `u` (satred's atom 2) the corank-one 2D model factors into after the `u = xy`
substitution — NOT the full 2D integral, one variable. Finite exactly when `p > 1/2` (the `‖·‖ₑ` tail
`t^{−2p}` integrable ⟺ `2p > 1`). Via Mathlib's Japanese-bracket
`integrable_rpow_neg_one_add_norm_sq` at `E = ℝ` (`finrank = 1 < 2p`), pushing the Bochner integrability
to the `∫⁻ ofReal` finiteness (`ofReal ≤ ‖·‖ₑ`). The scaled form `∫(w+u²)^{−p} = w^{1/2−p}·(this)` (sub
`u = √w·t`) supplies the `w^{1/2−p}` pivot-energy dependence in the edge assembly. -/
theorem radial1D_lintegral_lt_top {p : ℝ} (hp : 1 / 2 < p) :
    ∫⁻ t : ℝ, ENNReal.ofReal ((1 + t ^ 2) ^ (-p)) < ⊤ := by
  have hr : (Module.finrank ℝ ℝ : ℝ) < 2 * p := by
    rw [Module.finrank_self]; push_cast; linarith
  have hint : Integrable (fun x : ℝ => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * p) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq hr
  have hfun : (fun x : ℝ => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * p) / 2))
      = (fun t : ℝ => (1 + t ^ 2) ^ (-p)) := by
    funext x
    rw [Real.norm_eq_abs, sq_abs, show (-(2 * p) / 2) = -p from by ring]
  rw [hfun] at hint
  have hfin : ∫⁻ t : ℝ, ‖(1 + t ^ 2) ^ (-p)‖ₑ < ⊤ := by
    rw [← hasFiniteIntegral_iff_enorm]; exact hint.hasFiniteIntegral
  refine lt_of_le_of_lt (lintegral_mono (fun t => ?_)) hfin
  exact Real.ofReal_le_enorm _

/-! ## Atom 3 — the σ-radial log (the cut-off `1/σ` integral producing the corank-one log) -/

/-- **The σ-radial log identity.** `∫_{σ ∈ [τ,1]} σ⁻¹ dσ = log(1/τ)` (`τ > 0`). This is the elementary
`1/|y|`-Jacobian integral (satred's atom 3) that produces the corank-one **log**: after the `u = xy`
substitution in the scalar model `∫(w+x²y²)^{−p}`, the `y`-integral of the carried Jacobian `|y|⁻¹` over
the radial cut-off `[τ,1]` is exactly this log. Thin wrapper over `intervalIntegral.integral_inv_of_pos`. -/
theorem sigmaLog_integral {τ : ℝ} (hτ0 : 0 < τ) :
    ∫ σ in τ..1, σ⁻¹ = Real.log τ⁻¹ := by
  rw [integral_inv_of_pos hτ0 (by norm_num : (0:ℝ) < 1), one_div]

/-- **The σ-radial log, folded (the form the edge δ-slack consumes).** `1 + ∫_{[τ,1]} σ⁻¹ dσ`
`≤ (1 + 1/δ)·τ^{−δ}` for `τ ∈ (0,1]`, `δ > 0`. Composes the σ-radial log (atom 3) with the δ-fold
(atom 2): the corank-one log `∫σ⁻¹ = log(1/τ)`, incremented by `1`, is dominated by an arbitrarily-small
negative power `τ^{−δ}`. This is the per-exponent δ-slack bound: it converts the log into a `τ^{−δ}` the
arity-IH's open exponent headroom (`c' − ab/2 + δ < ½·minAdm(redChain)`) absorbs. The `+1` covers the
constant part of the morse residual. -/
theorem one_add_sigmaLog_le_rpow {τ δ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hδ : 0 < δ) :
    1 + ∫ σ in τ..1, σ⁻¹ ≤ (1 + 1 / δ) * τ ^ (-δ) := by
  rw [sigmaLog_integral hτ0]
  exact one_add_log_inv_le_rpow hτ0 hτ1 hδ

end DLNFibre.DLN.RLCT
