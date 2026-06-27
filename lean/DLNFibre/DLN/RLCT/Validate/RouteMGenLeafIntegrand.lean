import DLNFibre.DLN.RLCT.Validate.RouteMGenChartId
import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart

/-!
# `RouteMGenLeafIntegrand` — the det-INDEPENDENT `NodeAchieverChart` fields ∀M (the reusable algebra)

The `NodeAchieverChart M` bundle's `leaf_integrand` field is purely ALGEBRAIC in the rate identity
`F ∘ φ = (u_p)²·V` — it does NOT need the Jacobian determinant (the det only enters `cov`). This module
banks that algebra M-agnostically, plus `VvalGen ≥ 0`:

* `leaf_integrand_of_rate` — for ANY ambient `N`, pivot `p`, exponents `leafH`, loss `F`, unit `V ≥ 0`
  with `F x = (x p)²·V x`: `(∏_j |x_j|^{leafH j})·|F x|^{−c} = monomialIntegrand N (δ_p) leafH c x ·(V x)^{−c}`.
  The general form of `leaf_integrand3333`/`leaf_integrand4422`, det-FREE.
* `VvalGen_nonneg` — `0 ≤ VvalGen` (the ∀M unit factor is a sum of squares).

These are two of the `NodeAchieverChart M` fields, fillable ∀M from the banked rate engine
(`routeMCore_phiGen`). The REMAINING fields — `cov` (the Jacobian det `|det Dφ| = ∏|u_j|^{leafH j}` +
the triangular injectivity) and the flat coordinatization of `φ` as `(Fin N → ℝ) → (Fin N → ℝ)` — are the
residual design problem (the parametric full-ambient Schur-frame/LDU determinant; see thread 35's wall note).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure algebra; no S2).
-/

open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **`VvalGen ≥ 0`** — the ∀M unit factor `V = ‖Hr‖²` is a sum of squares. -/
theorem VvalGen_nonneg (u : ℝ) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) :
    0 ≤ VvalGen u M t B hle := by
  unfold VvalGen
  positivity

/-- **The det-independent leaf-integrand algebra (∀N, ∀ leafH, ∀ pivot).** Given the rate identity
`F x = (x p)²·V x` with `V ≥ 0`, the leaf-integrand identity
`(∏_j |x_j|^{leafH j})·|F x|^{−c} = monomialIntegrand N (nodeLeafK N p) leafH c x ·(V x)^{−c}` holds for
ANY exponent vector `leafH`. This is the `NodeAchieverChart.leaf_integrand` field, reduced to the rate
identity (NO Jacobian determinant): the loss base `∏|x_j|^{2·(δ_p)_j} = |x_p|²` factors `|F x|^{−c} =
(|x_p|²)^{−c}·(V x)^{−c}`, and `∏|x_j|^{leafH j}` cancels on both sides. -/
theorem leaf_integrand_of_rate {N : ℕ} (p : Fin N) (leafH : Fin N → ℕ)
    (F : (Fin N → ℝ) → ℝ) (Vf : (Fin N → ℝ) → ℝ)
    (hrate : ∀ x, F x = (x p) ^ 2 * Vf x) (hVnn : ∀ x, 0 ≤ Vf x)
    (c : ℝ) (x : Fin N → ℝ) :
    (∏ j, |x j| ^ (leafH j)) * |F x| ^ (-c)
      = monomialIntegrand N (nodeLeafK N p) leafH c x * (Vf x) ^ (-c) := by
  unfold monomialIntegrand
  have hloss : (∏ j, |x j| ^ (2 * (nodeLeafK N p) j)) = |x p| ^ 2 := by
    rw [Finset.prod_eq_single p]
    · simp [nodeLeafK]
    · intro j _ hj; simp [nodeLeafK, hj]
    · intro h; exact absurd (Finset.mem_univ p) h
  rw [hloss, hrate]
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (hVnn x)),
    Real.mul_rpow (sq_nonneg _) (hVnn x), ← sq_abs (x p)]
  ring

end DLNFibre.DLN.RLCT
