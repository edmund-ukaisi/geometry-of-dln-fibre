import DLNFibre.DLN.RLCT.Validate.RouteMSchurRectAngular

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurRectChart` — the RECTANGULAR per-chart radial factor (item 4 foundation)

The radial-axis Tonelli factor for the rectangular `mn`-chart cover. On a single radial-`Δ`-blow-up
entry-chart `pv` of the rectangular core `frobSq (Δ·S)` (`Δ : Fin m → Fin n`), the per-chart integral
Tonelli-separates the a-axis divisor `|a|^{(mn−1)−2c'}` (finite ⟺ `c' < mn/2`, the rectangular radial cap)
from the inner angular `innerSRect`-integral (supplied by the carve, item 3). This file lands the
INDEPENDENT radial half (`radial_aAxis_divisor_rect`), sorry-free; the full per-chart assembly
(`schur_matBoxRect_chart_lt_top`) consumes it + the carve at integration time.

The exponent is `mn − 1 − 2c'` (the radial Jacobian `|a|^{mn−1}` from `pivotBlowupOnDeriv_det` at
`N = m*n`, against the degree-2 scale `(a²·…)^{−c'}`), vs the square `r² − 1 − 2c'`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- **The rectangular radial a-axis divisor finiteness.** `∫_{[−T,T]} |a|^{(mn−1)−2c'} da < ⊤` for
`c' < mn/2` — the radial Jacobian `|a|^{mn−1}` against the degree-2 scale `(a²·…)^{−c'} = |a|^{−2c'}·…`.
The exponent `(mn−1)−2c' > −1 ⟺ c' < mn/2` is the rectangular radial cap. The asymmetric
`radial_aAxis_divisor_lt_top`; proved from the 1-D monomial atom `abs_rpow_lintegral_Icc_lt_top`. -/
theorem radial_aAxis_divisor_rect (m n : ℕ) (hmn : 1 ≤ m * n) (T : ℝ) (hT : 0 < T)
    (c' : ℝ) (hc' : c' < ((m * n : ℕ) : ℝ) / 2) :
    ∫⁻ a in Set.Icc (-T) T, ENNReal.ofReal (|a| ^ (((m * n : ℕ) : ℝ) - 1 - 2 * c')) < ⊤ := by
  apply abs_rpow_lintegral_Icc_lt_top T hT (((m * n : ℕ) : ℝ) - 1 - 2 * c')
  -- (mn − 1) − 2c' > −1  ⟺  c' < mn/2
  have h1 : (1 : ℝ) ≤ ((m * n : ℕ) : ℝ) := by exact_mod_cast hmn
  linarith [hc']

/-- The radial Jacobian det of the rectangular `mn`-chart blow-up is `|y_pv|^{mn−1}`
(`pivotBlowupOnDeriv_det` at `N = m*n`, `active = univ`, `card = m*n`). -/
theorem pivotBlowupOnDeriv_det_rect (m n : ℕ) (pv : Fin (m * n)) (y : Fin (m * n) → ℝ) :
    |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (m * n))) pv y).det|
      = |y pv| ^ (m * n - 1) := by
  rw [pivotBlowupOnDeriv_det (Finset.univ : Finset (Fin (m * n))) pv (Finset.mem_univ pv) y,
    Finset.card_univ, Fintype.card_fin, abs_pow]

end DLNFibre.DLN.RLCT
