import DLNFibre.DLN.RLCT.Validate.RouteMSmearedTelescope
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedRateBridge
import DLNFibre.DLN.RLCT.Validate.RouteM221

/-!
# `RouteMSmearedChartL2` — the L=2 opaque-width smeared chart-eval (`prod M chart = z•(P₁·H̄)`)

The L=2 (single front factor, `P = A⁰`) discharge of the chart-eval gap from `RouteMSmearedRateBridge`:
`prod M (chart) = z • (P₁·H̄)` over OPAQUE widths, where the deepest factor `A¹` is row-split `r ⊕ s`
(top `r` rows the radial-minus-shear `z·H̄ − Λ₀·S_bot`, bottom `s` rows the residual `S_bot`).

The opaque-width transport is isolated in ONE reindex `e := finSumFinEquiv.trans (finCongr hrs) :
Fin r ⊕ Fin s ≃ Fin (M 1)` (Codex `chart-encoding-answer` §1, the lowest-cast option): the entrywise
product sum `∑ k1 : Fin (M 1)` reindexes by `← Equiv.sum_comp e` to a sum over `Fin r ⊕ Fin s`, then
`Fintype.sum_sum_type` splits it and `telescope_collapse` collapses it (`P₁·Λ₀ = P₂`). No
`Matrix.fromBlocks` reindexing, no `Fin.addCases` cast exposure — the cast lives only in the sum-reindex.

Feeds `routeMCore_rate_of_prod_collapsed` to give the L=2 smeared rate `routeMCore M (φ u) = z²·U`.
The remaining gap shrinks to: build the flat chart `φ_sm` so that `(paramsEquivFlat M).symm (φ u)` IS
this `chartL2Params` (the pack/reshape), and supply the front-bottleneck factoring + the off-pole
hypotheses. The L ≥ 3 front-prefix-product needs `prodAux_front_peel` (a separate sub-tide).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

/-- The opaque-width deepest-width reindex `e : Fin r ⊕ Fin s ≃ Fin (M 1)` (`finSumFinEquiv` then the
`r + s = M 1` cast). The single carrier of the dependent-`Fin` transport. -/
noncomputable def deepWidthEquiv {r s : ℕ} {M1 : ℕ} (hrs : r + s = M1) :
    Fin r ⊕ Fin s ≃ Fin M1 :=
  (finSumFinEquiv).trans (finCongr hrs)

/-- **The L=2 chart deepest factor** `A¹ : Matrix (Fin (M 1)) (Fin (M 2)) ℝ`, row-split via
`deepWidthEquiv`: a row `k : Fin (M 1)` is the radial-minus-shear `(z·H̄ − Λ₀·S_bot)` row if `k` lands in
the top `r` block, else the residual `S_bot` row. The opaque-width analog of `(2,3,1)`'s explicit
`chartA1_231`. -/
noncomputable def chartL2Deep {r s M1 M2 : ℕ} (hrs : r + s = M1)
    (z : ℝ) (Hbar : Matrix (Fin r) (Fin M2) ℝ) (Sbot : Matrix (Fin s) (Fin M2) ℝ)
    (Λ₀ : Matrix (Fin r) (Fin s) ℝ) :
    Matrix (Fin M1) (Fin M2) ℝ :=
  fun k j => deepBlock z Hbar Sbot Λ₀ ((deepWidthEquiv hrs).symm k) j

/-- **The L=2 chart `Params`** `(A⁰, A¹)` with `A⁰` the free front factor and `A¹` the row-split deepest
factor (`chartL2Deep`). -/
noncomputable def chartL2Params (M : Fin 3 → ℕ) {r s : ℕ} (hrs : r + s = M 1)
    (A0 : Matrix (Fin (M 0)) (Fin (M 1)) ℝ)
    (z : ℝ) (Hbar : Matrix (Fin r) (Fin (M 2)) ℝ) (Sbot : Matrix (Fin s) (Fin (M 2)) ℝ)
    (Λ₀ : Matrix (Fin r) (Fin s) ℝ) : Params M :=
  Fin.cons A0 (Fin.cons (chartL2Deep hrs z Hbar Sbot Λ₀) (fun t => t.elim0))

/-- **The L=2 chart-eval collapse** `prod M (chartL2Params …) = z • (P₁·H̄)`. With `P₁ = A⁰∘(top cols)`,
`P₂ = A⁰∘(residual cols)` (selected via `deepWidthEquiv`), off the shear cancellation `P₁·Λ₀ = P₂`, the
deepest product is the pure radial. Entrywise: `prod_two_layer221` → reindex the `Fin (M 1)` sum by
`deepWidthEquiv` (`Equiv.sum_comp`) → `Fintype.sum_sum_type` split → `deepBlock_collapse`. -/
theorem prod_chartL2Params (M : Fin 3 → ℕ) {r s : ℕ} (hrs : r + s = M 1)
    (A0 : Matrix (Fin (M 0)) (Fin (M 1)) ℝ)
    (z : ℝ) (Hbar : Matrix (Fin r) (Fin (M 2)) ℝ) (Sbot : Matrix (Fin s) (Fin (M 2)) ℝ)
    (Λ₀ : Matrix (Fin r) (Fin s) ℝ)
    (P₁ : Matrix (Fin (M 0)) (Fin r) ℝ) (P₂ : Matrix (Fin (M 0)) (Fin s) ℝ)
    (hP₁ : ∀ i k, P₁ i k = A0 i (deepWidthEquiv hrs (Sum.inl k)))
    (hP₂ : ∀ i k, P₂ i k = A0 i (deepWidthEquiv hrs (Sum.inr k)))
    (hcancel : P₁ * Λ₀ = P₂) :
    prod M (chartL2Params M hrs A0 z Hbar Sbot Λ₀) = z • (P₁ * Hbar) := by
  funext i j
  rw [prod_two_layer221 M (chartL2Params M hrs A0 z Hbar Sbot Λ₀) i j]
  -- the chart layers: `A 0 = A0`, `A 1 = chartL2Deep …`
  have h0 : (chartL2Params M hrs A0 z Hbar Sbot Λ₀) 0 = A0 := rfl
  have h1 : (chartL2Params M hrs A0 z Hbar Sbot Λ₀) 1 = chartL2Deep hrs z Hbar Sbot Λ₀ := rfl
  rw [h0, h1]
  -- reindex `∑ k1 : Fin (M 1)` by `deepWidthEquiv` to a sum over `Fin r ⊕ Fin s`
  rw [← Equiv.sum_comp (deepWidthEquiv hrs)
    (fun k1 => A0 i k1 * chartL2Deep hrs z Hbar Sbot Λ₀ k1 j)]
  -- `chartL2Deep (e x) j = deepBlock … x j` (the `e.symm (e x) = x` round-trip)
  have hdeep : ∀ x, chartL2Deep hrs z Hbar Sbot Λ₀ (deepWidthEquiv hrs x) j
      = deepBlock z Hbar Sbot Λ₀ x j := by
    intro x; rw [chartL2Deep, Equiv.symm_apply_apply]
  simp only [hdeep]
  -- split the `Fin r ⊕ Fin s` sum
  rw [Fintype.sum_sum_type]
  -- this is exactly the `(i,j)` entry of `Pfront · deepBlock` with `Pfront := A0 ∘ e`
  have hcollapse := deepBlock_collapse z (fun i' x => A0 i' (deepWidthEquiv hrs x))
    Hbar Sbot Λ₀ P₁ P₂ hP₁ hP₂ hcancel
  -- read the `(i,j)` entry of `hcollapse`
  have hij := congrFun (congrFun hcollapse i) j
  rw [Matrix.mul_apply, Fintype.sum_sum_type] at hij
  simp only [deepBlock, Sum.elim_inl, Sum.elim_inr] at hij
  rw [Matrix.smul_apply, smul_eq_mul] at hij
  -- the LHS sums match `hij`'s LHS (the `Pfront · deepBlock` entry)
  rw [Matrix.smul_apply, smul_eq_mul]
  convert hij using 2 <;>
    simp only [deepBlock, Sum.elim_inl, Sum.elim_inr, Matrix.mul_apply]

/-! ## The L=2 smeared `routeMCore` rate (the chart-eval discharged) -/

/-- **The L=2 smeared chart in flat coordinates** `phiL2 := paramsEquivFlat M ∘ chartL2Params`. -/
noncomputable def phiL2 (M : Fin 3 → ℕ) {r s : ℕ} (hrs : r + s = M 1)
    (A0 : Matrix (Fin (M 0)) (Fin (M 1)) ℝ)
    (z : ℝ) (Hbar : Matrix (Fin r) (Fin (M 2)) ℝ) (Sbot : Matrix (Fin s) (Fin (M 2)) ℝ)
    (Λ₀ : Matrix (Fin r) (Fin s) ℝ) : Fin (routeMAmbient M) → ℝ :=
  paramsEquivFlat M (chartL2Params M hrs A0 z Hbar Sbot Λ₀)

/-- **The L=2 smeared rate** `routeMCore M (phiL2 …) = z²·‖P₁·H̄‖²_F`. The chart-eval `prod_chartL2Params`
(the deepest product collapses to `z•(P₁H̄)`) fed through `routeMCore_rate_of_prod_collapsed`. The
complete L=2 smeared rate `F = z²·U` with the `z`-free polynomial unit `U = ‖P₁·H̄‖²_F`, off the shear
pole (`P₁·Λ₀ = P₂`). -/
theorem routeMCore_phiL2 (M : Fin 3 → ℕ) {r s : ℕ} (hrs : r + s = M 1)
    (A0 : Matrix (Fin (M 0)) (Fin (M 1)) ℝ)
    (z : ℝ) (Hbar : Matrix (Fin r) (Fin (M 2)) ℝ) (Sbot : Matrix (Fin s) (Fin (M 2)) ℝ)
    (Λ₀ : Matrix (Fin r) (Fin s) ℝ)
    (P₁ : Matrix (Fin (M 0)) (Fin r) ℝ) (P₂ : Matrix (Fin (M 0)) (Fin s) ℝ)
    (hP₁ : ∀ i k, P₁ i k = A0 i (deepWidthEquiv hrs (Sum.inl k)))
    (hP₂ : ∀ i k, P₂ i k = A0 i (deepWidthEquiv hrs (Sum.inr k)))
    (hcancel : P₁ * Λ₀ = P₂) :
    routeMCore M (phiL2 M hrs A0 z Hbar Sbot Λ₀)
      = z ^ 2 * ∑ i, ∑ j, ((P₁ * Hbar) i j) ^ 2 := by
  -- `(paramsEquivFlat M).symm (phiL2 …) = chartL2Params …`, then `prod_chartL2Params`
  have hcollapse : prod M ((paramsEquivFlat M).symm (phiL2 M hrs A0 z Hbar Sbot Λ₀))
      = z • (P₁ * Hbar) := by
    rw [phiL2, MeasurableEquiv.symm_apply_apply,
      prod_chartL2Params M hrs A0 z Hbar Sbot Λ₀ P₁ P₂ hP₁ hP₂ hcancel]
  exact routeMCore_rate_of_prod_collapsed M
    (fun _ => phiL2 M hrs A0 z Hbar Sbot Λ₀) (0 : Fin (routeMAmbient M) → ℝ) z (P₁ * Hbar) hcollapse

end DLNFibre.DLN.RLCT
