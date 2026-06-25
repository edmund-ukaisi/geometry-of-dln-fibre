/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartSection
import DLNFibre.Core.EndBaseChangeSweep

/-!
# `DLNFibre.Core.ChartRetraction` — the tuple-level chart retraction onto `fibre E` (rung-2 brick 3)

The tuple-level lift of the matrix-heart normalization (`ChartSection.normalize_chart_matrix`):
the **chart retraction** `φ(A) = chartGauge(mult A) • A`, a regular map that carries the chart
`Σ^r ∩ U_Δ` onto the fibre `F = fibre d E` over the rank-`r` normal form `E = diag(I_r, 0)`.

The gauge `chartGauge M : BaseChangeGroup d` is the `k`-valued endpoint gauge built from `M`'s
Schur blocks: `L⁻¹` at the target vertex `last N`, `H` at the source vertex `0`, `1` interior
(mirroring `SchurGauge.endpointGauge`, but over `k` with the concrete `Lmatk`/`Hmatk`). By
`mult_smul`, `mult (chartGauge M • A) = L⁻¹ · mult A · H⁻¹`; at `M = mult A` on the chart this is
`normalize_chart_matrix`, equal to `E`. So `chartGauge(mult A) • A ∈ fibre E` — the retraction lands
in `F` **because of the rank relation** (the only place the locus equation enters).

## Main results
- `chartGauge` — the `k`-valued endpoint gauge `BaseChangeGroup` from a target matrix `M`.
- `chartGauge_mem_fibre` — `chartGauge(mult A) • A ∈ fibre E` for `A` in the chart with `rank ≤ r`.
-/

namespace DLNFibre.Core

open Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **The `k`-valued endpoint chart gauge.** From a target matrix `M : Mat_{d_N × d_0}(k)` with the
top-left `r×r` pivot block invertible, the `BaseChangeGroup` carrying `L⁻¹` (= `(Lmatk M)⁻¹`, the
target-vertex `p×p` unit) at `last N`, `H` (= `Hmatk M`, the source-vertex `q×q` unit) at `0`, and
`1` at every interior vertex. The units that, by `mult_smul`, conjugate `mult A` to its normal form. -/
noncomputable def chartGauge (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0)
    (M : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (hΔ : IsUnit (chartΔ M hp hq).det) :
    BaseChangeGroup (k := k) d :=
  fun v ↦
    if hv0 : v = 0 then
      cast (by rw [hv0]) (isUnit_Hmatk M hp hq hΔ).unit
    else if hvl : v = Fin.last N then
      cast (by rw [hvl]) (isUnit_Lmatk M hp hq).unit⁻¹
    else 1

/-- The source-vertex unit of the chart gauge is `H` (the `cast` at `v = 0` is the identity). -/
theorem chartGauge_zero (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0)
    (M : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (hΔ : IsUnit (chartΔ M hp hq).det) :
    (chartGauge d r hp hq M hΔ) 0 = (isUnit_Hmatk M hp hq hΔ).unit := by
  unfold chartGauge; rw [dif_pos rfl]; rfl

/-- The target-vertex unit of the chart gauge is `L⁻¹` (the `cast` at `v = last N` is the identity;
needs `N ≥ 1` so `last N ≠ 0`). -/
theorem chartGauge_last {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (M : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k)
    (hΔ : IsUnit (chartΔ M hp hq).det) :
    (chartGauge d r hp hq M hΔ) (Fin.last (N + 1)) = (isUnit_Lmatk M hp hq).unit⁻¹ := by
  unfold chartGauge
  rw [dif_neg Fin.last_pos.ne', dif_pos rfl]; rfl

/-! ## The retraction lands in the normal-form fibre -/

/-- **The chart retraction lands in `fibre E`.** For `A` in the chart `Σ^r ∩ U_Δ` (i.e.
`rank (mult A) ≤ r` and the top-left pivot block of `mult A` invertible), the gauge translate
`chartGauge (mult A) • A` lies in the fibre over the rank-`r` normal form `E = diag(I_r, 0)`. By
`mult_smul` the product transforms by the two end gauges to `L⁻¹ · mult A · H⁻¹`, which is `E` by
`normalize_chart_matrix`. The retraction onto `F` (`N ≥ 1`, here as `Fin (N+2)`). -/
theorem chartGauge_mem_fibre {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (A : Tuple (k := k) d)
    (hΔ : IsUnit (chartΔ (mult d A) hp hq).det) (hrank : (mult d A).rank ≤ r) :
    chartGauge d r hp hq (mult d A) hΔ • A
      ∈ fibre d (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq) := by
  rw [mem_fibre, mult_smul]
  -- the two end gauges: `P_last = L⁻¹`, `P_0 = H` (so `(P_0)⁻¹ = H⁻¹`).
  rw [chartGauge_last d r hp hq (mult d A) hΔ, chartGauge_zero d r hp hq (mult d A) hΔ]
  -- now `L⁻¹ · mult A · H⁻¹ = E` is the matrix-heart normalization.
  rw [Matrix.coe_units_inv, Matrix.coe_units_inv, IsUnit.unit_spec, IsUnit.unit_spec]
  exact normalize_chart_matrix (mult d A) hp hq hΔ hrank

end DLNFibre.Core
