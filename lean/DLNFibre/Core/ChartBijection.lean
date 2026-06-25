/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartRetraction

/-!
# `DLNFibre.Core.ChartBijection` — the set-level chart trivialization bijection (rung-2 brick 4)

The set-level trivialization the route-(c) chart AlgEquiv descends from (thread 31, step 3 geometry):
the chart `Σ^r ∩ U_Δ` is in regular bijection with the product `(base chart) × F`, via

- forward `Φ(A) = (mult A, chartGauge(mult A) • A)` — the base coordinate `mult A` together with the
  retraction `φ(A)` into `F` (`ChartRetraction.chartGauge_mem_fibre`);
- inverse `Ψ(M, B) = chartGauge(M)⁻¹ • B` — reconstruct the tuple from a base matrix `M` and a fibre
  point `B`.

The round-trips are pure group-action algebra (`smul_inv_smul` / `inv_smul_smul`) plus `mult_smul`
for the base coordinate. The single nontrivial geometric fact is that `Ψ(M, B)` has `mult = M`: by
`mult_smul`, `mult (chartGauge(M)⁻¹ • B) = L · (mult B) · H = L · E · H = M`, the factorization
direction of `normalize_chart_matrix`. Here the only place the locus relation enters.

This brick proves the two retraction round-trips (the iso at the set level); the coordinate-ring
`AlgEquiv` (and the dimension consequence) is downstream.

## Main results
- `chartGauge_smul_retraction` — `chartGauge(mult A)⁻¹ • (chartGauge(mult A) • A) = A` (Ψ∘Φ = id).
- `mult_chartGauge_inv_smul` — `mult (chartGauge(mult A)⁻¹ • (chartGauge(mult A) • A)) = mult A`.
-/

namespace DLNFibre.Core

open Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **The retraction round-trip `Ψ∘Φ = id`.** `chartGauge(mult A)⁻¹ • (chartGauge(mult A) • A) = A`:
the gauge action is a group action, so applying the gauge then its inverse is the identity. The set
bijection's left inverse (recover `A` from `(mult A, φ(A))`). -/
theorem chartGauge_smul_retraction (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) (A : Tuple (k := k) d)
    (hΔ : IsUnit (chartΔ (mult d A) hp hq).det) :
    (chartGauge d r hp hq (mult d A) hΔ)⁻¹ • (chartGauge d r hp hq (mult d A) hΔ • A) = A :=
  inv_smul_smul _ A

/-- The base coordinate is recovered: `mult (Ψ (mult A) (φ A)) = mult A`. (Immediate from the
round-trip, but stated for the bijection's base-projection.) -/
theorem mult_chartGauge_inv_smul (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) (A : Tuple (k := k) d)
    (hΔ : IsUnit (chartΔ (mult d A) hp hq).det) :
    mult d ((chartGauge d r hp hq (mult d A) hΔ)⁻¹ • (chartGauge d r hp hq (mult d A) hΔ • A))
      = mult d A := by
  rw [chartGauge_smul_retraction]

/-- **The base reconstruction `mult (Ψ(M, B)) = M`.** For a fibre point `B ∈ fibre E` (so
`mult B = E = diag(I_r,0)`) and a chart matrix `M` (`rank ≤ r`, pivot invertible), the inverse map
`Ψ(M, B) = chartGauge(M)⁻¹ • B` reconstructs the base coordinate: `mult (chartGauge(M)⁻¹ • B) = M`.
By `mult_smul` the product is `L · (mult B) · H = L · E · H = M` (the `factor_chart_matrix`
factorization). This is the surjectivity-of-base direction of the chart bijection — the only place
the locus relation (`mult B = E`) enters the inverse. (`N ≥ 1`, as `Fin (N+2)`.) -/
theorem mult_chartGauge_inv_smul_fibre {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (M : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k)
    (hΔ : IsUnit (chartΔ M hp hq).det) (hrank : M.rank ≤ r)
    (B : Tuple (k := k) d) (hB : B ∈ fibre d (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq)) :
    mult d ((chartGauge d r hp hq M hΔ)⁻¹ • B) = M := by
  rw [mem_fibre] at hB
  rw [mult_smul]
  -- the inverse gauge at the two ends, as matrices: `(P⁻¹)_last = L`, `((P⁻¹)_0)⁻¹ = H`.
  have hlast : Units.val ((chartGauge d r hp hq M hΔ)⁻¹ (Fin.last (N + 1))) = Lmatk M hp hq := by
    rw [Pi.inv_apply, chartGauge_last d r hp hq M hΔ, inv_inv, IsUnit.unit_spec]
  have hzero : Units.val (((chartGauge d r hp hq M hΔ)⁻¹ 0)⁻¹) = Hmatk M hp hq := by
    rw [Pi.inv_apply, inv_inv, chartGauge_zero d r hp hq M hΔ, IsUnit.unit_spec]
  rw [hlast, hzero, hB]
  -- now `L · E · H = M` is the factorization.
  exact factor_chart_matrix M hp hq hΔ hrank

end DLNFibre.Core
