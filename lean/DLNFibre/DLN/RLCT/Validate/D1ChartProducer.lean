import DLNFibre.DLN.RLCT.Foundations.S1QuasiSplit
import DLNFibre.DLN.RLCT.Validate.DeepestMinRlct

/-!
# `DLNFibre.DLN.RLCT.Validate.D1ChartProducer` — the D1 (★) chart-producer skeleton (L = 2)

Use-site for the banked quasi-splitting engine `rlct_quasiSplit_ge` (`Foundations.S1QuasiSplit`).
Goal: the D1 obligation (★)

    nReg/2 + rlctAtOn(core)(deepest-core) ≤ rlctAt (dlnLoss H B) v   (at a general optimal `v`)

which feeds the banked `deepest_le_of_optimal_via_L2_ge` (`DeepestMinRlct`) ⟹
`rlctAt_deepest_le_of_optimal` ⟹ D1 (rung 2/5). The loss `dlnLoss H B A = ∑ᵢⱼ ((prod A−B)ᵢⱼ)²` is
a sum of squares of the smooth entries `g_{ij}(A) = (prod A − B)_{ij}` — exactly the
`f = ∑ g_k²` shape the engine targets, `m = nReg = r(H⁰+Hᴸ−r)` the count of independent gradients.

## What this banks (PART (a)) and what it surfaces (PART (b))

**PART (a) — `rlctAt_ge_nReg_add_slice` (the (★)-as-`hAtV` reduction, BANKED).** Given the IFT-chart
producer's outputs as hypotheses (the chart transfer `rlctAt (dlnLoss H B) v = rlctAtOn F (0,t0)`,
banked `rlctAtOn_boundedUnit_localHomeomorph` discharges it; the post-chart sum-of-squares form
`F = ∑s² + Q`, `Q ≥ 0`; the slice residual `R = Q(0,·)`, measurable a.e.-nonzero; the constant
comparison `∑s² + R ≤ C·F` near `(0,t0)`), the engine gives `nReg/2 + rlctAtOn R t0 ≤
rlctAt (dlnLoss H B) v` — the `hAtV` shape `deepest_le_of_optimal_via_L2_ge` consumes, with
`coreV := rlctAtOn R t0`. Mechanical: reuses the banked engine + the chart-transfer equality.

**PART (b) — the residual-core comparison (VERIFY-FIRST, decorrelated pen-and-paper, 2026-06-29).**
Setting `coreV := rlctAtOn R t0` (NOT a separate `v−core` map) makes `hAtV` the engine output;
the SOLE remaining obligation is `hCore : coreDeepest ≤ rlctAtOn R t0`, i.e. `rlctAtOn R 0 ≥
rlctAtOn (core) 0`. The pen-and-paper VERIFIED (exact algebra, L=2, r=1, reduced widths
M ∈ {(1,1,1),(2,2,2),(1,2,1)}): `R = ‖Schur complement of A₁A₂‖² · unit`, with the EXACT polynomial
identity `R|_K = core` (`K` the gradient-kernel slice through `0`) and the degree-`2L` leading form
of `R` equal to `core`; `rlctAtOn R 0 = coreDeepest` TIGHT. The gap is **NOT** the #44 gauge slice;
one **network-free leading-form RLCT lower bound**: `rlctAtOn R 0 ≥ rlctAtOn core 0` given `R`
real-analytic, `R|_K = core`, `core` the degree-`2L` leading form of `R`. (Bare slice-monotonicity
`rlct(F) ≥ rlct(F|_K)` is FALSE without `F|_K ≢ 0`; here `R|_K = core ≢ 0` avoids that, but
the lemma is not free — cleanest discharge reuses R1's resolution of `core`.)

Scope L = 2 (general-L = the named wall #120). This file does NOT close (★): it BANKS the mechanical
reduction and names the two open producer obligations precisely (the IFT chart + the leading-form
comparison), so the controller routes the leading-form lemma to the R1-resolution / #44-Fix-B work.
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

/-- **PART (a): the (★)-as-`hAtV` reduction** (mechanical; the chart producer's wiring). Given the
IFT-chart producer's outputs at a general optimal `v`, packaged on the flat product space
`(Fin m → ℝ) × Y` (the `Params H`-flattening the producer supplies), the engine `rlct_quasiSplit_ge`
delivers `(★)`'s `hAtV` side: `nReg/2 + rlctAtOn R t0 ≤ rlctAt (dlnLoss H B) v`, with
`coreV := rlctAtOn R t0`. The hypotheses are EXACTLY the producer obligations:

  * `hchart` — the chart transfer (banked `rlctAtOn_boundedUnit_localHomeomorph` at the producer;
    IFT chart `Φ` fixing the flat origin, bounded-unit Jacobian);
  * `hF` — the post-chart sum-of-squares form (the `g_{ij}`-built chart; the `nReg` active functions
    become the coordinates `sᵢ`);
  * `hR`/`hRne` — the slice residual `R = Q(0,·)`, measurable, a.e.-nonzero near `t0`;
  * `hcmp` — the constant comparison (`C¹` Lipschitz quasi-split, `coupled_controls_slice` summed
    over the inactive index).

After this, the remaining D1 obligation is `hCore : coreDeepest ≤ rlctAtOn R t0` (PART (b)). -/
theorem rlctAt_ge_nReg_add_slice {L m : ℕ} {Y : Type*}
    [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y]
    (H : Fin (L + 1) → ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (v : Params H)
    (F : (Fin m → ℝ) × Y → ℝ) (Q : (Fin m → ℝ) × Y → ℝ) (R : Y → ℝ) (t0 : Y)
    (hchart : rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin m → ℝ), t0))
    (hF : ∀ p, F p = (∑ i, p.1 i ^ 2) + Q p)
    (hQ0 : ∀ p, 0 ≤ Q p) (hFmeas : Measurable F)
    (hR : ∀ t, R t = Q (0, t)) (hRmeas : Measurable R)
    (hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U), R z ≠ 0)
    (C : ℝ) (hC : 0 < C)
    (hcmp : ∃ U ∈ 𝓝 ((0 : Fin m → ℝ), t0), ∀ p ∈ U,
        (∑ i, p.1 i ^ 2) + R p.2 ≤ C * F p) :
    (m : ℝ≥0∞) / 2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v := by
  rw [hchart]
  exact rlct_quasiSplit_ge F Q R t0 hF hQ0 hFmeas hR hRmeas hRne C hC hcmp

/-- **PART (a) → D1 per-point `≥`** (the (★) close MODULO the two producer obligations). Wiring
`rlctAt_ge_nReg_add_slice` (the `hAtV` side) through banked `deepest_le_of_optimal_via_L2_ge`: with
the deepest-side equality `hDeepest` (banked via `deepest_regular_core_normal_form`, #44) and the
leading-form comparison `hCore : coreDeepest ≤ rlctAtOn R t0` (PART (b)), the deepest point has
`≤` local RLCT than `v`: `rlctAt (dlnLoss H B) deepest ≤ rlctAt (dlnLoss H B) v`. This is the
`rlctAt_deepest_le_of_optimal` per-point conclusion, reduced to EXACTLY: (i) the IFT-chart producer,
(ii) `hDeepest` (= #44), (iii) `hCore` (the leading-form comparison). The `nReg/2` shift cancels. -/
theorem deepest_le_of_optimal_chart {L m : ℕ} {Y : Type*}
    [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y]
    (H : Fin (L + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
    (deepest v : Params H)
    (F : (Fin m → ℝ) × Y → ℝ) (Q : (Fin m → ℝ) × Y → ℝ) (R : Y → ℝ) (t0 : Y)
    (coreDeepest : ℝ≥0∞)
    (hDeepest : rlctAt H (dlnLoss H B) deepest = (m : ℝ≥0∞) / 2 + coreDeepest)
    (hchart : rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin m → ℝ), t0))
    (hF : ∀ p, F p = (∑ i, p.1 i ^ 2) + Q p)
    (hQ0 : ∀ p, 0 ≤ Q p) (hFmeas : Measurable F)
    (hR : ∀ t, R t = Q (0, t)) (hRmeas : Measurable R)
    (hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U), R z ≠ 0)
    (C : ℝ) (hC : 0 < C)
    (hcmp : ∃ U ∈ 𝓝 ((0 : Fin m → ℝ), t0), ∀ p ∈ U,
        (∑ i, p.1 i ^ 2) + R p.2 ≤ C * F p)
    (hCore : coreDeepest ≤ rlctAtOn R t0) :
    rlctAt H (dlnLoss H B) deepest ≤ rlctAt H (dlnLoss H B) v := by
  have hAtV : (m : ℝ≥0∞) / 2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v :=
    rlctAt_ge_nReg_add_slice H B v F Q R t0 hchart hF hQ0 hFmeas hR hRmeas hRne C hC hcmp
  exact deepest_le_of_optimal_via_L2_ge (B := B) H r (rlctAt H (dlnLoss H B) deepest)
    (rlctAt H (dlnLoss H B) v) m coreDeepest (rlctAtOn R t0) hDeepest hAtV hCore

end DLNFibre.DLN.RLCT
