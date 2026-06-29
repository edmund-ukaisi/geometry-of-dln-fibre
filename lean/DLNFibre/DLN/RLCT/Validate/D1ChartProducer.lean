import DLNFibre.DLN.RLCT.Foundations.S1QuasiSplit
import DLNFibre.DLN.RLCT.Foundations.S1Spectator
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
Setting `coreV := rlctAtOn R t0` (NOT a separate `v−core` map) makes `hAtV` the engine output; the
SOLE remaining obligation is `hCore : coreDeepest ≤ rlctAtOn R t0`, i.e. `rlctAtOn R 0 ≥
rlctAtOn (core) 0`. G1 verify-first (exact algebra, L=2, r∈{1,2,3}, M ranging over the small
reduced widths + Codex xhigh) found `R = ‖T₁·(I_{M₁}+G)·T₂‖²_F` (`G` gauge-only, `G(0)=0`,
min-degree 2), so `R = (core ∘ fst) ∘ Φ` for the LOCAL DIFFEO `Φ : (T,g) ↦ ((T₁,(I+G(g))·T₂),g)`
fixing the origin (`det DΦ(0) = (det(I+G(0)))^{M₂} = 1`, bounded-unit). `hCore` is DISCHARGED WITH
EQUALITY and is **NOT** the R1-resolution leading-form lemma first feared: the r≥2 coupling `Z₁·Y₂`
is ABSORBED into the invertible inner factor `I+G` (multiplicative reparametrization, NOT additive
Newton-lowering perturbation), so it routes through the SAME banked machinery #44 uses
(`rlctAtOn_boundedUnit_localHomeomorph` + `rlctAtOn_spectator_peel`), DECOUPLED from R1. This is
`hCore_slice_residual_eq` below, banked CONDITIONAL on the producer's diffeo data.

Scope L = 2 (general-L = the named wall #120). This file does NOT close (★): it BANKS the mechanical
PART (a) reduction + PART (b) `hCore`-interface, leaving the single remaining D1 obligation: the
IFT-chart producer (obligation (i), `deepest_gauge_construction` at a general `v`; #44 is the
already-tracked Skeleton sorry the deepest side `hDeepest` consumes). -/

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

/-! ## PART (b) interface — the slice-residual ↦ core RLCT identification (`hCore` discharge)

The G1 verify-first (decorrelated pen-and-paper, EXACT algebra, L=2, r∈{1,2,3}, reduced widths
M∈{(1,1,1),(2,2,2),(1,2,1),(2,1,2),(3,3,3)} + Codex xhigh) found the slice residual to be EXACTLY

    R = ‖ T₁·(I_{M₁} + G)·T₂ ‖²_F,   G = gauge-only, G(0) = 0, min-degree 2,

so `R = (core ∘ fst) ∘ Φ` for the LOCAL DIFFEO `Φ : (T, g) ↦ ((T₁, (I+G(g))·T₂), g)` fixing the
origin (block-triangular Jacobian, `det DΦ(0) = (det(I+G(0)))^{M₂} = 1` ⟹ bounded-unit), with `core`
loss `dlnLoss M 0` (a function of `T` alone, NOT the gauge `g`). The same-weight transverse coupling
`Z₁·Y₂` flagged at r≥2 is ABSORBED into the invertible inner factor `I+G` — NOT an additive
germ-changing perturbation — so the identification is `r`-independent and TIGHT (`rlctAtOn R 0 =
coreDeepest`, equality). The bound is NOT the R1-resolution-coupled leading-form lemma first feared;
it is this local-diffeo + spectator reduction, routing through the SAME banked machinery #44 uses.

The interface below banks `hCore` CONDITIONAL on the producer's diffeo data (the EXACT shape the
producer at obligation (i) supplies). It decouples `hCore` from the R1 / interior-det timeline. -/

/-- **`hCore` via the slice-residual diffeo** (the PART (b) interface, conditional clean-three). The
slice residual `R` on `Reduced × Gauge` equals the reduced core `core₀` (a function of
the `Reduced` factor alone) pulled back along a bounded-unit local diffeo `Φ` fixing the basepoint
`(t0, g0)`, i.e. `R = (core₀ ∘ fst) ∘ Φ` (`hRform`). Then `rlctAtOn R (t0,g0) = rlctAtOn core₀ t0`:
the diffeo transfer (`rlctAtOn_boundedUnit_localHomeomorph`) strips `Φ`, the spectator peel
(`rlctAtOn_spectator_peel`) drops the gauge factor. In particular `coreDeepest = rlctAtOn core₀ t0`
discharges the D1 `hCore : coreDeepest ≤ rlctAtOn R (t0,g0)` with EQUALITY (the G1 tightness).

The hypotheses are EXACTLY the producer's outputs: the diffeo `Φ`/`Φsymm`/derivatives + bounded-unit
Jacobian on an open `V ∋ (t0,g0)` (the raw-data `rlctAtOn_boundedUnit_localHomeomorph` form —
the `Φ` of G1), the form identity `hRform`, and a positive-finite gauge
nbhd `hG` (the spectator box). `core₀` is the reduced loss `dlnLoss M 0` at the producer. -/
theorem hCore_slice_residual_eq
    {Reduced Gauge : Type*}
    [NormedAddCommGroup Reduced] [NormedSpace ℝ Reduced] [MeasureSpace Reduced]
    [BorelSpace Reduced] [FiniteDimensional ℝ Reduced]
    [NormedAddCommGroup Gauge] [NormedSpace ℝ Gauge] [MeasureSpace Gauge]
    [BorelSpace Gauge] [FiniteDimensional ℝ Gauge]
    [(volume : Measure (Reduced × Gauge)).IsAddHaarMeasure]
    [SFinite (volume : Measure Reduced)] [SFinite (volume : Measure Gauge)]
    [Measure.IsOpenPosMeasure (volume : Measure Gauge)]
    (core₀ : Reduced → ℝ) (R : Reduced × Gauge → ℝ) (t0 : Reduced) (g0 : Gauge)
    (Φ Φsymm : Reduced × Gauge → Reduced × Gauge)
    (DΦ DΦsymm : Reduced × Gauge → ((Reduced × Gauge) →L[ℝ] (Reduced × Gauge)))
    (V : Set (Reduced × Gauge))
    (hVopen : IsOpen V) (hwV : (t0, g0) ∈ V)
    (hfix : Φ (t0, g0) = (t0, g0))
    (hleft : ∀ w ∈ V, Φsymm (Φ w) = w) (hright : ∀ w ∈ V, Φ (Φsymm w) = w)
    (hΦcont : ContinuousOn Φ V) (hsymmcont : ContinuousOn Φsymm V)
    (hderiv : ∀ w ∈ V, HasFDerivAt Φ (DΦ w) w)
    (hderivsymm : ∀ w ∈ V, HasFDerivAt Φsymm (DΦsymm w) w)
    (hdetmeas : Measurable fun w => |(DΦ w).det|)
    (hdetmeassymm : Measurable fun w => |(DΦsymm w).det|)
    (hbdd : ∃ a b : ℝ, 0 < a ∧ ∀ w ∈ V, a ≤ |(DΦ w).det| ∧ |(DΦ w).det| ≤ b)
    (hbddsymm : ∃ a b : ℝ, 0 < a ∧ ∀ w ∈ V, a ≤ |(DΦsymm w).det| ∧ |(DΦsymm w).det| ≤ b)
    (hRform : ∀ w, R w = core₀ (Φ w).1)
    (hG : ∃ W : Set Gauge, IsOpen W ∧ g0 ∈ W ∧ volume W < ⊤) :
    rlctAtOn R (t0, g0) = rlctAtOn core₀ t0 := by
  -- `R = (core₀ ∘ fst) ∘ Φ`; strip `Φ` (bounded-unit local diffeo), then peel the gauge spectator.
  have hRfun : R = fun w => (fun p : Reduced × Gauge => core₀ p.1) (Φ w) := by
    funext w; rw [hRform]
  rw [hRfun]
  rw [rlctAtOn_boundedUnit_localHomeomorph (fun p : Reduced × Gauge => core₀ p.1) (t0, g0)
      Φ Φsymm DΦ DΦsymm V hVopen hwV hfix hleft hright hΦcont hsymmcont hderiv hderivsymm
      hdetmeas hdetmeassymm hbdd hbddsymm]
  exact rlctAtOn_spectator_peel core₀ t0 g0 hG

end DLNFibre.DLN.RLCT
