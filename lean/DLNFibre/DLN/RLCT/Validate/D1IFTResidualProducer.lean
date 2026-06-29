import DLNFibre.DLN.RLCT.Validate.D1ChartProducerL2Build
import DLNFibre.DLN.RLCT.Foundations.S1IFTProducer

/-!
# `DLNFibre.DLN.RLCT.Validate.D1IFTResidualProducer` — the D1 producer fed by a `C¹` residual

The §SEL selected-minor IFT-chart producer, WIRED. The banked reductions
`deepest_le_of_optimal_chart` (`D1ChartProducer`) and `deepest_le_of_optimal_middle_stratum`
(`D1ChartProducerL2Build`) consume the post-chart sum-of-squares form `F = ∑s² + Q` with the
constant comparison `hcmp` as **bare hypotheses**. This module DISCHARGES those from the
genuinely-lighter premise the §SEL route identified: the residual is a `C¹` sum of squares
`Q = ‖q‖²`. The network-free producer `rlctAtOn_quasiSplit_ge_of_contDiff_residual`
(`Foundations.S1IFTProducer`) builds `hF`, `hQ0`, `hR` (definitional) and `hcmp` (the §SEL
vector-triangle mean-value bound) from `q`'s smoothness, so the only chart fact left hypothesized is
the bounded-unit chart TRANSFER `hchart : rlctAt (dlnLoss H B) v = rlctAtOn F (0,t0)` (the banked
`rlctAtOn_boundedUnit_localHomeomorph` applied to the actual `Params H → flat` IFT chart at `v` —
the Altitude-B DLN-specific wiring, NOT a quadratic-split / Morse-Bott lemma).

## What it lands

  * **`rlctAt_ge_nReg_add_slice_of_residual`** — the `hAtV` half from a `C¹` first-peel residual:
    the chart transfer `hchart` + `q` `C¹` + the slice a.e.-nonzero ⟹
    `nReg/2 + rlctAtOn R t0 ≤ rlctAt (dlnLoss H B) v`, with `F`, `R` built from `q` (no bare
    `hF`/`hQ0`/`hcmp`).
  * **`deepest_le_of_optimal_of_iftResidual`** — the full D1 per-point `≥` at a middle-stratum
    optimal `v`, wired through BOTH peels: the first-peel residual `q` (this module) feeds the
    `hAtV` half, and the second-peel residual `q₂` + the §5 R1-resolution interface feed the
    case-(B) `hCore` (`hCore_middle_stratum_of_interface`). All chart data is CONSTRUCTED from the
    two `C¹` residuals; only `hchart`/`hchart₂` (the two `rlctAtOn`-equality transfers), `hDeepest`
    (#44), and `hDegraded` (the R1 interface) remain hypotheses.

Scope L = 2 (general-L = wall #120). The chart-transfer `hchart` and the deepest `hDeepest` stay the
tracked Skeleton obligations; this module removes the chart-DATA (`hF`/`hQ0`/`hcmp`) from the
hypothesis list, replacing them with the single `C¹`-residual premise the §SEL route certified.
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

/-- **The `hAtV` half from a `C¹` first-peel residual** (the §SEL producer wired). At a general
optimal `v` at L = 2, given the bounded-unit chart transfer `hchart` to the post-chart loss
`F (s,t) = (∑ s²) + ‖q (s,t)‖²` (`q` the `C¹` inactive-residual vector on the flat slice
`(Fin m → ℝ) × Y`), with the slice residual `R t = ‖q (0,t)‖²` a.e.-nonzero near `t0`, the engine
gives the `hAtV` shape:

    (m : ℝ≥0∞)/2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v.

`hF`/`hQ0`/`hR`/`hcmp` are NOT hypotheses here — they are built from `q`'s smoothness by the
network-free `rlctAtOn_quasiSplit_ge_of_contDiff_residual`. -/
theorem rlctAt_ge_nReg_add_slice_of_residual {L m n : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasureSpace Y] [BorelSpace Y]
    [FiniteDimensional ℝ Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)]
    (H : Fin (L + 1) → ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (v : Params H)
    (q : (Fin m → ℝ) × Y → EuclideanSpace ℝ (Fin n)) (hq : ContDiff ℝ 1 q) (t0 : Y)
    (hchart : rlctAt H (dlnLoss H B) v
        = rlctAtOn (fun p : (Fin m → ℝ) × Y => (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2))
            ((0 : Fin m → ℝ), t0))
    (hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U),
        (∑ i, q ((0 : Fin m → ℝ), z) i ^ 2) ≠ 0) :
    (m : ℝ≥0∞) / 2 + rlctAtOn (fun t : Y => ∑ i, q ((0 : Fin m → ℝ), t) i ^ 2) t0
      ≤ rlctAt H (dlnLoss H B) v := by
  rw [hchart]
  exact rlctAtOn_quasiSplit_ge_of_contDiff_residual q hq t0 hRne

/-- **The full D1 per-point `≥` from two `C¹` residuals** (the §SEL producer wired through both
peels). At a middle-stratum optimal `v` (square deepest reduced widths `(m,m,m)`,
`coreDeepest = ofReal(lambdaCore (square m))`, `a + b ≤ m`):

  * the FIRST-peel `C¹` residual `q` (on `(Fin nReg → ℝ) × Y`) + the chart transfer `hchart` give
    the `nReg`-block `hAtV` half (`rlctAt_ge_nReg_add_slice_of_residual` content, inlined via the
    engine);
  * the SECOND-peel `C¹` residual `q₂` (on `(Fin extra → ℝ) × Y₂`) + its chart transfer `hchart₂` +
    the §5 R1-resolution interface `hDegraded` discharge the case-(B) `hCore` via
    `hCore_middle_stratum_of_interface`;

and the deepest-side `#44` equality `hDeepest` closes `rlctAt deepest ≤ rlctAt v`. ALL chart DATA
(`hF`/`hQ0`/`hR`/`hcmp` for both peels) is CONSTRUCTED from `q`, `q₂` smoothness; only the two
`rlctAtOn`-equality transfers, `hDeepest`, and the R1 interface stay hypotheses.
`nReg = nRegL2 H r`, `extra = extraCount m a b`. -/
theorem deepest_le_of_optimal_of_iftResidual {n n₂ : ℕ}
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasureSpace Y] [BorelSpace Y]
    [FiniteDimensional ℝ Y] [ProperSpace Y] [IsFiniteMeasureOnCompacts (volume : Measure Y)]
    {Y₂ : Type*} [NormedAddCommGroup Y₂] [NormedSpace ℝ Y₂] [MeasureSpace Y₂] [BorelSpace Y₂]
    [FiniteDimensional ℝ Y₂] [ProperSpace Y₂] [IsFiniteMeasureOnCompacts (volume : Measure Y₂)]
    (H : Fin (2 + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ)
    (deepest v : Params H) (m a b : ℕ) (hab : a + b ≤ m) (coreDeepest : ℝ≥0∞)
    (hcoreDeepest : coreDeepest = ENNReal.ofReal (lambdaCore (squareWidths m) : ℝ))
    (hDeepest : rlctAt H (dlnLoss H B) deepest = (nRegL2 H r : ℝ≥0∞) / 2 + coreDeepest)
    -- FIRST-peel `C¹` residual + chart transfer
    (q : (Fin (nRegL2 H r) → ℝ) × Y → EuclideanSpace ℝ (Fin n)) (hq : ContDiff ℝ 1 q) (t0 : Y)
    (hchart : rlctAt H (dlnLoss H B) v
        = rlctAtOn (fun p : (Fin (nRegL2 H r) → ℝ) × Y => (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2))
            ((0 : Fin (nRegL2 H r) → ℝ), t0))
    (hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U),
        (∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), z) i ^ 2) ≠ 0)
    -- SECOND-peel `C¹` residual + chart transfer + the §5 interface
    (q₂ : (Fin (extraCount m a b) → ℝ) × Y₂ → EuclideanSpace ℝ (Fin n₂)) (hq₂ : ContDiff ℝ 1 q₂)
    (t0₂ : Y₂)
    (hchart₂ : rlctAtOn (fun t : Y => ∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2) t0
        = rlctAtOn (fun p : (Fin (extraCount m a b) → ℝ) × Y₂ =>
            (∑ i, p.1 i ^ 2) + (∑ i, q₂ p i ^ 2))
            ((0 : Fin (extraCount m a b) → ℝ), t0₂))
    (hR₂ne : ∃ U ∈ 𝓝 t0₂, ∀ᵐ z ∂(volume.restrict U),
        (∑ i, q₂ ((0 : Fin (extraCount m a b) → ℝ), z) i ^ 2) ≠ 0)
    (hDegraded : rlctAtOn (fun t : Y₂ => ∑ i, q₂ ((0 : Fin (extraCount m a b) → ℝ), t) i ^ 2) t0₂
        = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ)) :
    rlctAt H (dlnLoss H B) deepest ≤ rlctAt H (dlnLoss H B) v := by
  -- the FIRST-peel post-chart loss / slice residual (built from `q`)
  set F : (Fin (nRegL2 H r) → ℝ) × Y → ℝ :=
    fun p => (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2) with hFdef
  set Q : (Fin (nRegL2 H r) → ℝ) × Y → ℝ := fun p => ∑ i, q p i ^ 2 with hQdef
  set R : Y → ℝ := fun t => ∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2 with hRdef
  -- the SECOND-peel post-chart loss / slice residual (built from `q₂`)
  set F₂ : (Fin (extraCount m a b) → ℝ) × Y₂ → ℝ :=
    fun p => (∑ i, p.1 i ^ 2) + (∑ i, q₂ p i ^ 2) with hF₂def
  set Q₂ : (Fin (extraCount m a b) → ℝ) × Y₂ → ℝ := fun p => ∑ i, q₂ p i ^ 2 with hQ₂def
  set R₂ : Y₂ → ℝ := fun t => ∑ i, q₂ ((0 : Fin (extraCount m a b) → ℝ), t) i ^ 2 with hR₂def
  -- measurability of `F`, `R` (continuity of the sum-of-squares of `C¹` coords)
  have hqcont : Continuous q := hq.continuous
  have hqi : ∀ i, Continuous fun p : (Fin (nRegL2 H r) → ℝ) × Y => q p i := fun i =>
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous).comp hqcont
  have hFmeas : Measurable F := by
    have hcont : Continuous F := by
      refine Continuous.add (continuous_finset_sum _
        (fun i _ => ((continuous_apply i).comp continuous_fst).pow 2))
        (continuous_finset_sum _ (fun i _ => (hqi i).pow 2))
    exact hcont.measurable
  have hRmeas : Measurable R := by
    have hcont : Continuous R := continuous_finset_sum _ (fun i _ =>
      ((hqi i).comp (Continuous.prodMk continuous_const continuous_id)).pow 2)
    exact hcont.measurable
  -- the FIRST-peel `hcmp` (the §SEL vector triangle from `q`'s smoothness)
  obtain ⟨C, hC, hcmp⟩ := hcmp_of_contDiff q hq t0
  -- the SECOND-peel measurability + `hcmp`
  have hq₂cont : Continuous q₂ := hq₂.continuous
  have hq₂i : ∀ i, Continuous fun p : (Fin (extraCount m a b) → ℝ) × Y₂ => q₂ p i := fun i =>
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous).comp hq₂cont
  have hF₂meas : Measurable F₂ := by
    have hcont : Continuous F₂ := by
      refine Continuous.add (continuous_finset_sum _
        (fun i _ => ((continuous_apply i).comp continuous_fst).pow 2))
        (continuous_finset_sum _ (fun i _ => (hq₂i i).pow 2))
    exact hcont.measurable
  have hR₂meas : Measurable R₂ := by
    have hcont : Continuous R₂ := continuous_finset_sum _ (fun i _ =>
      ((hq₂i i).comp (Continuous.prodMk continuous_const continuous_id)).pow 2)
    exact hcont.measurable
  obtain ⟨C₂, hC₂, hcmp₂⟩ := hcmp_of_contDiff q₂ hq₂ t0₂
  -- assemble through the banked two-peel reduction
  exact deepest_le_of_optimal_middle_stratum H r B deepest v m a b hab coreDeepest hcoreDeepest
    F Q R t0 hDeepest hchart (fun _ => rfl)
    (fun p => Finset.sum_nonneg fun i _ => sq_nonneg _) hFmeas (fun _ => rfl) hRmeas hRne C hC hcmp
    F₂ Q₂ R₂ t0₂ hchart₂ (fun _ => rfl)
    (fun p => Finset.sum_nonneg fun i _ => sq_nonneg _) hF₂meas (fun _ => rfl) hR₂meas hR₂ne
    C₂ hC₂ hcmp₂ hDegraded

end DLNFibre.DLN.RLCT
