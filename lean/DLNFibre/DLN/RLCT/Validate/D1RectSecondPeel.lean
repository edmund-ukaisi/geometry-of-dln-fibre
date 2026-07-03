import DLNFibre.DLN.RLCT.Validate.D1RectValueArith
import DLNFibre.DLN.RLCT.Validate.D1SecondPeelChart
import DLNFibre.DLN.RLCT.Validate.D1SecondPeelMinor

/-!
# `DLNFibre.DLN.RLCT.Validate.D1RectSecondPeel` — the RECTANGULAR second-peel `hCore` producer

The banked `hCore_middle_stratum_of_interface` (`D1ChartProducerL2Build`) discharges the case-(B)
`hCore` `coreDeepest ≤ rlctAtOn R t0` at a middle-stratum optimal `v`, but SQUARE-only (`coreDeepest =
ofReal(lambdaCore (square m))`, `extra = extraCount m a b`, `M' = MprimeWidths m a b`). This module
supplies the RECTANGULAR analog — the value-side of the `hDom` producer at a general `H` — using the
CROSS-paired rectangular arithmetic (`D1RectValueArith`, decorrelated-certified) and the banked
second-peel chart (`secondPeel_hchart_residual`).

## What it lands

`hCoreRect_of_slice_data`: from the first-peel slice residual `h := q (0,·)` being `C²` and vanishing
at `t0` (BOTH supplied by `dln_hchart_residual_c2`), a second-peel Jacobian RANK bound
`extraCountRect M0 M2 a b ≤ rank(jacResid h t0)` (the geometric middle-stratum fact — a NAMED hypothesis
`hrank₂` here, the tracked chart-unwind), and the R1-resolution interface at the rectangular degraded
core `M' = MprimeRect M a b` (`hDegraded`, a NAMED hypothesis — the R₂-to-`M'`-core identification, the
tracked R1 gate), the case-(B) `hCore` holds:

    ofReal(lambdaCore M) ≤ rlctAtOn (fun t => ∑ i, h t i ^ 2) t0.

The second peel is BUILT (`exists_secondPeel_minor` from `hrank₂`, then `secondPeel_hchart_residual`);
the value close is `coreRect_le_extraRect_half_add_lambdaCore_Mprime`. `hrank₂` (the excess is the
CROSS-paired `a·M2 + b·M0 − ab`, the Jacobian-rank of `mult`'s differential at ranks `(r+a, r+b)`,
decorrelated-certified) and `hDegraded` are the two NAMED-OPEN geometric gates — NOT laundered: they
are the genuine per-`v` middle-stratum content the chart-unwind + R1 supply.

Scope L = 2 (`M : Fin 3 → ℕ`, the deepest reduced widths `M = H − r`). Network-free above the DLN
first-peel residual: the slice residual `h` enters as an abstract `C²` vector.
-/

open Matrix Module MeasureTheory Set Filter
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

/-- **The rectangular case-(B) `hCore`, from the slice-residual data.** For the deepest reduced widths
`M : Fin 3 → ℕ` with honest middle-stratum data `a ≤ M0`, `a + b ≤ M1`, `b ≤ M2`: given the first-peel
slice residual `h : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n)` `C²` (`hh`) vanishing at `t0` (`hh0`), the
second-peel Jacobian RANK bound `hrank₂ : extraCountRect M0 M2 a b ≤ (jacResid h t0).rank`, and the R1
interface at `M' = MprimeRect M a b` — stated on the BUILT second-peel residual `q₂` (`hInterface`) —
the deepest core value dominates the slice residual's local RLCT:

    ofReal(lambdaCore M) ≤ rlctAtOn (fun t => ∑ i, h t i ^ 2) t0.

The second peel is CONSTRUCTED from `hrank₂` (via `exists_secondPeel_minor` +
`secondPeel_hchart_residual`); the value close is the rectangular arithmetic. `extra = extraCountRect
M0 M2 a b` (cross-paired). -/
theorem hCoreRect_of_slice_data {N n : ℕ}
    (M : Fin 3 → ℕ) (a b : ℕ) (ha : a ≤ M 0) (hab : a + b ≤ M 1) (hb : b ≤ M 2)
    (h : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n)) (t0 : Fin N → ℝ)
    (hh : ContDiff ℝ 2 h) (hh0 : h t0 = 0)
    (hrank₂ : extraCountRect (M 0) (M 2) a b ≤ (jacResid h t0).rank)
    (hInterface : ∀ (q₂ : (Fin (extraCountRect (M 0) (M 2) a b) → ℝ)
            × (Fin (N - extraCountRect (M 0) (M 2) a b) → ℝ) → EuclideanSpace ℝ (Fin n))
          (t0₂ : Fin (N - extraCountRect (M 0) (M 2) a b) → ℝ),
        (rlctAtOn (fun t : Fin N → ℝ => ∑ i, h t i ^ 2) t0
            = rlctAtOn (fun p : (Fin (extraCountRect (M 0) (M 2) a b) → ℝ)
                  × (Fin (N - extraCountRect (M 0) (M 2) a b) → ℝ) =>
                (∑ i, p.1 i ^ 2) + (∑ i, q₂ p i ^ 2))
                ((0 : Fin (extraCountRect (M 0) (M 2) a b) → ℝ), t0₂)) →
        (∃ U ∈ 𝓝 t0₂, ∀ᵐ z ∂(volume.restrict U),
            (∑ i, q₂ ((0 : Fin (extraCountRect (M 0) (M 2) a b) → ℝ), z) i ^ 2) ≠ 0)
          ∧ rlctAtOn (fun t : Fin (N - extraCountRect (M 0) (M 2) a b) → ℝ =>
              ∑ i, q₂ ((0 : Fin (extraCountRect (M 0) (M 2) a b) → ℝ), t) i ^ 2) t0₂
            = ENNReal.ofReal (lambdaCore (MprimeRect M a b) : ℝ)) :
    ENNReal.ofReal (lambdaCore M : ℝ)
      ≤ rlctAtOn (fun t : Fin N → ℝ => ∑ i, h t i ^ 2) t0 := by
  -- BUILD the second-peel selected minor from the rank bound.
  obtain ⟨eh, ec, heh, hec, hminor₂⟩ := exists_secondPeel_minor h t0 hrank₂
  -- BUILD the second-peel chart `hchart₂` + the `C¹` residual `q₂`.
  obtain ⟨q₂, t0₂, hq₂CD, hchart₂⟩ :=
    secondPeel_hchart_residual h t0 hh hh0 eh ec heh hec hminor₂
  -- the R1 interface, at the built residual, supplies `hR₂ne` + `hDegraded`.
  obtain ⟨hR₂ne, hDeg⟩ := hInterface q₂ t0₂ hchart₂
  -- the SECOND quasi-split engine pass on `R` (peel the `extra` cross-paired Morse squares).
  set R : (Fin N → ℝ) → ℝ := fun t => ∑ i, h t i ^ 2 with hRdef
  set F₂ : (Fin (extraCountRect (M 0) (M 2) a b) → ℝ)
      × (Fin (N - extraCountRect (M 0) (M 2) a b) → ℝ) → ℝ :=
    fun p => (∑ i, p.1 i ^ 2) + (∑ i, q₂ p i ^ 2) with hF₂def
  set Q₂ : (Fin (extraCountRect (M 0) (M 2) a b) → ℝ)
      × (Fin (N - extraCountRect (M 0) (M 2) a b) → ℝ) → ℝ := fun p => ∑ i, q₂ p i ^ 2 with hQ₂def
  set R₂ : (Fin (N - extraCountRect (M 0) (M 2) a b) → ℝ) → ℝ :=
    fun t => ∑ i, q₂ ((0 : Fin (extraCountRect (M 0) (M 2) a b) → ℝ), t) i ^ 2 with hR₂def
  -- measurability from `q₂`'s continuity.
  have hq₂cont : Continuous q₂ := hq₂CD.continuous
  have hq₂i : ∀ i, Continuous fun p => q₂ p i := fun i =>
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
  -- the second-peel `hcmp₂` (the §SEL vector triangle from `q₂`'s smoothness).
  obtain ⟨C, hC, hcmp₂⟩ := hcmp_of_contDiff q₂ hq₂CD t0₂
  have hpeel : (extraCountRect (M 0) (M 2) a b : ℝ≥0∞) / 2 + rlctAtOn R₂ t0₂
      ≤ rlctAtOn F₂ ((0 : Fin (extraCountRect (M 0) (M 2) a b) → ℝ), t0₂) :=
    rlct_quasiSplit_ge F₂ Q₂ R₂ t0₂ (fun _ => rfl)
      (fun p => Finset.sum_nonneg fun i _ => sq_nonneg _) hF₂meas (fun _ => rfl) hR₂meas hR₂ne C hC
      hcmp₂
  -- close: chart transfer ▸ interface value ▸ rectangular arithmetic.
  rw [hchart₂]
  refine le_trans ?_ hpeel
  rw [hDeg]
  exact coreRect_le_extraRect_half_add_lambdaCore_Mprime M a b ha hab hb

end DLNFibre.DLN.RLCT
