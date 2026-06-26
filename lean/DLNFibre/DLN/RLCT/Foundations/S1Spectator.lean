import DLNFibre.DLN.RLCT.Foundations.Rlct
import Mathlib.MeasureTheory.Integral.Prod

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1Spectator` — the loss-independent spectator-coordinate peel (S1)

A function on a product `X × Y` that depends only on the first factor has the SAME RLCT as the
function on `X` alone: the spectator factor `Y` contributes an RLCT-neutral (positive-finite) box.

    rlctAtOn (fun p : X × Y => F p.1) (x0, y0) = rlctAtOn F x0.

The "spectator" directions are coordinates the loss is FLAT along — e.g. the gauge-orbit directions
of the deepest-point gauge slice (`DeepestGaugeChart.nGauge`; the loss is gauge-invariant), or the
parameter directions a regular block does not touch. Used by L2 (`DeepestGaugeChart`,
`deepest_regular_smooth_split`) and shared with D1 (the homogeneous-residual chart's regular block).

The proof is the two-direction admissibility-set equality (`weightedThreshold` is an `sSup` over
admissible `c'`):
- a box `U ×ˢ V` (open, `V` a unit ball) factors the integral `∫_{U×V} |F(p.1)|^{−c'} = (∫_U
  |F|^{−c'}) · vol(V)` (`integrable_prod_iff`, the integrand is constant in `Y`), so `U` admissible
  for `F` ⟹ `U ×ˢ V` admissible for `F∘fst`, and conversely a box inside any admissible `Ω` factors
  back (`vol(V) > 0`).
-/

open MeasureTheory Set
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

variable {X Y : Type*}
  [MeasureSpace X] [TopologicalSpace X] [MeasureSpace Y] [TopologicalSpace Y]

/-- `Integrable (fun p => g p.1)` on `μ.prod ν` (with `ν` finite-nonzero) iff `Integrable g μ`.
`fun p => g p.1 = g ∘ Prod.fst`; the pushforward `map fst (μ.prod ν) = (ν univ) • μ`
(`map_fst_prod`), and `integrable_smul_measure` strips the positive-finite scalar. -/
private theorem integrable_prod_iff_of_indep
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    [NeZero ν] [IsFiniteMeasure ν] (g : X → ℝ) :
    Integrable (fun p : X × Y => g p.1) (μ.prod ν) ↔ Integrable g μ := by
  have hcne : ν univ ≠ 0 := by
    simpa using (NeZero.ne ν) ∘ (Measure.measure_univ_eq_zero.1)
  have hclt : ν univ ≠ ∞ := measure_ne_top ν univ
  have hkey : Integrable (fun p : X × Y => g p.1) (μ.prod ν)
      ↔ Integrable g (Measure.map Prod.fst (μ.prod ν)) := by
    constructor
    · intro h
      have hslice := h.prod_left_ae
      have hg : Integrable g μ := (Filter.Eventually.exists hslice).choose_spec
      rw [Measure.map_fst_prod]
      exact hg.smul_measure hclt
    · intro h
      have := h.comp_measurable (measurable_fst : Measurable (Prod.fst : X × Y → X))
      exact this
  rw [hkey, Measure.map_fst_prod, integrable_smul_measure hcne hclt]

/-- The product integrand `fun p => |F p.1|^{−c'}·1` is integrable on a box `U ×ˢ V`
(with `0 < vol V < ⊤`) iff `fun x => |F x|^{−c'}·1` is integrable on `U`. The integrand is constant
in the `Y`-factor, so `integrable_prod_iff` reduces to the `X`-integrability times the finite-positive
box `vol V`. -/
private theorem box_integrableOn_iff
    [SFinite (volume : Measure X)] [SFinite (volume : Measure Y)]
    (F : X → ℝ) (c' : ℝ) {U : Set X} {V : Set Y}
    (hVpos : 0 < volume V) (hVlt : volume V < ⊤) :
    IntegrableOn (fun p : X × Y => |F p.1| ^ (-c') * (fun _ => (1 : ℝ)) p) (U ×ˢ V) volume
      ↔ IntegrableOn (fun x => |F x| ^ (-c') * (fun _ => (1 : ℝ)) x) U volume := by
  set f : X → ℝ := fun x => |F x| ^ (-c') * (fun _ => (1 : ℝ)) x with hf
  have hg : (fun p : X × Y => |F p.1| ^ (-c') * (fun _ => (1 : ℝ)) p)
      = fun p : X × Y => f p.1 := by funext p; simp [f]
  rw [hg, IntegrableOn, IntegrableOn, Measure.volume_eq_prod X Y, ← Measure.prod_restrict]
  have hVne : NeZero (volume.restrict V) := by
    refine ⟨fun h => hVpos.ne' ?_⟩
    have := congrArg (fun μ => μ univ) h
    simpa [Measure.restrict_apply_univ] using this
  have hVfin : IsFiniteMeasure (volume.restrict V) := by
    refine ⟨?_⟩; rw [Measure.restrict_apply_univ]; exact hVlt
  exact integrable_prod_iff_of_indep f

/-- **The loss-independent spectator peel (S1).** A function depending only on the first factor of a
product `X × Y` has the same RLCT as on `X` alone: the spectator factor `Y` is RLCT-neutral (a
positive-finite box). Hypotheses: `Y` has an `SFinite` volume and a nonempty open `y0`-nbhd of
positive finite volume (a metric ball; `IsOpenPosMeasure` + locally-finite gives this), `X` is
`SFinite`. -/
theorem rlctAtOn_spectator_peel
    [SFinite (volume : Measure X)] [SFinite (volume : Measure Y)]
    [OpensMeasurableSpace Y] [Measure.IsOpenPosMeasure (volume : Measure Y)]
    (F : X → ℝ) (x0 : X) (y0 : Y)
    (hY : ∃ V : Set Y, IsOpen V ∧ y0 ∈ V ∧ volume V < ⊤) :
    rlctAtOn (fun p : X × Y => F p.1) (x0, y0) = rlctAtOn F x0 := by
  obtain ⟨V, hVopen, hy0V, hVlt⟩ := hY
  have hVpos : 0 < volume V := hVopen.measure_pos volume ⟨y0, hy0V⟩
  unfold rlctAtOn weightedThreshold
  congr 1
  ext c
  constructor
  · -- product-admissible ⟹ `X`-admissible: a box `U' ×ˢ V'` inside `Ω` factors back.
    rintro ⟨c', rfl, Ω, hΩopen, hKΩ, hint⟩
    have hmem : (x0, y0) ∈ Ω := hKΩ rfl
    obtain ⟨U', V', hU'open, hV'open, hxU', hyV', hsub⟩ :=
      isOpen_prod_iff.1 hΩopen x0 y0 hmem
    refine ⟨c', rfl, U', hU'open, Set.singleton_subset_iff.2 hxU', ?_⟩
    -- shrink `V'` to a positive-finite open box `V''` around `y0`.
    set V'' := V' ∩ V with hV''
    have hV''open : IsOpen V'' := hV'open.inter hVopen
    have hyV'' : y0 ∈ V'' := ⟨hyV', hy0V⟩
    have hV''pos : 0 < volume V'' := hV''open.measure_pos volume ⟨y0, hyV''⟩
    have hV''lt : volume V'' < ⊤ := lt_of_le_of_lt (measure_mono inter_subset_right) hVlt
    have hsub'' : U' ×ˢ V'' ⊆ Ω := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩; exact hsub ⟨hx, hy.1⟩
    have hboxint :
        IntegrableOn (fun p : X × Y => |F p.1| ^ (-(c' : ℝ)) * (fun _ => (1 : ℝ)) p)
          (U' ×ˢ V'') volume := hint.mono_set hsub''
    exact (box_integrableOn_iff F (c' : ℝ) hV''pos hV''lt).1 hboxint
  · -- `X`-admissible ⟹ product-admissible: take the box `U ×ˢ V`.
    rintro ⟨c', rfl, U, hUopen, hKU, hint⟩
    refine ⟨c', rfl, U ×ˢ V, hUopen.prod hVopen,
      Set.singleton_subset_iff.2 ⟨hKU rfl, hy0V⟩, ?_⟩
    exact (box_integrableOn_iff F (c' : ℝ) hVpos hVlt).2 hint

end DLNFibre.DLN.RLCT
