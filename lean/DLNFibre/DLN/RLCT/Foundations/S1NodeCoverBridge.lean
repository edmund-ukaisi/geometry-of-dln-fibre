import DLNFibre.DLN.RLCT.Foundations.S1NodeCoverGE

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1NodeCoverBridge` — the box→point bridge interface (R1 item 2b)

The per-node cover's interface (g156 adjudication, 2026-06-23): the obligation the cover and the binding
spine consume is genuinely **box-threaded** — full-ratio-box integrability of the loss density,
descending to the child's box — NOT a point-RLCT. The clean point-min `rlctAtOn (dlnLoss M 0) 0 =
min{mk/2, rlctAtOn core 0}` is a true VALUE identity (the NUMBER matches the point threshold), but the
PROOF obligation per node is `|K|^{−c'}` integrable over the full box `Vz` (`chart_pullback_lt_top_of_boxpm`'s
`hKint`), which `rlctAtOn K 0` (the point) does NOT supply — the divisor-vs-point gap (the (2,2,2)
`resolved_residual_lt_top` `recStep` precedent).

So `BoxThresholdBridge K` below is a **box statement** (full `Vz` integrability) PARAMETRISED by the point
threshold `rlctAtOn K 0`: the antecedent is the point number, the consequent is the full-box obligation.
It is the box-threaded interface, and it descends one dimension to the child's box. The bridge FACT (that
the box obligation holds, given the point number) is proved separately (deriv-finish lane: the all-zero
deepest point is the GLOBAL-MIN-RLCT point — maximal rank-drop ⇒ every partial-vanishing stratum is
*less* singular — so the point threshold governs every bounded box). Here we (1) STATE it as the precise
interface predicate the GE producer consumes, and (2) show it discharges
`chart_pullback_lt_top_of_boxpm`'s `hKint`.

## The bridge predicate (the side-fact the GE producer consumes)
`BoxThresholdBridge K`: for every bounded measurable box `Vz` and every `c' < rlctAtOn K 0`, the
density `|K|^{−c'}` is integrable on `Vz`. This is exactly the "deepest = global-min-rlct point ⇒
the point threshold governs every bounded box" fact. Stated generically over `K : Z → ℝ` so the GE
producer can instantiate it at `K = core` (and the recursion descends it to the child).

Axiom-free target (only `propext`/`Classical.choice`/`Quot.sound`).
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

variable {Z : Type*} [PseudoMetricSpace Z] [MeasureSpace Z] [Zero Z]
    [SFinite (volume : Measure Z)] [BorelSpace Z] [SecondCountableTopology Z]

/-- **The box→point bridge predicate (the GE producer's side-input).** `K`'s sub-threshold density is
integrable on EVERY bounded box: for bounded measurable `Vz` and `c' < rlctAtOn K 0`, `|K|^{−c'}` is
integrable on `Vz`. The content (proved in the deriv-finish lane for `K = dlnLoss N 0`): the deepest
point `0` is the global-min-RLCT point, so the point threshold `rlctAtOn K 0` governs the whole box —
collapsing the cover's full-box integrability requirement to the point-min value. -/
def BoxThresholdBridge (K : Z → ℝ) : Prop :=
  ∀ (c' : NNReal), (c' : ℝ≥0∞) < rlctAtOn K 0 →
    ∀ (Vz : Set Z), MeasurableSet Vz → Bornology.IsBounded Vz →
      IntegrableOn (fun z => |K z| ^ (-(c' : ℝ))) Vz volume

/-- **The bridge discharges the per-chart `hKint`.** Given `BoxThresholdBridge K` and `c' < rlctAtOn
K 0` (with `c' < mk/2`, `e = mk−1`), the per-chart pulled-back threshold integrand is finite on the
chart rectangle `Iy ×ˢ Vz` — the box-threaded `chart_pullback_lt_top_of_boxpm`, with its `hKint`
hypothesis now SUPPLIED by the bridge (collapsing box-integrability to the point threshold). The GE
producer's per-chart obligation, freed of the standalone full-box integrability ask. -/
theorem chart_pullback_lt_top_of_bridge
    (e : ℕ) (c' : NNReal) (hc'lt : (c' : ℝ) < ((e : ℝ) + 1) / 2)
    (K : Z → ℝ) (hKm : Measurable K) (hbridge : BoxThresholdBridge K)
    (hc'core : (c' : ℝ≥0∞) < rlctAtOn K 0)
    (Iy : Set ℝ) (hIy : MeasurableSet Iy) (hIybdd : Bornology.IsBounded Iy)
    (Vz : Set Z) (hVz : MeasurableSet Vz) (hVzbdd : Bornology.IsBounded Vz) :
    ∫⁻ p in Iy ×ˢ Vz,
        ENNReal.ofReal (|p.1| ^ e * |p.1 ^ 2 * K p.2| ^ (-(c' : ℝ))) < ⊤ :=
  chart_pullback_lt_top_of_boxpm e (c' : ℝ) (c'.coe_nonneg) hc'lt K hKm Iy hIy hIybdd Vz
    (hbridge c' hc'core Vz hVz hVzbdd)

end DLNFibre.DLN.RLCT
