import DLNFibre.DLN.RLCT.Validate.RouteMNodeDescent

/-!
# `RouteMNodeDescentBuild` — the G-a per-node datum CONSTRUCTOR (fm3 #135 parallel-fill)

The `RouteMNodeDescent` seam (`RouteMNodeDescent.lean`) is the LOCKED interface; this file is fm3's
parallel-fill of the PRODUCER side — the constructor that builds a `RouteMNodeDescent` from the per-node
blow-up data. It consumes the PROVEN `schur_straighten_squeeze_exists` (`GeneralR1Recursion`, the
g131-certified squeeze existence) + a `ReducedTransport S Y` (crux2's banked det-1 MP descent).

The constructor is **defect-class-AGNOSTIC** (pp-rstar #134): C1 (hard-pivot — defect in the `bcol·Erow`
perturbation) and C5 (partial-drop — defect in an `nReg`-regular generator after the shear `δ'`) differ
ONLY in the field values `bcol`/`SΓ`/`Erow` the producer (rs-grind) supplies to the `hnode` presentation.
The constructor takes those as data; the squeeze constants `c₁ = (2(1+T²))⁻¹`, `c₂ = 2+2T²` are produced
by `schur_straighten_squeeze_exists`.

**The G-a design pin (why this composes):** the squeeze's reduced core `G` and reduced-coord embed
`redEmbed` are sourced FROM the transport (`transport.G`, `↑transport.redEmbed`), and the
`hredCore : ∀ y, G y² = dlnLoss S.red 0 (redEmbed y)` obligation of `schur_straighten_squeeze_exists` is
discharged by `transport.hredCore` — so the squeeze datum and the descent transport share the SAME `G` by
construction, and `RouteMNodeDescent.descentStep`'s two legs compose with no coherence side-condition.
-/

open DLNFibre.DLN.RLCT MeasureTheory
open scoped BigOperators ENNReal

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The per-node datum constructor (G-a producer fill).** From a `ReducedTransport S Y` (the det-1 MP
descent), the per-node core `flatCore`, the blow-up Schur-form presentation `hnode` (the `(B)`-lane
contract — `flatCore w = ∑ⱼ w.1ⱼ² + ∑ᵢⱼ (bcol·w.1ⱼ + SΓ)²`, the reduced part `= ∑ᵢⱼ SΓ²`, the pivot column
bounded `∑ bcol² ≤ T²`), and the measurability / germ-nonvanishing / well-foundedness contracts, build a
`RouteMNodeDescent M S nReg Y`.

`G`/`redEmbed` are sourced from `transport`; the `hredCore` obligation of `schur_straighten_squeeze_exists`
is `transport.hredCore`, the `Gne` is the supplied germ, the `Gmeas` is the supplied `hGmeas`. The squeeze
constants come from `schur_straighten_squeeze_exists`. C1/C5 are the same call with different `bcol`/`SΓ`. -/
noncomputable def RouteMNodeDescent.ofNodePresentation
    {M : Fin (L + 1) → ℕ} {S : ChainDimSplit M} {nReg : ℕ}
    {Y : Type} [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y] [OpensMeasurableSpace Y] [Zero Y]
    (transport : ReducedTransport S Y)
    (flatCore : (Fin nReg → ℝ) × Y → ℝ) (T : ℝ)
    {Mblk : Type} [Fintype Mblk]
    (bcol : (Fin nReg → ℝ) × Y → Mblk → ℝ)
    (SΓ : (Fin nReg → ℝ) × Y → Mblk → Fin nReg → ℝ)
    (hFmeas : Measurable flatCore)
    (hGmeas : Measurable transport.G)
    (hGne : ∃ U ∈ nhds (0 : Y), ∀ᵐ z ∂(volume.restrict U), transport.G z ≠ 0)
    (hdrop : ∑ s, S.red s < ∑ s, M s)
    (hnode : ∃ U ∈ nhds ((0, 0) : (Fin nReg → ℝ) × Y), ∀ w ∈ U,
        flatCore w = (∑ j, (w.1 j) ^ 2) + (∑ i, ∑ j, (bcol w i * w.1 j + SΓ w i j) ^ 2)
        ∧ transport.G w.2 ^ 2 = (∑ i, ∑ j, (SΓ w i j) ^ 2)
        ∧ (∑ i, (bcol w i) ^ 2) ≤ T ^ 2) :
    RouteMNodeDescent M S nReg Y :=
  let h := schur_straighten_squeeze_exists M S flatCore transport.G
    (fun y => transport.redEmbed y) T bcol SΓ hFmeas hGmeas
    (fun y => transport.hredCore y) hGne hdrop hnode
  { flatCore := flatCore
    transport := transport
    c₁ := h.choose
    c₂ := h.choose_spec.choose
    isSqueeze := h.choose_spec.choose_spec }

/-- **End-to-end check: the constructed datum descends.** The `descentStep` of a datum built by
`ofNodePresentation` is the per-node descent step at the deepest point — confirming the G-sourcing pin
composes through the constructor (the squeeze's `G` = `transport.G`, so the two legs meet). This is the
producer→consumer round-trip the G-b cover lintegral relies on. -/
example {M : Fin (L + 1) → ℕ} {S : ChainDimSplit M} {nReg : ℕ}
    {Y : Type} [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y] [OpensMeasurableSpace Y] [Zero Y]
    (transport : ReducedTransport S Y)
    (flatCore : (Fin nReg → ℝ) × Y → ℝ) (T : ℝ)
    {Mblk : Type} [Fintype Mblk]
    (bcol : (Fin nReg → ℝ) × Y → Mblk → ℝ)
    (SΓ : (Fin nReg → ℝ) × Y → Mblk → Fin nReg → ℝ)
    (hFmeas : Measurable flatCore) (hGmeas : Measurable transport.G)
    (hGne : ∃ U ∈ nhds (0 : Y), ∀ᵐ z ∂(volume.restrict U), transport.G z ≠ 0)
    (hdrop : ∑ s, S.red s < ∑ s, M s)
    (hnode : ∃ U ∈ nhds ((0, 0) : (Fin nReg → ℝ) × Y), ∀ w ∈ U,
        flatCore w = (∑ j, (w.1 j) ^ 2) + (∑ i, ∑ j, (bcol w i * w.1 j + SΓ w i j) ^ 2)
        ∧ transport.G w.2 ^ 2 = (∑ i, ∑ j, (SΓ w i j) ^ 2)
        ∧ (∑ i, (bcol w i) ^ 2) ≤ T ^ 2) :
    rlctAtOn (RouteMNodeDescent.ofNodePresentation transport flatCore T bcol SΓ
        hFmeas hGmeas hGne hdrop hnode).flatCore (0, 0)
      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) :=
  (RouteMNodeDescent.ofNodePresentation transport flatCore T bcol SΓ
    hFmeas hGmeas hGne hdrop hnode).descentStep

end DLNFibre.DLN.RLCT
