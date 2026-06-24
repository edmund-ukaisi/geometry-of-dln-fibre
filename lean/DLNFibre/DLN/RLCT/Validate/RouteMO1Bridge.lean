import DLNFibre.DLN.RLCT.Validate.RouteMNodeDescentBuild
import DLNFibre.DLN.RLCT.Foundations.LossContinuity

/-!
# `RouteMO1Bridge` — the MP-chart squeeze descent (fm3 #148; SCOPE-LIMITED, see caveat)

`rlctAtOn (dlnLoss M 0) (chart (0,0)) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0` from a measure-preserving
chart `χ : ((Fin nReg → ℝ) × Y) ≃ₜ Params M` + the SQUEEZE of `dlnLoss M 0 ∘ χ` by `smoothBlockSplitForm G`.
Composes `dlnLoss_chart_squeeze_descent` (chart transport via `rlctAtOn_comp_homeomorph` + the chart-free
`schur_recursion_step_squeeze`) with `ReducedTransport.descent`.

**SOUNDNESS CAVEAT (fm3 + Codex xhigh, 2026-06-23 — name≠content correction).** These lemmas are valid for
their stated hypotheses, but the hypotheses are NOT a sound per-node `hstep` at a real BLOW-UP node:
- The MP chart `χ` exists (a `paramsEquivFlat`-style det-1 coordinate reindex). BUT
- the SQUEEZE `c₁·Φ ≤ dlnLoss M 0 ∘ χ ≤ c₂·Φ` is UNSATISFIABLE from the raw loss via an MP reindex: the
  hard-pivot Schur normal form (the squeezable `smoothBlockSplitForm`) only appears AFTER the blow-up
  `A = y₀·Â`; the raw `‖A·B‖²` at the zero-core origin has a rank-0 Jacobian and is NOT locally squeezable.
- The blow-up's Jacobian (e.g. `y₀³` at `(2,2,2)`) SHIFTS the RLCT threshold (exceptional divisor
  `(3+1)/(2·1)=2`, not `1/2`); the MP-chart route does NOT carry it (it would only survive when the divisor
  is non-binding, e.g. `(2,2,2)` accidentally giving `3/2`). So this is NOT a sound descent principle for
  blow-up nodes.

**Therefore:** these lemmas are sound ONLY when `χ` is a genuine MP/unit-Jacobian phase, or when the
argument is ALREADY a post-blow-up `flatCore` in blown-up coordinates (where `descentStep` /
`RouteMNodeDescent`, which take `flatCore` = "the post-blow-up per-node core", are the correct, sound tools).
The per-node `hstep` for `binding_recursion_of_step` at the `dlnLoss` level requires the WEIGHTED-COVER
route (`weightedThreshold F 1 = weightedThreshold (F ∘ π) |Jac π|`, the blow-up Jacobian explicit in the
integrand — the existing `(2,2,2)` cover machinery / `#104`), NOT this MP-chart bridge. Kept as the sound
MP-phase / post-blow-up lemma + the dead-route record; do NOT wire as the blow-up-node `hstep`.
-/

open scoped ENNReal
open MeasureTheory

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The chart-level SQUEEZE descent (the O1 transport core).** Given a measure-preserving chart
`χ : ((Fin nReg → ℝ) × Y) ≃ₜ Params M`, a measurable germ-nonvanishing `G`, positive squeeze constants
`c₁ c₂`, and the SQUEEZE of `dlnLoss M 0 ∘ χ` by `smoothBlockSplitForm G` near `(0,0)`, the local RLCT at
the chart image `χ (0,0)` splits: `rlctAtOn (dlnLoss M 0) (χ (0,0)) = nReg/2 + rlctAtOn (G²) 0`. Composes
`rlctAtOn_comp_homeomorph` (transport `dlnLoss` to the chart source) with `schur_recursion_step_squeeze`
(the chart-free squeeze on `dlnLoss M 0 ∘ χ`). The deepest-point anchor is `χ (0,0)`. -/
theorem dlnLoss_chart_squeeze_descent {M : Fin (L + 1) → ℕ} {nReg : ℕ}
    {Y : Type*} [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y] [OpensMeasurableSpace Y] [Zero Y]
    (chart : ((Fin nReg → ℝ) × Y) ≃ₜ Params M)
    (hmp : MeasurePreserving chart volume volume) (hemb : MeasurableEmbedding chart)
    (G : Y → ℝ) (hGmeas : Measurable G)
    (hGne : ∃ U ∈ nhds (0 : Y), ∀ᵐ z ∂(volume.restrict U), G z ≠ 0)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hsq : ∃ U ∈ nhds ((0, 0) : (Fin nReg → ℝ) × Y), ∀ w ∈ U,
        0 ≤ smoothBlockSplitForm G w
          ∧ c₁ * smoothBlockSplitForm G w ≤ (dlnLoss M 0) (chart w)
          ∧ (dlnLoss M 0) (chart w) ≤ c₂ * smoothBlockSplitForm G w) :
    rlctAtOn (dlnLoss M 0) (chart (0, 0))
      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (fun y => G y ^ 2) (0 : Y) := by
  -- transport `dlnLoss M 0` to the chart source: `rlctAtOn (dlnLoss M 0) (χ (0,0)) = rlctAtOn (dlnLoss ∘ χ) (0,0)`.
  rw [← rlctAtOn_comp_homeomorph chart hmp hemb (dlnLoss M 0) (0, 0)]
  -- the composed core `flatCore := dlnLoss M 0 ∘ χ` is squeezed by `smoothBlockSplitForm G`; apply the step.
  exact schur_recursion_step_squeeze (fun w => dlnLoss M 0 (chart w))
    ((measurable_dlnLoss M 0).comp hemb.measurable) G hGmeas hGne
    c₁ c₂ hc₁ hc₂ hsq

/-- **The per-node O1 step (the `hstep` the binding recursion consumes), as a composition lemma.** From a
`ReducedTransport S Y` (the det-1 MP descent, whose `G` is the squeeze's reduced core — the G-sourcing pin)
+ the chart/squeeze data of `dlnLoss_chart_squeeze_descent`, the local RLCT of the network loss at the
deepest point splits AND descends to the reduced chain:
`rlctAtOn (dlnLoss M 0) (χ (0,0)) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0`. Composes
`dlnLoss_chart_squeeze_descent` (chart + squeeze → `nReg/2 + rlctAtOn (G²) 0`, `G = transport.G`) with
`ReducedTransport.descent` (`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0`); the two legs share the SAME
`transport.G`, so they compose with no coherence gap. This is the geometric `O1` for `#145`'s
`binding_recursion_of_step` (`hstep`), modulo identifying `χ (0,0)` with the node's deepest point. The
producer (per-node blow-up plumbing, = pending `#104`) supplies the chart + squeeze; `transport.hGne` is the
non-leaf guard. Stated as a plain lemma (not a bundled structure) — the recursion wires it directly. -/
theorem dlnLoss_O1_descent {M : Fin (L + 1) → ℕ} {S : ChainDimSplit M} {nReg : ℕ}
    {Y : Type} [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y] [OpensMeasurableSpace Y] [Zero Y]
    (transport : ReducedTransport S Y)
    (hGmeas : Measurable transport.G)
    (hGne : ∃ U ∈ nhds (0 : Y), ∀ᵐ z ∂(volume.restrict U), transport.G z ≠ 0)
    (chart : ((Fin nReg → ℝ) × Y) ≃ₜ Params M)
    (hmp : MeasurePreserving chart volume volume) (hemb : MeasurableEmbedding chart)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hsq : ∃ U ∈ nhds ((0, 0) : (Fin nReg → ℝ) × Y), ∀ w ∈ U,
        0 ≤ smoothBlockSplitForm transport.G w
          ∧ c₁ * smoothBlockSplitForm transport.G w ≤ (dlnLoss M 0) (chart w)
          ∧ (dlnLoss M 0) (chart w) ≤ c₂ * smoothBlockSplitForm transport.G w) :
    rlctAtOn (dlnLoss M 0) (chart (0, 0))
      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) := by
  rw [dlnLoss_chart_squeeze_descent chart hmp hemb transport.G hGmeas hGne c₁ c₂ hc₁ hc₂ hsq,
    transport.descent]

end DLNFibre.DLN.RLCT
