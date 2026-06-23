import DLNFibre.DLN.RLCT.Validate.RouteMNodeDescentBuild
import DLNFibre.DLN.RLCT.Foundations.LossContinuity

/-!
# `RouteMO1Bridge` — the G-b O1 bridge: `dlnLoss`-level per-node descent (fm3 #148/#104)

The per-node `hstep` the binding recursion (`BindingRecursion.binding_recursion_of_step`) consumes, at the
ACTUAL network loss `dlnLoss M 0` (not the abstract `flatCore`): for a non-leaf node, the local RLCT at the
deepest point splits as
`rlctAtOn (dlnLoss M 0) (chart (0,0)) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0`.

This is the GEOMETRIC half of G-b (Codex route verdict: the recursion route; rs-grind's `#143` supplies the
combinatorial `nReg`/telescope/well-foundedness facts). It composes:
- `dlnLoss_chart_squeeze_descent` — the chart transport (`rlctAtOn_comp_homeomorph`) + the chart-free squeeze
  (`schur_recursion_step_squeeze`): transport `dlnLoss M 0` to the chart source, where it is squeezed by
  `smoothBlockSplitForm G`, giving `nReg/2 + rlctAtOn (G²) 0`;
- `ReducedTransport.descent` — `rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0` (crux2's det-1 MP reindex).

The producer obligation isolated here (the only formaliser-weeks piece): the per-node `O1Presentation`
datum — a measure-preserving chart `χ : ((Fin nReg → ℝ) × Y) ≃ₜ Params M` and the SQUEEZE of `dlnLoss M 0 ∘ χ`
by `smoothBlockSplitForm G` near `(0,0)`. The (2,2,2) anchor cert
(`case222-hnode-schur-cert.md`) is the C1 prototype: `dlnLoss = ‖A·B‖²`, the A-pivot blow-up presents the
core in Schur form `∑Erow² + ‖bcol·Erow + SΓ‖²`, `G²` the reduced `(1,1,2)` loss, `nReg = 2`.
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

end DLNFibre.DLN.RLCT
