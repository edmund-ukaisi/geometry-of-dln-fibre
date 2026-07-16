import DLNFibre.DLN.RLCT.Validate.RouteMSJHcellNull

set_option linter.style.longLine false

/-!
# `RouteMSJEdgeCellDrop` — the generic-cell a-fortiori (edge brick wrapper, hBackbone-independent)

Thread `genm-tideD` (edge dispatch arm). The **cell-drop** half of the edge brick `edge_coupledBox_lt_top`:
the generic cell `box ∩ projDeep⁻¹'(deepCell … i)` sits inside the full box `paramsBoxM ×ˢ matBox`, so a
finite full-box coupled-box integral (which satred's edge-descent lemma / `hBackbone` supplies, having
absorbed the outerDom peel + a.e.-positivity + `|v'|^{−a}` disposal + the redChain reduction) dominates the
per-cell integral a-fortiori (`lintegral_mono_set`, integrand `≥ 0`).

This is the `hBackbone`-INDEPENDENT half of the wrapper: once `hBackbone` is pinned (yielding the full-box
finiteness `hbox`), `edge_coupledBox_lt_top = edge_generic_cells_of_box hbox`. Matches the
`GenericCellFinite`-shaped `h_edge_b1` slot of `routeMBoxThresholdFinite_of_coupled_bsplit`
(arch1build, `RouteMSJHcellNull` on `genm-integration`).
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory DeepAtlas
open scoped ENNReal

variable {L : ℕ}

/-- **The generic-cell a-fortiori (cell-drop).** A finite full-box coupled-box integral dominates every
per-cell integral: for each deep-atlas cell `i`, `∫_{box ∩ projDeep⁻¹'(deepCell … i)} coupledBox ≤
∫_{box} coupledBox` (`cell ⊆ box`, `lintegral_mono_set`), so `hbox : ∫_box coupledBox < ⊤` gives every
cell `< ⊤` — in particular the generic cells (`cellRankIndex i = deepTailMin M`), the `GenericCellFinite`
shape the `h_edge_b1` slot consumes. Integrand-agnostic, `hBackbone`-independent: the analytic content is
the full-box finiteness `hbox` (satred's edge descent), this is only the a-fortiori restriction. -/
theorem edge_generic_cells_of_box (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (c' : ℝ)
    (hbox : ∫⁻ p in paramsBoxM (redChain u M) 1 ×ˢ matBox (M 1 - u) (M 2) 1,
        coupledBoxIntegrand M u c' p < ⊤) :
    ∀ i : CRIndex (dropHead (redChain u M)),
        cellRankIndex (dropHead (redChain u M)) i = deepTailMin M →
        ∫⁻ p in (paramsBoxM (redChain u M) 1 ×ˢ matBox (M 1 - u) (M 2) 1)
            ∩ projDeep M u ⁻¹' (deepCell (dropHead (redChain u M)) (dropHead (redChain u M) 0) L
                le_rfl (dropHead (redChain u M) (Fin.last L)) i
                (fun _ => (1 : Matrix (Fin (dropHead (redChain u M) (Fin.last L)))
                  (Fin (dropHead (redChain u M) (Fin.last L))) ℝ))),
          coupledBoxIntegrand M u c' p < ⊤ := by
  intro i _
  exact lt_of_le_of_lt (lintegral_mono_set Set.inter_subset_left) hbox

end DLNFibre.DLN.RLCT
