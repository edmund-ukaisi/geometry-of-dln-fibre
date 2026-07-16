import DLNFibre.DLN.RLCT.Validate.RouteMSJEdgeNullCell
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankRec

set_option linter.style.longLine false

/-!
# `RouteMSJHcellNull` — the null-layer discharge of `coupledBox_lt_top_of_cells`'s `hcell ∀ i`

The per-cell coupled-box finiteness `hcell : ∀ i, ∫coupledBox over cell i < ⊤` (the sole hole of
`coupledBox_lt_top_of_cells`, the coupled-box G2) splits by the deep-atlas rank trichotomy
`cellRankIndex i ≤ deepTailMin M` (`cellRank_le_deepTailMin`, corankrec):

* `cellRankIndex i < deepTailMin M` (a **deficient**/null cell): the cell lies in a null set of the
  `z`-marginal (`deepFactor_rank_ge_deepTailMin_ae`), so `∫coupledBox = 0 < ⊤` UNCONDITIONALLY
  (`coupledBox_deficientCell_null`, dbuild/joint). Integrand-agnostic.
* `cellRankIndex i = deepTailMin M` (the unique **generic** co-null cell): the real content — interior
  (`a+b ≤ deepTailMin`) or edge (`a+b = deepTailMin + 1`). Left as the hypothesis `hgen`.

So `coupledBox_cell_lt_top_of_generic` REDUCES the `∀ i` hole to the single generic cell: the null layer
(the bulk of the atlas) is closed with no analytic content, and the remaining work is exactly the
generic-cell finiteness. This is the honest floor for the item-4 fill; the generic cell's interior arm
(via schurB's charge free-box, through a `frontChargeIntegrand ↔ chargeGramDet` bridge not yet landed) and
its edge arm (edgeasm's `edge_coupledBox_lt_top`) discharge `hgen` when those land.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory DeepAtlas
open scoped ENNReal

variable {L : ℕ}

/-- **Null-layer discharge: `hcell ∀ i` reduces to the generic cell.** Every deep-atlas cell has
`cellRankIndex i ≤ deepTailMin M` (`cellRank_le_deepTailMin`). On a deficient cell
(`cellRankIndex i < deepTailMin M`) the coupled-box integral is `0` (`coupledBox_deficientCell_null`, the
deep-rank locus is null), hence `< ⊤` unconditionally; only the generic cell (`cellRankIndex i = deepTailMin M`)
needs the hypothesis `hgen`. Feeds `coupledBox_lt_top_of_cells`'s `hcell` from the generic-cell finiteness. -/
theorem coupledBox_cell_lt_top_of_generic (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (c' : ℝ)
    (hgen : ∀ i : CRIndex (dropHead (redChain u M)),
        cellRankIndex (dropHead (redChain u M)) i = deepTailMin M →
        ∫⁻ p in (paramsBoxM (redChain u M) 1 ×ˢ matBox (M 1 - u) (M 2) 1)
            ∩ projDeep M u ⁻¹' (deepCell (dropHead (redChain u M)) (dropHead (redChain u M) 0) L
                le_rfl (dropHead (redChain u M) (Fin.last L)) i
                (fun _ => (1 : Matrix (Fin (dropHead (redChain u M) (Fin.last L)))
                  (Fin (dropHead (redChain u M) (Fin.last L))) ℝ))),
          coupledBoxIntegrand M u c' p < ⊤) :
    ∀ i : CRIndex (dropHead (redChain u M)),
        ∫⁻ p in (paramsBoxM (redChain u M) 1 ×ˢ matBox (M 1 - u) (M 2) 1)
            ∩ projDeep M u ⁻¹' (deepCell (dropHead (redChain u M)) (dropHead (redChain u M) 0) L
                le_rfl (dropHead (redChain u M) (Fin.last L)) i
                (fun _ => (1 : Matrix (Fin (dropHead (redChain u M) (Fin.last L)))
                  (Fin (dropHead (redChain u M) (Fin.last L))) ℝ))),
          coupledBoxIntegrand M u c' p < ⊤ := by
  intro i
  rcases (cellRank_le_deepTailMin M u i).lt_or_eq with hlt | heq
  · rw [coupledBox_deficientCell_null M u c' i hlt]; exact ENNReal.zero_lt_top
  · exact hgen i heq

/-- **Per-`M` coupled closure from the GENERIC-cell finiteness (null layer banked).** Same as
`routeMBoxThresholdFinite_of_coupled` but the per-shell per-cell hole is only the GENERIC cells
(`cellRankIndex i = deepTailMin M`) — the deficient/null cells are discharged internally by
`coupledBox_cell_lt_top_of_generic`. So the coupled route delivers `RouteMBoxThresholdFinite M` from
`hgeneric` (generic-cell finiteness on `j<r`: interior via schurB's charge free-box through the
`frontChargeIntegrand ↔ chargeGramDet` bridge, edge via `edge_coupledBox_lt_top`), `hG1`, `hbdryShell`.
Makes the remaining item-4 hole PRECISE: only the single co-null generic cell per interior shell. -/
theorem routeMBoxThresholdFinite_of_coupled_generic
    (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ) (ε : ℝ)
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i) (htb : t + 1 ≤ min (M 0) (M 1))
    (hbind : minAdm M = peelCharge M t + minAdm (redChain t M))
    (hred : 0 < minAdm (redChain t M))
    (hG1 : ∀ c' : ℝ, routeMLayerBoxIntegral M c' 1
        ≤ ∑ j : Fin (min (M 0 - t) (M 1 - t) + 1),
            ∑ _ρ : Fin (t + (j : ℕ)) ↪ Fin (M 0),
              ∑ κ : Fin (t + (j : ℕ)) ↪ Fin (M 1),
                shellSpineIntegrand M (t + (j : ℕ)) κ ε (min (M 0 - t) (M 1 - t)) j c')
    (hgeneric : ∀ (c' : ℝ) (j : Fin (min (M 0 - t) (M 1 - t) + 1)),
        (j : ℕ) < min (M 0 - t) (M 1 - t) →
        ∀ i : CRIndex (dropHead (redChain (t + (j : ℕ)) M)),
        cellRankIndex (dropHead (redChain (t + (j : ℕ)) M)) i = deepTailMin M →
        ∫⁻ p in (paramsBoxM (redChain (t + (j : ℕ)) M) 1 ×ˢ matBox (M 1 - (t + (j : ℕ))) (M 2) 1)
            ∩ projDeep M (t + (j : ℕ)) ⁻¹'
              (deepCell (dropHead (redChain (t + (j : ℕ)) M)) (dropHead (redChain (t + (j : ℕ)) M) 0) L
                le_rfl (dropHead (redChain (t + (j : ℕ)) M) (Fin.last L)) i
                (fun _ => (1 : Matrix (Fin (dropHead (redChain (t + (j : ℕ)) M) (Fin.last L)))
                  (Fin (dropHead (redChain (t + (j : ℕ)) M) (Fin.last L))) ℝ))),
          coupledBoxIntegrand M (t + (j : ℕ)) c' p < ⊤)
    (hbdryShell : ∀ (c' : ℝ) (j : Fin (min (M 0 - t) (M 1 - t) + 1))
        (κ : Fin (t + (j : ℕ)) ↪ Fin (M 1)),
        (j : ℕ) = min (M 0 - t) (M 1 - t) →
        shellSpineIntegrand M (t + (j : ℕ)) κ ε (min (M 0 - t) (M 1 - t)) j c' < ⊤) :
    RouteMBoxThresholdFinite M :=
  routeMBoxThresholdFinite_of_coupled M t ε ht1 hnd htb hbind hred hG1
    (fun c' j hj => coupledBox_cell_lt_top_of_generic M (t + (j : ℕ)) c' (hgeneric c' j hj))
    hbdryShell

end DLNFibre.DLN.RLCT
