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

/-! ## The 4-way b-split of the generic-cell obligation -/

/-- **The generic-cell coupled-box finiteness at cut `u`** — the `hgen` hypothesis of
`coupledBox_cell_lt_top_of_generic`, named so the 4-way dispatch reads cleanly. Definitionally the
per-generic-cell (`cellRankIndex i = deepTailMin M`) coupled-box integral finiteness. -/
def GenericCellFinite (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (c' : ℝ) : Prop :=
  ∀ i : CRIndex (dropHead (redChain u M)),
      cellRankIndex (dropHead (redChain u M)) i = deepTailMin M →
      ∫⁻ p in (paramsBoxM (redChain u M) 1 ×ˢ matBox (M 1 - u) (M 2) 1)
          ∩ projDeep M u ⁻¹' (deepCell (dropHead (redChain u M)) (dropHead (redChain u M) 0) L
              le_rfl (dropHead (redChain u M) (Fin.last L)) i
              (fun _ => (1 : Matrix (Fin (dropHead (redChain u M) (Fin.last L)))
                (Fin (dropHead (redChain u M) (Fin.last L))) ℝ))),
        coupledBoxIntegrand M u c' p < ⊤

/-- **The 4-way b-split dispatch of the generic-cell obligation.** At an interior shell `u = t + j`
(`j < r = min(M₀−t, M₁−t)`, so `a = M₀−u ≥ 1`, `b = M₁−u ≥ 1`), the generic-cell finiteness splits into
FOUR arms keyed on the decidable `(a+b vs deepTailMin) × (b vs 1)` regime — EXHAUSTIVE and DISJOINT: the
`a+b ≤ deepTailMin+1` cover is `bindingCut_ab_le_deepTailMin_succ` (at cut `t`, extended to `u = t+j` by
`Nat.sub_le_sub_left` monotonicity — corankrec's deep-corank-empty scan: NO `a+b ≥ deepTailMin+2` regime),
so `a+b ≤ deepTailMin` (interior) ∪ `a+b = deepTailMin+1` (edge) is a trichotomy split, and `b ≥ 1`
(from `hj`) makes `b = 1` ∪ `b ≥ 2` the other axis. Each arm is a NAMED hole, closed by its piece as it
lands: `h_int_b1` ← charge-factoring (`frontChargeIntegrand_eq_charge_mul_loss`) + `chargeFreeBox_b1a1` +
the uniform-`frontLossIntegral` bound (couplerad); `h_int_b2` ← the (D)/slabD `chargeFreeBox_of_inner`;
`h_edge_b1` ← edgered's corank-one edge brick; `h_edge_b2` ← R3 (couplerad). Banks the dispatch STRUCTURE
sorry-free over the atlas. -/
theorem coupledBox_cell_generic_of_bsplit (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ) (c' : ℝ)
    (ht1 : t + 1 ≤ min (M 0) (M 1))
    (hbind : minAdm M = peelCharge M t + minAdm (redChain t M))
    (j : ℕ) (hj : j < min (M 0 - t) (M 1 - t))
    (h_int_b1 : (M 0 - (t + j)) + (M 1 - (t + j)) ≤ deepTailMin M → M 1 - (t + j) = 1 →
        GenericCellFinite M (t + j) c')
    (h_int_b2 : (M 0 - (t + j)) + (M 1 - (t + j)) ≤ deepTailMin M → 2 ≤ M 1 - (t + j) →
        GenericCellFinite M (t + j) c')
    (h_edge_b1 : (M 0 - (t + j)) + (M 1 - (t + j)) = deepTailMin M + 1 → M 1 - (t + j) = 1 →
        GenericCellFinite M (t + j) c')
    (h_edge_b2 : (M 0 - (t + j)) + (M 1 - (t + j)) = deepTailMin M + 1 → 2 ≤ M 1 - (t + j) →
        GenericCellFinite M (t + j) c') :
    GenericCellFinite M (t + j) c' := by
  have hcov : (M 0 - (t + j)) + (M 1 - (t + j)) ≤ deepTailMin M + 1 := by
    have hc := bindingCut_ab_le_deepTailMin_succ M t ht1 hbind
    have h0 : M 0 - (t + j) ≤ M 0 - t := Nat.sub_le_sub_left (Nat.le_add_right t j) _
    have h1 : M 1 - (t + j) ≤ M 1 - t := Nat.sub_le_sub_left (Nat.le_add_right t j) _
    omega
  have hb1 : 1 ≤ M 1 - (t + j) := by omega
  rcases (show (M 0 - (t + j)) + (M 1 - (t + j)) ≤ deepTailMin M
      ∨ (M 0 - (t + j)) + (M 1 - (t + j)) = deepTailMin M + 1 by omega) with hint | hedge
  · rcases (show M 1 - (t + j) = 1 ∨ 2 ≤ M 1 - (t + j) by omega) with hb | hb
    · exact h_int_b1 hint hb
    · exact h_int_b2 hint hb
  · rcases (show M 1 - (t + j) = 1 ∨ 2 ≤ M 1 - (t + j) by omega) with hb | hb
    · exact h_edge_b1 hedge hb
    · exact h_edge_b2 hedge hb

/-- **`hcell` (∀-cell coupled-box finiteness) from the 4-way b-split.** Composes the b-split dispatch
(`coupledBox_cell_generic_of_bsplit`, generic cells) with the null-layer discharge
(`coupledBox_cell_lt_top_of_generic`, deficient cells `∫ = 0`). Drop-in for the coupled route's `hcell`
slot at the interior shell `u = t + j`, reduced to the FOUR named regime arms. -/
theorem coupledBox_cell_lt_top_of_bsplit (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ) (c' : ℝ)
    (ht1 : t + 1 ≤ min (M 0) (M 1))
    (hbind : minAdm M = peelCharge M t + minAdm (redChain t M))
    (j : ℕ) (hj : j < min (M 0 - t) (M 1 - t))
    (h_int_b1 : (M 0 - (t + j)) + (M 1 - (t + j)) ≤ deepTailMin M → M 1 - (t + j) = 1 →
        GenericCellFinite M (t + j) c')
    (h_int_b2 : (M 0 - (t + j)) + (M 1 - (t + j)) ≤ deepTailMin M → 2 ≤ M 1 - (t + j) →
        GenericCellFinite M (t + j) c')
    (h_edge_b1 : (M 0 - (t + j)) + (M 1 - (t + j)) = deepTailMin M + 1 → M 1 - (t + j) = 1 →
        GenericCellFinite M (t + j) c')
    (h_edge_b2 : (M 0 - (t + j)) + (M 1 - (t + j)) = deepTailMin M + 1 → 2 ≤ M 1 - (t + j) →
        GenericCellFinite M (t + j) c') :
    ∀ i : CRIndex (dropHead (redChain (t + j) M)),
        ∫⁻ p in (paramsBoxM (redChain (t + j) M) 1 ×ˢ matBox (M 1 - (t + j)) (M 2) 1)
            ∩ projDeep M (t + j) ⁻¹' (deepCell (dropHead (redChain (t + j) M))
                (dropHead (redChain (t + j) M) 0) L le_rfl (dropHead (redChain (t + j) M) (Fin.last L)) i
                (fun _ => (1 : Matrix (Fin (dropHead (redChain (t + j) M) (Fin.last L)))
                  (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ))),
          coupledBoxIntegrand M (t + j) c' p < ⊤ :=
  coupledBox_cell_lt_top_of_generic M (t + j) c'
    (coupledBox_cell_generic_of_bsplit M t c' ht1 hbind j hj h_int_b1 h_int_b2 h_edge_b1 h_edge_b2)

end DLNFibre.DLN.RLCT
