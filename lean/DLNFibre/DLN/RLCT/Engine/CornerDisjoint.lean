import DLNFibre.DLN.RLCT.Engine.GeoChart

/-!
# `DLNFibre.DLN.RLCT.Engine.CornerDisjoint` — the corner-disjointness pair (t17)

The construction-freshness content that discharges `ledgerMonomial_comp_spectator`'s two disjointness
hypotheses (`GeoFoldRegroup.lean`, t14). At a reachable step node emitted at state `s`, an OLD
divisor's diagonal cell `birthFlatCoord M s k h` (the `flatCoordOf`-diagonal `(a, b, b)` of the
stored birth corner `(a, b) = s.divBirthCoord k`) is:

* **(a) a SPECTATOR** of the node's chart — not one of the node's center cells `cNodeOf M node hd`; and
* **(b) ≠ the node's `diagTargetOf`** — distinct from the diagonal the new edge chart reads.

**The geometric heart is one atom** (`birthFlatCoord_ne_diag_layer_cell`): an old divisor's diagonal
never lands on a cell `(s.layer, row, col)` with `row ≥ s.cleared`. If it did, `flatCoordOf`-injectivity
(`flatCoordOf_val_inj`) forces the birth layer `a = s.layer` and `b = row`, but `DivBirthInv` FRESHNESS
(a corner at the current layer has `b < cleared`, `DivBirthReach:16`) gives `b < s.cleared ≤ row = b`.
The residual-block cells (case-2 / the case-1(2) `d`-block) and the fresh `(layer, cleared)` corner
(the case-2 / case-1(2) `diagTargetOf`) are all such cells, so the atom covers them uniformly.

**Case split on the node class** (`nodeOccMin`):
* **case-2** (`nodeOccMin = none`): the center is the full residual block; EVERY old divisor is a
  spectator, and the `diagTargetOf` is the fresh corner — so the full-quantifier `hspec`/`hdt` that
  `ledgerMonomial_comp_spectator` consumes hold VERBATIM (`case2_spectator`, `case2_diagTarget`).
* **case-1** (`nodeOccMin = some target`): the center ALSO contains the `u`-corner, which IS the merged
  divisor `f = chooseMin`'s own diagonal (`uCornerSel = birthFlatCoord s f`); likewise the case-1(1)
  edge's `diagTargetOf`. So the full-quantifier form is FALSE for `k = f`; the disjointness holds only
  for the OTHER divisors (`k ≠ f`), supplied here for the merge-peeled maintenance (t14's lane).
* **rollover / terminal**: `dCenterOfNode = 0`, no center, `hspec` vacuous.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The `birthFlatCoord = flatCoordOf`-diagonal reduction (local, `DivBirthReach`-only) -/

/-- **On a valid corner, `birthFlatCoord` is the `flatCoordOf`-diagonal** `(a, b, b)` of the stored
birth corner `(a, b) = s.divBirthCoord k`. Local re-derivation of the GeoFoldRegroup `(β)`-kernel from
`birthFlatCoord_of_valid` + `flatCoordOf`'s definition (avoids importing t14's module — GeoFoldRegroup
will consume THIS file, not the reverse). -/
theorem birthFlatCoord_eq_flatCoordOf' (M : Fin (L + 1) → ℕ) (s : ConState L) (k : Fin s.numDiv)
    (h : 0 < flatDim M) (hv : CornerValid M (s.divBirthCoord k)) :
    ∃ (hL : (s.divBirthCoord k).1 < L)
      (hi : (s.divBirthCoord k).2 < M (Fin.castSucc ⟨(s.divBirthCoord k).1, hL⟩))
      (hj : (s.divBirthCoord k).2 < M (Fin.succ ⟨(s.divBirthCoord k).1, hL⟩)),
      birthFlatCoord M s k h
        = flatCoordOf M ⟨(s.divBirthCoord k).1, hL⟩ ⟨(s.divBirthCoord k).2, hi⟩
            ⟨(s.divBirthCoord k).2, hj⟩ := by
  obtain ⟨hL, hi, hj, heq⟩ := birthFlatCoord_of_valid (h := h) hv
  exact ⟨hL, hi, hj, by rw [heq, flatCoordOf]⟩

/-! ## The geometric atom: an old divisor's diagonal avoids the layer's `col ≥ cleared` cells -/

/-- **The corner-disjointness atom** (the fidelity heart): an OLD divisor's diagonal
`birthFlatCoord M s k h = (a, b, b)` never equals a cell `(s.layer, row, col)` whose ROW is at or above
the cleared count (`s.cleared ≤ row`). By `flatCoordOf_val_inj` a coincidence forces `a = s.layer` and
`b = row`; then `DivBirthInv` freshness gives `b < s.cleared ≤ row = b` — contradiction. Both the
residual-block cells and the fresh `(layer, cleared)` corner are such cells (`row = cleared + r ≥
cleared`, resp. `row = cleared`), so this single atom serves case-2 spectator + both `diagTargetOf`
branches. -/
theorem birthFlatCoord_ne_diag_layer_cell {M : Fin (L + 1) → ℕ} (s : ConState L)
    (dinv : DivBirthInv M s) (h : 0 < flatDim M) (k : Fin s.numDiv)
    {sf : Fin L} (hsf : (sf : ℕ) = s.layer) {row col : ℕ} (hrowge : s.cleared ≤ row)
    (hrow : row < M sf.castSucc) (hcol : col < M sf.succ) :
    birthFlatCoord M s k h ≠ flatCoordOf M sf ⟨row, hrow⟩ ⟨col, hcol⟩ := by
  obtain ⟨hvalid, _, hfresh, _⟩ := dinv
  intro heq
  obtain ⟨hL, hi, hj, hbf⟩ := birthFlatCoord_eq_flatCoordOf' M s k h (hvalid k)
  rw [hbf] at heq
  obtain ⟨ha, hb, -⟩ := flatCoordOf_val_inj heq
  have haLayer : (s.divBirthCoord k).1 = s.layer := by
    have : ((⟨(s.divBirthCoord k).1, hL⟩ : Fin L) : ℕ) = (sf : ℕ) := ha
    simpa [hsf] using this
  have hbfresh : (s.divBirthCoord k).2 < s.cleared := hfresh k haLayer
  have hbrow : (s.divBirthCoord k).2 = row := hb
  omega

/-! ## The injectivity atom (distinct divisors, distinct diagonals) -/

/-- **Distinct old divisors have distinct diagonals** — the `k ≠ f` disjointness (`birthFlatCoord`
injective under `DivBirthInv`). Behind the case-1 `u`-corner spectator for the non-merge divisors: the
`u`-corner IS `birthFlatCoord s f`, so an old divisor `k ≠ f` avoids it. -/
theorem birthFlatCoord_ne_of_ne {M : Fin (L + 1) → ℕ} {s : ConState L} (dinv : DivBirthInv M s)
    (h : 0 < flatDim M) {k f : Fin s.numDiv} (hkf : k ≠ f) :
    birthFlatCoord M s k h ≠ birthFlatCoord M s f h := fun heq =>
  hkf (birthFlatCoord_injective (h := h) dinv heq)

/-! ## Node ↔ state field bridge (from the step decision) -/

/-- **A built-tree branch node carries the state's `layer`/`cleared`** — extracted from the step
`ConDecision` (`hlayer` + `hnode`'s ledger-core match), no `occ` enumeration. Every oracle branch
builds `node = s.toStepData …`, so these are the decision's own guarantees. -/
theorem step_node_layer_cleared {M : Fin (L + 1) → ℕ} (s : ConState L)
    (node : StepData M) (edges : List (Edge M))
    (htree : buildTree M (conOracle M) s = ResolutionTree.branch node edges) :
    node.layer = s.layer ∧ node.cleared = s.cleared := by
  cases hoc : conOracle M s with
  | terminal l' hleaf =>
      rw [buildTree_terminal M (conOracle M) s l' hleaf hoc] at htree
      exact absurd htree (by simp)
  | step node' children hnode hlayer hstep =>
      rw [buildTree_step M (conOracle M) s node' children hoc] at htree
      obtain ⟨rfl, -⟩ := ResolutionTree.branch.inj htree
      exact ⟨hlayer, congrArg ResolutionTree.RootLedger.cleared hnode⟩

/-! ## The case-2 center reduction: every center cell is a residual-block cell -/

/-- **`centerSelCase` at `occ = none` is `resBlockOrFallback`** — with `occ` a VARIABLE (so `subst`
reduces the `match`), transporting the dependent dimension by `Fin.cast`. The bridge that lets a node
whose `nodeOccMin` is only propositionally `none` reduce its selector to the residual block. -/
theorem centerSelCase_none_eq_resBlockOrFallback {M : Fin (L + 1) → ℕ} (node : StepData M)
    (occ : Option ℕ) (hocc : occ = none)
    (hd' : occ.elim (node.resRows * node.resCols)
      (fun t => 1 + (t - node.cleared) * node.resCols) ≤ flatDim M)
    (hdimeq : occ.elim (node.resRows * node.resCols)
      (fun t => 1 + (t - node.cleared) * node.resCols) = node.resRows * node.resCols)
    (j : Fin (occ.elim (node.resRows * node.resCols)
      (fun t => 1 + (t - node.cleared) * node.resCols))) :
    centerSelCase M node occ hd' j
      = resBlockOrFallback M node.layer node.cleared node.resRows node.resCols
          (hdimeq ▸ hd') (Fin.cast hdimeq j) := by
  subst hocc; rfl

/-- **At a case-2 node, `realCNode` lands in the residual block** — its value at any center index is a
`resBlockCenterIndices` cell (`realCNode = centerSelCase (nodeOccMin) ∘ finCongr`, and at `occ = none`
`centerSelCase = resBlockOrFallback = resBlockCenterIndices` on-cone). The `finCongr` transports the
node's `dCenterOfNode`-index to the block's `resRows·resCols`-index. -/
theorem realCNode_case2_mem {M : Fin (L + 1) → ℕ} (node : StepData M)
    (h1 : ¬ L ≤ node.layer) (h2 : ¬ widthMinUpto M (node.layer + 1) ≤ node.cleared)
    (hocc : nodeOccMin M node = none)
    (hd : dCenterOfNode M node ≤ flatDim M) (hs : node.layer < L)
    (hrow : node.cleared + node.resRows ≤ M (⟨node.layer, hs⟩ : Fin L).castSucc)
    (hcol : node.cleared + node.resCols ≤ M (⟨node.layer, hs⟩ : Fin L).succ)
    (i : Fin (dCenterOfNode M node)) :
    ∃ j : Fin (node.resRows * node.resCols),
      realCNode M node hd i
        = resBlockCenterIndices M ⟨node.layer, hs⟩ node.cleared node.resRows node.resCols
            hrow hcol j := by
  have hdim : dCenterOfNode M node = node.resRows * node.resCols := by
    rw [dCenterOfNode_nonterminal M node h1 h2, hocc]; rfl
  have hdimeq : (nodeOccMin M node).elim (node.resRows * node.resCols)
      (fun t => 1 + (t - node.cleared) * node.resCols) = node.resRows * node.resCols :=
    (dCenterOfNode_nonterminal M node h1 h2).symm.trans hdim
  refine ⟨finCongr hdim i, ?_⟩
  rw [← resBlockOrFallback_eq_resBlockCenterIndices M node.layer node.cleared
    node.resRows node.resCols (hdim ▸ hd) hs hrow hcol]
  simp only [realCNode, dif_neg h1, dif_neg h2]
  rw [centerSelCase_none_eq_resBlockOrFallback node (nodeOccMin M node) hocc _ hdimeq _]
  congr 1

/-! ## `s.layer < L` at a branch node (non-terminal) -/

/-- **A built-tree branch node lives below `L`** — if `L ≤ s.layer` the oracle terminates (a leaf),
contradicting `htree`'s `branch`. -/
theorem layer_lt_of_branch {M : Fin (L + 1) → ℕ} (s : ConState L)
    (node : StepData M) (edges : List (Edge M))
    (htree : buildTree M (conOracle M) s = ResolutionTree.branch node edges) :
    s.layer < L := by
  by_contra hc
  have hge : L ≤ s.layer := not_lt.mp hc
  have horacle : conOracle M s = oracleTerminal M s := by unfold conOracle; rw [dif_pos hge]
  rw [buildTree_terminal M (conOracle M) s (leafOfState M s) (leafOfState_rootLedger M s)
    horacle] at htree
  exact absurd htree (by simp)

/-! ## The case-2 corner-disjointness pair (`ledgerMonomial_comp_spectator`, verbatim) -/

/-- **case-2 `hspec`** (t14's `ledgerMonomial_comp_spectator` first hypothesis, VERBATIM): at a
reachable case-2 node (`nodeOccMin = none`), EVERY old divisor's diagonal is a spectator of the
node's chart — distinct from every center cell `cNodeOf M node hd i`. The center is the full residual
block (`realCNode_case2_mem`), and every old divisor avoids it (`birthFlatCoord_ne_diag_layer_cell`:
freshness/layer). -/
theorem case2_spectator {M : Fin (L + 1) → ℕ} (s : ConState L) (dinv : DivBirthInv M s)
    (node : StepData M) (edges : List (Edge M))
    (htree : buildTree M (conOracle M) s = ResolutionTree.branch node edges)
    (hnr : ¬ widthMinUpto M (s.layer + 1) ≤ s.cleared)
    (hocc : nodeOccMin M node = none)
    (h : 0 < flatDim M) (hd : dCenterOfNode M node ≤ flatDim M) :
    ∀ (k : Fin s.numDiv) (i : Fin (dCenterOfNode M node)),
      cNodeOf M node hd i ≠ birthFlatCoord M s k h := by
  intro k i
  obtain ⟨hlayer, hcleared⟩ := step_node_layer_cleared s node edges htree
  have hlive : s.layer < L := layer_lt_of_branch s node edges htree
  have h1 : ¬ L ≤ node.layer := by rw [hlayer]; exact not_le.mpr hlive
  have h2 : ¬ widthMinUpto M (node.layer + 1) ≤ node.cleared := by rw [hlayer, hcleared]; exact hnr
  have hdim : dCenterOfNode M node = node.resRows * node.resCols := by
    rw [dCenterOfNode_nonterminal M node h1 h2, hocc]; rfl
  obtain ⟨hs, hrow, hcol, -⟩ :=
    centerSelCase_none_geometric_of_conOracle s node edges htree hnr hocc (hdim ▸ hd)
  rw [cNodeOf_eq_realCNode_of_conOracle s dinv node edges htree hd]
  obtain ⟨j, hj⟩ := realCNode_case2_mem node h1 h2 hocc hd hs hrow hcol i
  rw [hj]
  simp only [resBlockCenterIndices]
  refine (birthFlatCoord_ne_diag_layer_cell s dinv h k (sf := ⟨node.layer, hs⟩) hlayer
    ?_ _ _).symm
  rw [hcleared]; exact Nat.le_add_right _ _

end DLNFibre.DLN.RLCT.Engine
