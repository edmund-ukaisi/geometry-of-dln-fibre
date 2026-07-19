import DLNFibre.DLN.RLCT.Engine.QNodeChart
import DLNFibre.DLN.RLCT.Engine.DivBirthReach

/-!
# `DLNFibre.DLN.RLCT.Engine.QNodeCarrier` — the per-NODE center split (`dCenterOfNode` + `qNodeOf`)

The per-node cover ruling (cert-psi-mix §R-b): the cover shares **one** `q` per blow-up node, of
dimension `dCenterOfNode` (the node's FULL center), and all `dCenterOfNode` pivots ride that single
`q` (the per-edge `qEdgeOf`/`dCenterOfEdge` were a verified conflation — kept as gauges). This
module
supplies coverage's `QNodeFam M dCenterOfNode` instance.

## `dCenterOfNode` (option (iv): recompute the case, zero StepData-field ripple)

`dCenterOfNode : StepData M → ℕ` is the FULL node center dimension:
* rollover / terminal ⟹ `0` (chartless);
* case-2 ⟹ `resRows · resCols` (the full residual block);
* case-1 ⟹ `1 + runLen · resCols` (the `u`-pivot coord + the case-1(2) `d`-block).

The **case** is on the EDGE, not the node — and case-1/case-2 nodes are the SAME `StepData` shape
(`toStepData`), distinguished only by whether an occupied clearing level is in range. So the case is
recomputed at the StepData level via the *same* dispatch `conOracle`/`classify` use (the guards
`L ≤ layer` / `widthMinUpto (layer+1) ≤ cleared`, then `occ.min?`). `StepData` carries
`layer`/`cleared`/`numDiv`/`divProfile` verbatim from the state (`toStepData`), so the recomputation
agrees with the oracle's choice on every built-tree node (`dCenterOfNode_edgeSum`). This is option
(iv): NO new `runLen` carrier field — `runLen = occ.min? − cleared` is recoverable from the profile
ledger the node already holds, so there is zero StepData-constructor ripple (contrast option (i)).

## `qNodeOf : QNodeFam M dCenterOfNode`

`qNodeOf node hd = qOfCenter M (cNodeOf node hd) (cNodeOf_injective …)`, where `cNodeOf` selects the
node's `dCenterOfNode`-many center coordinates: case-1 = the `u`-corner (the merged divisor's
immutable birth corner, via the recomputed Def-4 chooser `chooseMinData`) `++` the case-1(2)
`d`-block
(`resBlockCenterIndices`); case-2 = the block alone. Injectivity is total via a classical fallback
(off the reachable cone the intended selector may collide; there we fall back to `Fin.castLE`), so
`qNodeOf` is a well-formed `Homeomorph` for every node; the ON-CONE fidelity (that the fallback is
not taken — the intended selector IS injective) is `cNodeOf_eq_realCNode`, given `RealCNodeFacts`
(the per-node corner/block/chooser facts the reachable cone's `DivBirthInv`/`OracleInv` supply).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## `dCenterOfNode` and its per-branch reductions -/

/-- The `occ.min?` a node computes (the least occupied clearing level in `[cleared+1, widthMinUpto
layer − 1]`) — the same `occ` `classify`/`conOracle` build, read off the node's profile ledger. -/
noncomputable def nodeOccMin (M : Fin (L + 1) → ℕ) (node : StepData M) : Option ℕ :=
  ((List.finRange node.numDiv).filterMap (fun k =>
    if node.cleared + 1 ≤ node.divTilde k ∧ node.divTilde k + 1 ≤ widthMinUpto M node.layer
    then some (node.divTilde k) else none)).min?

/-- **The per-NODE center dimension** `d_center` (per-node cover ruling): the case recomputed at the
StepData level. Rollover/terminal = `0`; case-2 = `resRows · resCols`; case-1 =
`1 + runLen · resCols`
(`runLen = target − cleared`, `target = occ.min?`). -/
noncomputable def dCenterOfNode (M : Fin (L + 1) → ℕ) (node : StepData M) : ℕ :=
  if L ≤ node.layer then 0
  else if widthMinUpto M (node.layer + 1) ≤ node.cleared then 0
  else (nodeOccMin M node).elim (node.resRows * node.resCols)
        (fun target => 1 + (target - node.cleared) * node.resCols)

/-- `nodeOccMin` on a `toStepData` node is (definitionally) the state's `occ.min?` — the bridge to
the `conOracle`/`classify` dispatch. -/
theorem nodeOccMin_toStepData (M : Fin (L + 1) → ℕ) (s : ConState L) (rr rc : ℕ) :
    nodeOccMin M (s.toStepData M rr rc) =
      ((List.finRange s.numDiv).filterMap (fun k =>
        if s.cleared + 1 ≤ s.divTilde k ∧ s.divTilde k + 1 ≤ widthMinUpto M s.layer
        then some (s.divTilde k) else none)).min? := rfl

/-- `dCenterOfNode` at a `toStepData` node, restated in `s`-level projections (all `rfl`). -/
theorem dCenterOfNode_toStepData_eq (M : Fin (L + 1) → ℕ) (s : ConState L) (rr rc : ℕ) :
    dCenterOfNode M (s.toStepData M rr rc) =
      (if L ≤ s.layer then 0
       else if widthMinUpto M (s.layer + 1) ≤ s.cleared then 0
       else ((List.finRange s.numDiv).filterMap (fun k =>
              if s.cleared + 1 ≤ s.divTilde k ∧ s.divTilde k + 1 ≤ widthMinUpto M s.layer
              then some (s.divTilde k) else none)).min?.elim (rr * rc)
              (fun target => 1 + (target - s.cleared) * rc)) := rfl

/-- `dCenterOfNode` at a rollover node (`= 0`). -/
theorem dCenterOfNode_rollover (M : Fin (L + 1) → ℕ) (s : ConState L) (rr rc : ℕ)
    (hlive : s.layer < L) (hex : widthMinUpto M (s.layer + 1) ≤ s.cleared) :
    dCenterOfNode M (s.toStepData M rr rc) = 0 := by
  rw [dCenterOfNode_toStepData_eq, if_neg (not_le.mpr hlive), if_pos hex]

/-- `dCenterOfNode` at a case-2 node (`occ.min? = none`) is the residual block `rr · rc`. -/
theorem dCenterOfNode_case2 (M : Fin (L + 1) → ℕ) (s : ConState L) (rr rc : ℕ)
    (hlive : s.layer < L) (hnex : ¬ widthMinUpto M (s.layer + 1) ≤ s.cleared)
    (hmin : ((List.finRange s.numDiv).filterMap (fun k =>
        if s.cleared + 1 ≤ s.divTilde k ∧ s.divTilde k + 1 ≤ widthMinUpto M s.layer
        then some (s.divTilde k) else none)).min? = none) :
    dCenterOfNode M (s.toStepData M rr rc) = rr * rc := by
  rw [dCenterOfNode_toStepData_eq, if_neg (not_le.mpr hlive), if_neg hnex, hmin]
  rfl

/-- `dCenterOfNode` at a case-1 node (`occ.min? = some target`) is `1 + (target − cleared) · rc`. -/
theorem dCenterOfNode_case1 (M : Fin (L + 1) → ℕ) (s : ConState L) (rr rc target : ℕ)
    (hlive : s.layer < L) (hnex : ¬ widthMinUpto M (s.layer + 1) ≤ s.cleared)
    (hmin : ((List.finRange s.numDiv).filterMap (fun k =>
        if s.cleared + 1 ≤ s.divTilde k ∧ s.divTilde k + 1 ≤ widthMinUpto M s.layer
        then some (s.divTilde k) else none)).min? = some target) :
    dCenterOfNode M (s.toStepData M rr rc) = 1 + (target - s.cleared) * rc := by
  rw [dCenterOfNode_toStepData_eq, if_neg (not_le.mpr hlive), if_neg hnex, hmin]
  rfl

/-! ## The REQUIRED sum property: `dCenterOfNode node = Σ_e dCenterOfEdge node e` -/

/-- **The edge-sum partition identity** (coverage's global-offset partition): every branch node of
the built tree has `Σ (edges).map (dCenterOfEdge node) = dCenterOfNode node`. Walk the `conOracle`
dispatch: rollover ⟹ `[0]`; case-2 ⟹ `[rr·rc]`; case-1 ⟹ `[1, runLen·rc]`. -/
theorem dCenterOfNode_edgeSum {M : Fin (L + 1) → ℕ} (s : ConState L)
    (node : StepData M) (edges : List (Edge M))
    (htree : buildTree M (conOracle M) s = ResolutionTree.branch node edges) :
    (edges.map (dCenterOfEdge node)).sum = dCenterOfNode M node := by
  by_cases h1 : L ≤ s.layer
  · -- terminal ⟹ leaf, contradicting `htree : … = branch …`
    have horacle : conOracle M s = oracleTerminal M s := by unfold conOracle; rw [dif_pos h1]
    rw [buildTree_terminal M (conOracle M) s (leafOfState M s) (leafOfState_rootLedger M s)
      horacle] at htree
    exact absurd htree (by simp)
  · have hlive : s.layer < L := not_le.mp h1
    have hL1 : s.layer + 1 < L + 1 := by omega
    by_cases h2 : widthMinUpto M (s.layer + 1) ≤ s.cleared
    · -- rollover: one chartless edge, `dCenterOfEdge = 0`
      have horacle : conOracle M s = rolloverDecision M s (le_of_lt hlive) h2 := by
        unfold conOracle; rw [dif_neg h1, dif_pos h2]
      rw [buildTree_step M (conOracle M) s _ _ horacle] at htree
      obtain ⟨rfl, rfl⟩ := ResolutionTree.branch.inj htree
      rw [dCenterOfNode_rollover M s 0 0 hlive h2]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rfl
    · have hlt : s.cleared < widthMinUpto M (s.layer + 1) := not_le.mp h2
      have hcap : s.cleared < layerCap M := lt_of_lt_of_le hlt (widthMinUpto_le_layerCap M _)
      rcases hmin : ((List.finRange s.numDiv).filterMap (fun k =>
          if s.cleared + 1 ≤ s.divTilde k ∧ s.divTilde k + 1 ≤ widthMinUpto M s.layer
          then some (s.divTilde k) else none)).min? with _ | target
      · -- case-2: one full-block edge, `dCenterOfEdge = resRows·resCols`
        have horacle : conOracle M s = case2Decision M s
            (widthMinUpto M s.layer - s.cleared) (M ⟨s.layer + 1, hL1⟩ - s.cleared) hcap := by
          unfold conOracle; rw [dif_neg h1, dif_neg h2]
          split <;> simp_all only [reduceCtorEq]
        rw [buildTree_step M (conOracle M) s _ _ horacle] at htree
        obtain ⟨rfl, rfl⟩ := ResolutionTree.branch.inj htree
        rw [dCenterOfNode_case2 M s _ _ hlive h2 hmin]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        rfl
      · -- case-1: `chooseMin` must succeed (else terminal ⟹ leaf); two edges `[1, runLen·rc]`
        rcases hf : chooseMin s target with _ | f
        · have horacle : conOracle M s = oracleTerminal M s := by
            unfold conOracle; rw [dif_neg h1, dif_neg h2]
            split <;> simp_all only [reduceCtorEq, Option.some.injEq]
            all_goals (try subst_vars)
            all_goals (try (split <;> simp_all only [reduceCtorEq]))
          rw [buildTree_terminal M (conOracle M) s (leafOfState M s)
            (leafOfState_rootLedger M s) horacle] at htree
          exact absurd htree (by simp)
        · have hgt : s.cleared < target := by
            obtain ⟨hmemtar, -⟩ := List.min?_eq_some_iff.mp hmin
            rw [List.mem_filterMap] at hmemtar
            obtain ⟨k0, -, hk0⟩ := hmemtar
            by_cases hc0 : s.cleared + 1 ≤ s.divTilde k0 ∧
                s.divTilde k0 + 1 ≤ widthMinUpto M s.layer
            · rw [if_pos hc0] at hk0
              have hdt : s.divTilde k0 = target := Option.some.inj hk0
              omega
            · rw [if_neg hc0] at hk0; exact absurd hk0 (by simp)
          have horacle : conOracle M s = case1Decision M s f (target - s.cleared)
              (widthMinUpto M s.layer - s.cleared) (M ⟨s.layer + 1, hL1⟩ - s.cleared)
              (not_le.mp h1) (by omega) (by rw [(chooseMin_spec s target hf).1]; omega) hcap := by
            unfold conOracle
            rw [dif_neg h1, dif_neg h2]
            split
            · rename_i target' heq
              obtain rfl : target' = target := Option.some.inj (heq ▸ hmin)
              split
              · rename_i f' hf'
                obtain rfl : f' = f := Option.some.inj (hf' ▸ hf)
                rfl
              · rename_i hf'
                exact absurd (hf' ▸ hf) (by simp)
            · rename_i heq
              exact absurd (heq ▸ hmin) (by simp)
          rw [buildTree_step M (conOracle M) s _ _ horacle] at htree
          obtain ⟨rfl, rfl⟩ := ResolutionTree.branch.inj htree
          rw [dCenterOfNode_case1 M s _ _ target hlive h2 hmin]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          rfl

/-! ## The totality bound: `dCenterOfNode node ≤ flatDim M` on-cone -/

/-- The residual block `(widthMinUpto layer − J)·(M⁽ˢ⁺¹⁾ − J)` fits inside the layer-`s` `flatDim`
term `M⁽ˢ⁾·M⁽ˢ⁺¹⁾ ≤ flatDim` (`resRows ≤ M⁽ˢ⁾`, `resCols ≤ M⁽ˢ⁺¹⁾`). -/
theorem block_le_flatDim {M : Fin (L + 1) → ℕ} (s : ConState L) (hlive : s.layer < L)
    (hL1 : s.layer + 1 < L + 1) :
    (widthMinUpto M s.layer - s.cleared) * (M ⟨s.layer + 1, hL1⟩ - s.cleared) ≤ flatDim M := by
  have hbridge : M (⟨s.layer + 1, hL1⟩ : Fin (L + 1)) = M ((⟨s.layer, hlive⟩ : Fin L).succ) := rfl
  have hrr : widthMinUpto M s.layer - s.cleared ≤ M ((⟨s.layer, hlive⟩ : Fin L).castSucc) :=
    le_trans (Nat.sub_le _ _) (widthMinUpto_le _ (by simp))
  have hrc : M (⟨s.layer + 1, hL1⟩ : Fin (L + 1)) - s.cleared
      ≤ M ((⟨s.layer, hlive⟩ : Fin L).succ) := by rw [hbridge]; exact Nat.sub_le _ _
  have hterm : M ((⟨s.layer, hlive⟩ : Fin L).castSucc) * M ((⟨s.layer, hlive⟩ : Fin L).succ)
      ≤ flatDim M := by
    rw [flatDim_eq]
    exact Finset.single_le_sum (f := fun j : Fin L => M j.castSucc * M j.succ)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ _)
  exact le_trans (Nat.mul_le_mul hrr hrc) hterm

/-- **The totality bound** (`hd` of `QNodeFam`): every branch node of the built tree has
`dCenterOfNode node ≤ flatDim M`. Arithmetic (no `DivBirthInv`): the case-2 block `rr·rc` and the
case-1 `1 + runLen·rc ≤ rr·rc` both fit inside the layer's term `M⁽ˢ⁾·M⁽ˢ⁺¹⁾ ≤ flatDim`. -/
theorem dCenterOfNode_le_flatDim {M : Fin (L + 1) → ℕ} (s : ConState L)
    (node : StepData M) (edges : List (Edge M))
    (htree : buildTree M (conOracle M) s = ResolutionTree.branch node edges) :
    dCenterOfNode M node ≤ flatDim M := by
  by_cases h1 : L ≤ s.layer
  · have horacle : conOracle M s = oracleTerminal M s := by unfold conOracle; rw [dif_pos h1]
    rw [buildTree_terminal M (conOracle M) s (leafOfState M s) (leafOfState_rootLedger M s)
      horacle] at htree
    exact absurd htree (by simp)
  · have hlive : s.layer < L := not_le.mp h1
    have hL1 : s.layer + 1 < L + 1 := by omega
    by_cases h2 : widthMinUpto M (s.layer + 1) ≤ s.cleared
    · have horacle : conOracle M s = rolloverDecision M s (le_of_lt hlive) h2 := by
        unfold conOracle; rw [dif_neg h1, dif_pos h2]
      rw [buildTree_step M (conOracle M) s _ _ horacle] at htree
      obtain ⟨rfl, rfl⟩ := ResolutionTree.branch.inj htree
      rw [dCenterOfNode_rollover M s 0 0 hlive h2]
      exact Nat.zero_le _
    · have hlt : s.cleared < widthMinUpto M (s.layer + 1) := not_le.mp h2
      have hcap : s.cleared < layerCap M := lt_of_lt_of_le hlt (widthMinUpto_le_layerCap M _)
      rcases hmin : ((List.finRange s.numDiv).filterMap (fun k =>
          if s.cleared + 1 ≤ s.divTilde k ∧ s.divTilde k + 1 ≤ widthMinUpto M s.layer
          then some (s.divTilde k) else none)).min? with _ | target
      · -- case-2
        have horacle : conOracle M s = case2Decision M s
            (widthMinUpto M s.layer - s.cleared) (M ⟨s.layer + 1, hL1⟩ - s.cleared) hcap := by
          unfold conOracle; rw [dif_neg h1, dif_neg h2]
          split <;> simp_all only [reduceCtorEq]
        rw [buildTree_step M (conOracle M) s _ _ horacle] at htree
        obtain ⟨rfl, rfl⟩ := ResolutionTree.branch.inj htree
        rw [dCenterOfNode_case2 M s _ _ hlive h2 hmin]
        exact block_le_flatDim s hlive hL1
      · -- case-1
        rcases hf : chooseMin s target with _ | f
        · have horacle : conOracle M s = oracleTerminal M s := by
            unfold conOracle; rw [dif_neg h1, dif_neg h2]
            split <;> simp_all only [reduceCtorEq, Option.some.injEq]
            all_goals (try subst_vars)
            all_goals (try (split <;> simp_all only [reduceCtorEq]))
          rw [buildTree_terminal M (conOracle M) s (leafOfState M s)
            (leafOfState_rootLedger M s) horacle] at htree
          exact absurd htree (by simp)
        · -- occ membership gives the target bounds
          obtain ⟨hmemtar, -⟩ := List.min?_eq_some_iff.mp hmin
          rw [List.mem_filterMap] at hmemtar
          obtain ⟨k0, -, hk0⟩ := hmemtar
          have htbounds : s.cleared + 1 ≤ target ∧ target + 1 ≤ widthMinUpto M s.layer := by
            by_cases hc0 : s.cleared + 1 ≤ s.divTilde k0 ∧
                s.divTilde k0 + 1 ≤ widthMinUpto M s.layer
            · rw [if_pos hc0] at hk0
              have hdt : s.divTilde k0 = target := Option.some.inj hk0
              rw [hdt] at hc0; exact hc0
            · rw [if_neg hc0] at hk0; exact absurd hk0 (by simp)
          obtain ⟨hlb, hub⟩ := htbounds
          have horacle : conOracle M s = case1Decision M s f (target - s.cleared)
              (widthMinUpto M s.layer - s.cleared) (M ⟨s.layer + 1, hL1⟩ - s.cleared)
              (not_le.mp h1) (by omega) (by rw [(chooseMin_spec s target hf).1]; omega) hcap := by
            unfold conOracle
            rw [dif_neg h1, dif_neg h2]
            split
            · rename_i target' heq
              obtain rfl : target' = target := Option.some.inj (heq ▸ hmin)
              split
              · rename_i f' hf'
                obtain rfl : f' = f := Option.some.inj (hf' ▸ hf)
                rfl
              · rename_i hf'
                exact absurd (hf' ▸ hf) (by simp)
            · rename_i heq
              exact absurd (heq ▸ hmin) (by simp)
          rw [buildTree_step M (conOracle M) s _ _ horacle] at htree
          obtain ⟨rfl, rfl⟩ := ResolutionTree.branch.inj htree
          rw [dCenterOfNode_case1 M s _ _ target hlive h2 hmin]
          refine le_trans ?_ (block_le_flatDim s hlive hL1)
          have hwle : widthMinUpto M (s.layer + 1) ≤ M (⟨s.layer + 1, hL1⟩ : Fin (L + 1)) :=
            widthMinUpto_le _ (by simp)
          have hrc1 : 1 ≤ M (⟨s.layer + 1, hL1⟩ : Fin (L + 1)) - s.cleared := by omega
          have hrun1 : target - s.cleared + 1 ≤ widthMinUpto M s.layer - s.cleared := by omega
          have hmul : (target - s.cleared + 1) * (M (⟨s.layer + 1, hL1⟩ : Fin (L + 1)) - s.cleared)
              ≤ (widthMinUpto M s.layer - s.cleared) *
                (M (⟨s.layer + 1, hL1⟩ : Fin (L + 1)) - s.cleared) := by gcongr
          have hexp : (target - s.cleared + 1) * (M (⟨s.layer + 1, hL1⟩ : Fin (L + 1)) - s.cleared)
              = (M (⟨s.layer + 1, hL1⟩ : Fin (L + 1)) - s.cleared)
                + (target - s.cleared) * (M (⟨s.layer + 1, hL1⟩ : Fin (L + 1)) - s.cleared) := by
            ring
          omega

/-! ## `cNodeOf` (the center selector) and `qNodeOf` -/

/-- **The Def-4 minimal chooser at the StepData level** (mirror of `chooseMin`): the merged divisor
`cNodeOf`'s `u`-corner reads. Definitionally `chooseMin s target` on a `toStepData` node. -/
def chooseMinData {M : Fin (L + 1) → ℕ} (node : StepData M) (target : ℕ) :
    Option (Fin node.numDiv) :=
  (List.finRange node.numDiv).find? (fun k => decide
    (node.divTilde k = target ∧
      ∀ k' : Fin node.numDiv, node.divTilde k' = target →
        ∀ j : Fin L, node.divProfile k j ≤ node.divProfile k' j))

/-- **The case-1(1) `u`-corner selector** (`Fin 1`): the merged divisor's (the recomputed Def-4 pick
`chooseMinData`) immutable birth corner `(a, b, b)` as a flat coord, with the `uCoordSel`-style
totality fallback (`Fin.castLE hd 0`) off the reachable cone (invalid corner / no chooser pick). -/
noncomputable def uCornerSel (M : Fin (L + 1) → ℕ) (node : StepData M) (target : ℕ)
    (hd : 1 ≤ flatDim M) : Fin 1 → Fin (flatDim M) := fun _ =>
  match chooseMinData node target with
  | some f =>
      let c := node.divBirthCoord f
      if hL : c.1 < L then
        if h2 : c.2 < M (⟨c.1, hL⟩ : Fin L).castSucc ∧ c.2 < M (⟨c.1, hL⟩ : Fin L).succ then
          flatCoordOf M ⟨c.1, hL⟩ ⟨c.2, h2.1⟩ ⟨c.2, h2.2⟩
        else Fin.castLE hd 0
      else Fin.castLE hd 0
  | none => Fin.castLE hd 0

/-- **The non-rollover center selector**, indexed by the node's `occ.min?`: `none` (case-2) = the
full residual block; `some target` (case-1) = the `u`-corner `++` the case-1(2) `d`-block
(`Fin.append`). The `Option`-indexed return type lets `realCNode` land it under `dCenterOfNode`'s
dispatch by defeq. -/
noncomputable def centerSelCase (M : Fin (L + 1) → ℕ) (node : StepData M) (occ : Option ℕ)
    (hd : occ.elim (node.resRows * node.resCols)
      (fun t => 1 + (t - node.cleared) * node.resCols) ≤ flatDim M) :
    Fin (occ.elim (node.resRows * node.resCols)
      (fun t => 1 + (t - node.cleared) * node.resCols)) → Fin (flatDim M) :=
  match occ with
  | none => resBlockOrFallback M node.layer node.cleared node.resRows node.resCols hd
  | some target =>
      Fin.append
        (uCornerSel M node target (by
          have hd' : 1 + (target - node.cleared) * node.resCols ≤ flatDim M := hd
          omega))
        (resBlockOrFallback M node.layer node.cleared (target - node.cleared) node.resCols (by
          have hd' : 1 + (target - node.cleared) * node.resCols ≤ flatDim M := hd
          omega))

/-! ## `dCenterOfNode` per-case reductions (for `realCNode` + its injectivity) -/

/-- `dCenterOfNode = 0` at a terminal node (`L ≤ layer`). -/
theorem dCenterOfNode_zero_terminal (M : Fin (L + 1) → ℕ) (node : StepData M)
    (h1 : L ≤ node.layer) : dCenterOfNode M node = 0 := by
  unfold dCenterOfNode; rw [if_pos h1]

/-- `dCenterOfNode = 0` at a rollover node (`¬ L ≤ layer`, `widthMinUpto (layer+1) ≤ cleared`). -/
theorem dCenterOfNode_zero_rollover (M : Fin (L + 1) → ℕ) (node : StepData M)
    (h1 : ¬ L ≤ node.layer) (h2 : widthMinUpto M (node.layer + 1) ≤ node.cleared) :
    dCenterOfNode M node = 0 := by
  unfold dCenterOfNode; rw [if_neg h1, if_pos h2]

/-- At a non-terminal node `dCenterOfNode` is the `occ`-indexed dimension `centerSelCase` uses. -/
theorem dCenterOfNode_nonterminal (M : Fin (L + 1) → ℕ) (node : StepData M)
    (h1 : ¬ L ≤ node.layer) (h2 : ¬ widthMinUpto M (node.layer + 1) ≤ node.cleared) :
    dCenterOfNode M node = (nodeOccMin M node).elim (node.resRows * node.resCols)
      (fun t => 1 + (t - node.cleared) * node.resCols) := by
  unfold dCenterOfNode; rw [if_neg h1, if_neg h2]

/-- **The intended per-node center selector** `realCNode` (fidelity): case-1 = the `u`-corner `++`
the case-1(2) `d`-block; case-2 = the residual block; terminal/rollover = the empty map (dim 0).
Defined POINTWISE (each branch outputs `Fin (flatDim M)`, the input index cast by `finCongr` through
`dCenterOfNode`'s per-case reduction) so injectivity is a clean `finCongr`-transfer — no dependent
`Eq.mpr` on the function type. -/
noncomputable def realCNode (M : Fin (L + 1) → ℕ) (node : StepData M)
    (hd : dCenterOfNode M node ≤ flatDim M) : Fin (dCenterOfNode M node) → Fin (flatDim M) :=
  fun i =>
    if h1 : L ≤ node.layer then
      absurd i.isLt (by have := dCenterOfNode_zero_terminal M node h1; omega)
    else if h2 : widthMinUpto M (node.layer + 1) ≤ node.cleared then
      absurd i.isLt (by have := dCenterOfNode_zero_rollover M node h1 h2; omega)
    else
      centerSelCase M node (nodeOccMin M node) (dCenterOfNode_nonterminal M node h1 h2 ▸ hd)
        (finCongr (dCenterOfNode_nonterminal M node h1 h2) i)

/-- **`realCNode` is injective from `centerSelCase`'s injectivity**: terminal/rollover have empty
domain (`dCenterOfNode = 0`, vacuous); the non-terminal branch is `centerSelCase ∘ finCongr`, so
injectivity transfers through `centerSelCase`'s (`hci`) and `finCongr`'s bijectivity. -/
theorem realCNode_injective (M : Fin (L + 1) → ℕ) (node : StepData M)
    (hd : dCenterOfNode M node ≤ flatDim M)
    (hci : ∀ hd', Function.Injective (centerSelCase M node (nodeOccMin M node) hd')) :
    Function.Injective (realCNode M node hd) := by
  intro a b hab
  simp only [realCNode] at hab
  split_ifs at hab with h1 h2
  · exact absurd a.isLt (by have := dCenterOfNode_zero_terminal M node h1; omega)
  · exact absurd a.isLt (by have := dCenterOfNode_zero_rollover M node h1 h2; omega)
  · exact (finCongr (dCenterOfNode_nonterminal M node h1 h2)).injective (hci _ hab)

/-! ## `centerSelCase` injectivity (the u-corner ∉ d-block geometry) -/

/-- **`flatCoordOf` is val-level injective across layers**: equal flat coords have equal `(s, i, j)`
values (the `FlatIdx` sigma constructor recovers the layer + both cells). The uniform fact behind
the `u`-corner ∉ `d`-block disjointness (same-layer AND cross-layer at once). -/
theorem flatCoordOf_val_inj {M : Fin (L + 1) → ℕ} {s s' : Fin L}
    {i : Fin (M s.castSucc)} {j : Fin (M s.succ)} {i' : Fin (M s'.castSucc)} {j' : Fin (M s'.succ)}
    (h : flatCoordOf M s i j = flatCoordOf M s' i' j') :
    (s : ℕ) = s' ∧ (i : ℕ) = i' ∧ (j : ℕ) = j' := by
  unfold flatCoordOf at h
  have hsig : (⟨⟨s, i⟩, j⟩ : FlatIdx M) = ⟨⟨s', i'⟩, j'⟩ :=
    (Fintype.equivFin (FlatIdx M)).injective h
  obtain ⟨hq, hj⟩ := Sigma.mk.inj_iff.mp hsig
  obtain ⟨hs, hi⟩ := Sigma.mk.inj_iff.mp hq
  have hss : (s : ℕ) = s' := congrArg Fin.val hs
  refine ⟨hss, ?_, ?_⟩
  · have hM : M s.castSucc = M s'.castSucc := congrArg (fun t : Fin L => M t.castSucc) hs
    simpa using (Fin.heq_ext_iff hM).mp hi
  · have hM : M s.succ = M s'.succ := congrArg (fun t : Fin L => M t.succ) hs
    simpa using (Fin.heq_ext_iff hM).mp hj

/-- **The `u`-corner is disjoint from the case-1(2) `d`-block** (the fidelity heart): the merged
divisor's birth corner `(a, b, b)` cannot equal a block cell `(layer, cleared+r, cleared+c)`.
By `flatCoordOf_val_inj` a coincidence forces `a = layer`, whence freshness gives `b < cleared`, but
the block row is `b = cleared + r ≥ cleared` — contradiction. -/
theorem uCornerSel_ne_resBlockOrFallback (M : Fin (L + 1) → ℕ) (node : StepData M) (target : ℕ)
    (f : Fin node.numDiv) (hf : chooseMinData node target = some f)
    (hLf : (node.divBirthCoord f).1 < L)
    (hrowf : (node.divBirthCoord f).2 < M (⟨(node.divBirthCoord f).1, hLf⟩ : Fin L).castSucc)
    (hcolf : (node.divBirthCoord f).2 < M (⟨(node.divBirthCoord f).1, hLf⟩ : Fin L).succ)
    (hfresh : (node.divBirthCoord f).1 = node.layer → (node.divBirthCoord f).2 < node.cleared)
    (hblk : ∃ hs : node.layer < L,
        node.cleared + (target - node.cleared) ≤ M (⟨node.layer, hs⟩ : Fin L).castSucc ∧
        node.cleared + node.resCols ≤ M (⟨node.layer, hs⟩ : Fin L).succ)
    (hd1 : 1 ≤ flatDim M) (hdb : (target - node.cleared) * node.resCols ≤ flatDim M)
    (i : Fin 1) (j : Fin ((target - node.cleared) * node.resCols)) :
    uCornerSel M node target hd1 i ≠
      resBlockOrFallback M node.layer node.cleared (target - node.cleared) node.resCols hdb j := by
  have hu : uCornerSel M node target hd1 i = flatCoordOf M ⟨(node.divBirthCoord f).1, hLf⟩
      ⟨(node.divBirthCoord f).2, hrowf⟩ ⟨(node.divBirthCoord f).2, hcolf⟩ := by
    simp only [uCornerSel, hf]
    rw [dif_pos hLf, dif_pos ⟨hrowf, hcolf⟩]
  have hr : resBlockOrFallback M node.layer node.cleared (target - node.cleared) node.resCols hdb j
      = flatCoordOf M ⟨node.layer, hblk.choose⟩
        ⟨node.cleared + (finProdFinEquiv.symm j).1, by
          have := (finProdFinEquiv.symm j).1.isLt; have := hblk.choose_spec.1; omega⟩
        ⟨node.cleared + (finProdFinEquiv.symm j).2, by
          have := (finProdFinEquiv.symm j).2.isLt; have := hblk.choose_spec.2; omega⟩ := by
    rw [resBlockOrFallback, dif_pos hblk, resBlockCenterIndices]
  rw [hu, hr]
  intro heq
  obtain ⟨ha, hb, -⟩ := flatCoordOf_val_inj heq
  have hfr : (node.divBirthCoord f).2 < node.cleared := hfresh ha
  have hb' : (node.divBirthCoord f).2 = node.cleared + (finProdFinEquiv.symm j).1 := hb
  omega

/-- **`centerSelCase` is injective** on-cone: case-2 = the injective residual block; case-1 =
`Fin.append` of the `u`-corner (`Fin 1`, trivially injective) and the injective `d`-block, with
disjoint ranges (`uCornerSel_ne_resBlockOrFallback`). The `some`-case hypotheses are the reachable
cone's corner-validity, freshness, block-fit, and chooser-success facts. -/
theorem centerSelCase_injective (M : Fin (L + 1) → ℕ) (node : StepData M) (occ : Option ℕ)
    (hd : occ.elim (node.resRows * node.resCols)
      (fun t => 1 + (t - node.cleared) * node.resCols) ≤ flatDim M)
    (H : ∀ target, occ = some target → ∃ f : Fin node.numDiv, chooseMinData node target = some f ∧
        ∃ hLf : (node.divBirthCoord f).1 < L,
          (node.divBirthCoord f).2 < M (⟨(node.divBirthCoord f).1, hLf⟩ : Fin L).castSucc ∧
          (node.divBirthCoord f).2 < M (⟨(node.divBirthCoord f).1, hLf⟩ : Fin L).succ ∧
          ((node.divBirthCoord f).1 = node.layer → (node.divBirthCoord f).2 < node.cleared) ∧
          ∃ hs : node.layer < L,
            node.cleared + (target - node.cleared) ≤ M (⟨node.layer, hs⟩ : Fin L).castSucc ∧
            node.cleared + node.resCols ≤ M (⟨node.layer, hs⟩ : Fin L).succ) :
    Function.Injective (centerSelCase M node occ hd) := by
  cases occ with
  | none =>
      exact resBlockOrFallback_injective M node.layer node.cleared node.resRows node.resCols hd
  | some target =>
      obtain ⟨f, hf, hLf, hrowf, hcolf, hfresh, hs, hbrow, hbcol⟩ := H target rfl
      show Function.Injective (Fin.append _ _)
      rw [Fin.append_injective_iff]
      refine ⟨fun a b _ => Subsingleton.elim a b,
        resBlockOrFallback_injective M node.layer node.cleared (target - node.cleared)
          node.resCols _,
        fun a b => ?_⟩
      exact uCornerSel_ne_resBlockOrFallback M node target f hf hLf hrowf hcolf hfresh
        ⟨hs, hbrow, hbcol⟩ _ _ a b

/-- **The center selector with a global injectivity fallback**: `realCNode` when it is injective
(the reachable cone — `realCNode_injective_of_divBirthInv`), else the canonical `Fin.castLE`. Total
and INJECTIVE for every node, so `qNodeOf` is always a well-formed `Homeomorph`. -/
noncomputable def cNodeOf (M : Fin (L + 1) → ℕ) (node : StepData M)
    (hd : dCenterOfNode M node ≤ flatDim M) : Fin (dCenterOfNode M node) → Fin (flatDim M) := by
  classical
  exact if Function.Injective (realCNode M node hd) then realCNode M node hd else Fin.castLE hd

/-- `cNodeOf` is injective for every node (the fallback guarantees it). -/
theorem cNodeOf_injective (M : Fin (L + 1) → ℕ) (node : StepData M)
    (hd : dCenterOfNode M node ≤ flatDim M) : Function.Injective (cNodeOf M node hd) := by
  classical
  unfold cNodeOf
  split
  · assumption
  · exact Fin.castLE_injective hd

/-- **`qNodeOf : QNodeFam M dCenterOfNode`** (coverage's per-node center-split family): the
`qOfCenter` split along the node's full center `cNodeOf`, on the reachable cone (`hd`). -/
noncomputable def qNodeOf (M : Fin (L + 1) → ℕ) (node : StepData M)
    (hd : dCenterOfNode M node ≤ flatDim M) :
    Params M ≃ₜ (Fin (dCenterOfNode M node) → ℝ) × (Fin (flatDim M - dCenterOfNode M node) → ℝ) :=
  qOfCenter M (cNodeOf M node hd) (cNodeOf_injective M node hd)

/-! ## Fidelity: on the reachable cone `cNodeOf = realCNode` (the intended coordinates) -/

/-- The per-`some`-target corner/block/chooser facts `centerSelCase_injective` needs — bundled so
the reachability supply (`DivBirthInv` validity/freshness + `OracleInv` chooser-totality + fit)
is a single hypothesis for coverage's tree walk. -/
def RealCNodeFacts (M : Fin (L + 1) → ℕ) (node : StepData M) : Prop :=
  ∀ target, nodeOccMin M node = some target → ∃ f : Fin node.numDiv,
    chooseMinData node target = some f ∧
    ∃ hLf : (node.divBirthCoord f).1 < L,
      (node.divBirthCoord f).2 < M (⟨(node.divBirthCoord f).1, hLf⟩ : Fin L).castSucc ∧
      (node.divBirthCoord f).2 < M (⟨(node.divBirthCoord f).1, hLf⟩ : Fin L).succ ∧
      ((node.divBirthCoord f).1 = node.layer → (node.divBirthCoord f).2 < node.cleared) ∧
      ∃ hs : node.layer < L,
        node.cleared + (target - node.cleared) ≤ M (⟨node.layer, hs⟩ : Fin L).castSucc ∧
        node.cleared + node.resCols ≤ M (⟨node.layer, hs⟩ : Fin L).succ

/-- **`realCNode` is injective given the on-cone facts** (`centerSelCase_injective` for every `hd'`,
fed into `realCNode_injective`). -/
theorem realCNode_injective_of_facts (M : Fin (L + 1) → ℕ) (node : StepData M)
    (hd : dCenterOfNode M node ≤ flatDim M) (H : RealCNodeFacts M node) :
    Function.Injective (realCNode M node hd) :=
  realCNode_injective M node hd (fun _ => centerSelCase_injective M node (nodeOccMin M node) _ H)

/-- **`cNodeOf = realCNode` on the reachable cone**: `realCNode` injective ⟹ the classical fallback
guard resolves to `realCNode`, so `cNodeOf` (hence `qNodeOf`) names the intended blow-up coords —
the fidelity of the per-node cover. -/
theorem cNodeOf_eq_realCNode (M : Fin (L + 1) → ℕ) (node : StepData M)
    (hd : dCenterOfNode M node ≤ flatDim M) (H : RealCNodeFacts M node) :
    cNodeOf M node hd = realCNode M node hd := by
  classical
  unfold cNodeOf
  rw [if_pos (realCNode_injective_of_facts M node hd H)]

/-! ## The q-det lemma: `qOfCenter` is linear (its fderiv is a fixed continuous linear equiv)

The blow-up chart conjugates by `qOfCenter` (`geoChartMap = q.symm ∘ (pivotChart × id) ∘ q`). For
the downstream fold-Jacobian induction the conjugation preserves `|det D|` — but ONLY because `q` is
LINEAR (`fderiv q = q`, then `det (q.symm ∘ A ∘ q) = det A`). `qOfCenter` is built from a CLE
(`paramsEquivFlatCLE`) and two linear reindexings (`piCongrLeft`, `sumArrowProdArrow`); this section
exposes it as a `ContinuousLinearEquiv` and records the `HasFDerivAt` (fwd + symm) the fold uses. -/

/-- **`qOfCenter` as a continuous linear equivalence** (its linearity, made explicit): the same
composition as `qOfCenter`, but through the `ContinuousLinearEquiv` of each piece — the CLE
`paramsEquivFlatCLE`, then the finite-dim reindexing `piCongrLeft (centerPerm)` and the regrouping
`sumArrowLequivProdArrow`. -/
noncomputable def qOfCenterCLE (M : Fin (L + 1) → ℕ) {d : ℕ} (c : Fin d → Fin (flatDim M))
    (hinj : Function.Injective c) :
    Params M ≃L[ℝ] (Fin d → ℝ) × (Fin (flatDim M - d) → ℝ) :=
  (paramsEquivFlatCLE M).trans
    (((LinearEquiv.piCongrLeft ℝ (fun _ : Fin d ⊕ Fin (flatDim M - d) => ℝ)
          (centerPerm M c hinj)).toContinuousLinearEquiv).trans
      ((LinearEquiv.sumArrowLequivProdArrow (Fin d) (Fin (flatDim M - d)) ℝ ℝ)
        |>.toContinuousLinearEquiv))

/-- `qOfCenter` and `qOfCenterCLE` are the same underlying map (the pieces share their `Equiv`s). -/
theorem qOfCenter_coe_cle (M : Fin (L + 1) → ℕ) {d : ℕ} (c : Fin d → Fin (flatDim M))
    (hinj : Function.Injective c) :
    ⇑(qOfCenter M c hinj) = ⇑(qOfCenterCLE M c hinj) := rfl

/-- **The q-det lemma (`HasFDerivAt` form)**: `qOfCenter` is Fréchet-differentiable with derivative
the fixed continuous linear equiv `qOfCenterCLE` — so conjugating by it preserves `|det D|` (the
fold's conjugation step). -/
theorem qOfCenter_hasFDerivAt (M : Fin (L + 1) → ℕ) {d : ℕ} (c : Fin d → Fin (flatDim M))
    (hinj : Function.Injective c) (x : Params M) :
    HasFDerivAt (qOfCenter M c hinj)
      ((qOfCenterCLE M c hinj : Params M →L[ℝ] (Fin d → ℝ) × (Fin (flatDim M - d) → ℝ))) x := by
  rw [qOfCenter_coe_cle]
  exact (qOfCenterCLE M c hinj).hasFDerivAt

/-- **The q-det lemma (`symm` form)**: `qOfCenter.symm` is Fréchet-differentiable with derivative
the fixed continuous linear equiv `qOfCenterCLE.symm` — the other half of the conjugation. -/
theorem qOfCenter_symm_hasFDerivAt (M : Fin (L + 1) → ℕ) {d : ℕ} (c : Fin d → Fin (flatDim M))
    (hinj : Function.Injective c) (y : (Fin d → ℝ) × (Fin (flatDim M - d) → ℝ)) :
    HasFDerivAt (qOfCenter M c hinj).symm
      ((qOfCenterCLE M c hinj).symm :
        (Fin d → ℝ) × (Fin (flatDim M - d) → ℝ) →L[ℝ] Params M) y := by
  have hsymm : ⇑(qOfCenter M c hinj).symm = ⇑(qOfCenterCLE M c hinj).symm := rfl
  rw [hsymm]
  exact (qOfCenterCLE M c hinj).symm.hasFDerivAt

end DLNFibre.DLN.RLCT.Engine
