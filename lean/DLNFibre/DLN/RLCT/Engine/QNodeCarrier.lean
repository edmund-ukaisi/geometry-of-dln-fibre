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
`qNodeOf` is a well-formed `Homeomorph` for every node; the ON-CONE fidelity (that the fallback
is not taken — the intended selector IS injective under `DivBirthInv`) is
`realCNode_injective_of_divBirthInv`.
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

/-- **The intended per-node center selector** `realCNode` (fidelity): case-1 = the `u`-corner `++`
the case-1(2) `d`-block; case-2 = the residual block; rollover/off-cone = the canonical injection.
Total via the inner selectors' fallbacks; dispatches on `dCenterOfNode`'s structure so the dependent
`Fin (dCenterOfNode …)` type reduces per branch. -/
noncomputable def realCNode (M : Fin (L + 1) → ℕ) (node : StepData M)
    (hd : dCenterOfNode M node ≤ flatDim M) : Fin (dCenterOfNode M node) → Fin (flatDim M) := by
  unfold dCenterOfNode at hd ⊢
  split_ifs at hd ⊢ with h1 h2
  · exact Fin.castLE (Nat.zero_le _)
  · exact Fin.castLE (Nat.zero_le _)
  · exact centerSelCase M node (nodeOccMin M node) hd

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

end DLNFibre.DLN.RLCT.Engine
