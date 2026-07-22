import DLNFibre.DLN.Aoyagi.MonumentAtlas
import DLNFibre.Core.Aoyagi.BlockBlowup
import DLNFibre.DLN.RLCT.Engine.DivBirthReach

/-!
# `DLN.Aoyagi.PivotPreservation` — M4: the (★) pivot-preservation core

The producer-side of L5's Jacobian-collapse clause (`FoldRealizes` third conjunct): each step's
pivot coordinate is preserved by all deeper steps, so the per-step Jacobian monomials evaluate at the
same source pivot value and telescope to `jacWeight (jac c)` with unit ≡ 1 (`chart_of_collapse`
consumes the collapse; this file produces the (★) it rests on). Route R2 (bridge-free): worked on
`canonCenterOf`/`cornerToFlat`/`divBirthCoord` directly (the `tupIdxEquiv` encoding), NOT the engine
`flatCoordOf` machinery.

Atom family (L5FoldSpec §E, M4):
* **A1** `blockBlowupMap` fixes the pivot and fixes off-center coordinates (raw def facts).
* **A2** `canonCenterOf` disjointness: an earlier divisor's birth corner is fixed by a deeper step's
  block blow-up — it is either the deeper pivot (fixed) or off the deeper center (fixed); a NON-pivot
  center membership is excluded by `DivBirthInv` clause-3 freshness (`a = layer → b < cleared`).
* A3 `DivBirthInv` along a real branch + `divBirthCoord` persistence (supplies A2's freshness).
* A4 clause-III shear extraction at an earlier corner (via A3).
* A5 the branch-level (★) glue over the path suffix (foldG frame), for L5's collapse (§D.3).
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi.PivotPres

variable {N : ℕ}

/-! ## A1 — raw `blockBlowupMap` fixed-coordinate atoms -/

/-- **A1a** — the block blow-up fixes its pivot coordinate (`= w p`, def's first branch). -/
theorem blockBlowupMap_apply_pivot {D : ℕ} (S : Finset (Fin D)) (p : Fin D) (w : Fin D → ℝ) :
    blockBlowupMap S p w p = w p := by
  simp [blockBlowupMap]

/-- **A1b** — the block blow-up fixes every coordinate off its center (`c₀ ∉ S ⟹ = w c₀`); holds even
if `c₀ = p` (then both sides are `w p`). -/
theorem blockBlowupMap_fixes_offCenter {D : ℕ} (S : Finset (Fin D)) (p : Fin D) (w : Fin D → ℝ)
    (c₀ : Fin D) (h : c₀ ∉ S) : blockBlowupMap S p w c₀ = w c₀ := by
  unfold blockBlowupMap
  split_ifs with h1
  · exact congrArg w h1.symm
  · rfl

/-- **A1 (the fixed-point criterion)** — `blockBlowupMap S p` fixes `c₀` whenever `c₀` is the pivot or
lies off the center. This is exactly the shape the (★) blow-up half needs: a deeper step fixes an
earlier pivot corner because that corner is the deeper pivot (case-1 re-pivot) or off the deeper
center (A2). -/
theorem blockBlowupMap_fixes_of_pivot_or_offCenter {D : ℕ} (S : Finset (Fin D)) (p : Fin D)
    (w : Fin D → ℝ) (c₀ : Fin D) (h : c₀ = p ∨ c₀ ∉ S) :
    blockBlowupMap S p w c₀ = w c₀ := by
  rcases h with h | h
  · subst h; exact blockBlowupMap_apply_pivot S c₀ w
  · exact blockBlowupMap_fixes_offCenter S p w c₀ h

/-! ## A2 — the `canonCenterOf` disjointness (freshness ⟹ earlier corner off the width-block) -/

/-- **A2 (width-block disjointness)** — an earlier divisor's diagonal birth corner
`cornerToFlat d a b` is NOT in the `widthMinUpto` block filter that `canonCenterOf` uses for
`case2`/`case12`, PROVIDED the `DivBirthInv` clause-3 freshness `a = s.layer → b < s.cleared` holds.
Pure `omega` on the filter predicate after collapsing the `image` by `tupIdxEquiv` injectivity: the
corner's `(layer, col) = (a, b)`, and the block demands `a = layer ∧ cleared ≤ b`, contradicting
freshness (`b < cleared`) when `a = layer`, and failing `q.1.1 = layer` when `a ≠ layer`. -/
theorem cornerToFlat_notMem_widthBlock {d : Fin (N + 1) → ℕ} (s : ConState N) (a b : ℕ)
    (i : Fin (flatDim d)) (hfresh : a = s.layer → b < s.cleared)
    (hcf : cornerToFlat d a b = some i) :
    i ∉ (Finset.univ.filter (fun q : tupIdx d =>
        (q.1.1 : ℕ) = s.layer ∧ s.cleared ≤ (q.1.2 : ℕ) ∧ s.cleared ≤ (q.2 : ℕ) ∧
          (q.2 : ℕ) < widthMinUpto d s.layer)).image (tupIdxEquiv d) := by
  -- Recover the corner tuple from `cornerToFlat`.
  simp only [cornerToFlat] at hcf
  split_ifs at hcf with hS hr hc
  -- hcf : some (tupIdxEquiv d ⟨⟨⟨a, hS⟩, ⟨b, hr⟩⟩, ⟨b, hc⟩⟩) = some i
  obtain rfl : tupIdxEquiv d ⟨⟨⟨a, hS⟩, ⟨b, hr⟩⟩, ⟨b, hc⟩⟩ = i := Option.some.injEq _ _ ▸ hcf
  intro hmem
  rw [Finset.mem_image] at hmem
  obtain ⟨q, hq, hqi⟩ := hmem
  rw [Finset.mem_filter] at hq
  -- `tupIdxEquiv` injective: `q = ⟨⟨⟨a,_⟩,⟨b,_⟩⟩,⟨b,_⟩⟩`.
  obtain rfl : q = ⟨⟨⟨a, hS⟩, ⟨b, hr⟩⟩, ⟨b, hc⟩⟩ := (tupIdxEquiv d).injective hqi
  obtain ⟨_, hP1, hP2, hP3, hP4⟩ := hq
  simp only at hP1 hP2 hP3 hP4
  -- hP1 : a = s.layer,  hP3 : s.cleared ≤ b,  freshness contradicts.
  omega

/-- **A2 (row-block disjointness)** — the `case11` row-block analog: the same freshness `omega`
excludes the earlier corner from the `[cleared, cleared+runLen)` row-block that `canonCenterOf(case11)`
adjoins to the reused pivot. -/
theorem cornerToFlat_notMem_rowBlock {d : Fin (N + 1) → ℕ} (s : ConState N) (runLen a b : ℕ)
    (i : Fin (flatDim d)) (hfresh : a = s.layer → b < s.cleared)
    (hcf : cornerToFlat d a b = some i) :
    i ∉ (Finset.univ.filter (fun q : tupIdx d =>
        (q.1.1 : ℕ) = s.layer ∧ s.cleared ≤ (q.1.2 : ℕ) ∧ s.cleared ≤ (q.2 : ℕ) ∧
          (q.2 : ℕ) < s.cleared + runLen)).image (tupIdxEquiv d) := by
  simp only [cornerToFlat] at hcf
  split_ifs at hcf with hS hr hc
  obtain rfl : tupIdxEquiv d ⟨⟨⟨a, hS⟩, ⟨b, hr⟩⟩, ⟨b, hc⟩⟩ = i := Option.some.injEq _ _ ▸ hcf
  intro hmem
  rw [Finset.mem_image] at hmem
  obtain ⟨q, hq, hqi⟩ := hmem
  rw [Finset.mem_filter] at hq
  obtain rfl : q = ⟨⟨⟨a, hS⟩, ⟨b, hr⟩⟩, ⟨b, hc⟩⟩ := (tupIdxEquiv d).injective hqi
  obtain ⟨_, hP1, hP2, hP3, hP4⟩ := hq
  simp only at hP1 hP2 hP3 hP4
  omega

/-! ## A3 — `DivBirthInv` holds along a real branch (supplies A2's freshness) -/

/-- **A3** — every node of a real branch carries `DivBirthInv` (TreePath induction off
`DivBirthInv_conRoot` + `DivBirthInv_conOracle_stepChildren`; a step's `conState` is its recorded
`nextState = sc.child`). Gives, at each deeper node, the clause-3 freshness A2 consumes for the
earlier (persisted, immutable) birth corner. -/
theorem divBirthInv_of_isRealBranch {d : Fin (N + 1) → ℕ}
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) :
    ∀ p : TreePath d, p.IsRealBranch e → DivBirthInv d p.conState := by
  intro p
  induction p with
  | root => intro _; exact DivBirthInv_conRoot
  | step p center pivot cse nextState shearφ ih =>
    intro hbranch
    obtain ⟨hrec, ⟨sc, hsc_mem, _hecase, hchild, _hcenter, _hpiv⟩, _hshear⟩ := hbranch
    have hp : DivBirthInv d p.conState := ih hrec
    have hchildInv := DivBirthInv_conOracle_stepChildren p.conState hp sc hsc_mem
    show DivBirthInv d nextState
    exact hchild ▸ hchildInv

/-! ## A2-package — `canonCenterOf` is disjoint from an earlier corner, or that corner is the pivot -/

/-- **A2-package** — for any step child `sc`, an earlier divisor's birth corner `i = cornerToFlat d a b`
is EITHER off `canonCenterOf d s sc` OR is the canonical pivot, given clause-3 freshness. The
`sc.ecase` case-split: `case2`/`case12` use the width-block disjointness (never the pivot); `case11`
either `i` is the reused pivot (right) or off both the pivot slot and the row-block (left); `rollover`
has empty center. Fed to A1's criterion, this makes a deeper block blow-up FIX the earlier corner. -/
theorem canonCenterOf_disjoint_or_pivot {d : Fin (N + 1) → ℕ} (s : ConState N) (sc : StepChild d s)
    (a b : ℕ) (i : Fin (flatDim d)) (hfresh : a = s.layer → b < s.cleared)
    (hcf : cornerToFlat d a b = some i) :
    i ∉ canonCenterOf d s sc ∨ canonPivotOf d s sc = some i := by
  by_cases hpiv : canonPivotOf d s sc = some i
  · exact Or.inr hpiv
  · refine Or.inl ?_
    rcases hc : sc.ecase with _ | _ | _ | _ <;> simp only [canonCenterOf, hc]
    · -- case11: (canonPivotOf).toFinset ∪ row-block
      rw [Finset.mem_union, not_or]
      refine ⟨fun hmem => hpiv ?_, cornerToFlat_notMem_rowBlock s _ a b i hfresh hcf⟩
      rwa [Option.mem_toFinset, Option.mem_def] at hmem
    · exact cornerToFlat_notMem_widthBlock s a b i hfresh hcf
    · exact cornerToFlat_notMem_widthBlock s a b i hfresh hcf
    · simp

/-! ## A4 (shear half) — a real-branch step's edgeShear fixes an earlier ledger birth-corner

Route (predecessor-registered): (iii) `blockShear φ` fixes `i` iff `φ · i = 0`; (ii) at a real-branch
step node, `ShearWithinCarveRaw` clause (III) gives that vanishing on every birth-corner of the node's
(child) ledger, UNCONDITIONALLY once `foldRegion = univ` collapses the `∀ u ∈ V` guard; (i) the
persistence that carries an EARLIER pivot corner into the deeper node's ledger is the
`divBirthCoord_persists*` family below. -/

/-- `blockShear φ` fixes coordinate `i` where the displacement vanishes (`u ↦ u + φ u`). -/
theorem blockShear_fixes_of_displacement_zero {D : ℕ}
    (φ : (Fin D → ℝ) → (Fin D → ℝ)) (v : Fin D → ℝ) (i : Fin D) (h : φ v i = 0) :
    blockShear φ v i = v i := by
  simp [blockShear, h]

/-- `edgeShearRaw` fixes coordinate `i` where the displacement vanishes: `id` fixes everything
(case11/rollover); `blockShear φ` fixes `i` via the previous atom (case12/case2). -/
theorem edgeShearRaw_fixes_of_displacement_zero {d : Fin (N + 1) → ℕ}
    (cse : StepCase) (φ : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ))
    (v : Fin (flatDim d) → ℝ) (i : Fin (flatDim d)) (h : φ v i = 0) :
    edgeShearRaw d cse φ v i = v i := by
  unfold edgeShearRaw
  split <;> first | rfl | exact blockShear_fixes_of_displacement_zero φ v i h

/-- Clause (III), extracted UNCONDITIONALLY: at a node carrying `ShearWithinCarveRaw`, the step's own
displacement `φ` vanishes on every birth-corner of the node's ledger, at EVERY point (region = univ). -/
theorem shearφ_zero_of_ledgerCorner {d : Fin (N + 1) → ℕ}
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (node : TreePath d)
    (φ : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ)) (hwc : ShearWithinCarveRaw d e node φ)
    (k : Fin node.conState.numDiv) (i : Fin (flatDim d))
    (hcf : cornerToFlat d (node.conState.divBirthCoord k).1 (node.conState.divBirthCoord k).2
      = some i) (u : Fin (flatDim d) → ℝ) :
    φ u i = 0 :=
  hwc.2.2 k i hcf u (by rw [foldRegion_eq_univ]; exact Set.mem_univ u)

/-- **A4 (shear half, single step)** — at a real-branch step node, the step's `edgeShearRaw` FIXES
every birth-corner `i` of the node's ledger (`id` at case11/rollover; `blockShear φ` via clause III). -/
theorem edgeShearRaw_fixes_ledgerCorner {d : Fin (N + 1) → ℕ}
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (node : TreePath d) (cse : StepCase)
    (φ : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ)) (hwc : ShearWithinCarveRaw d e node φ)
    (k : Fin node.conState.numDiv) (i : Fin (flatDim d))
    (hcf : cornerToFlat d (node.conState.divBirthCoord k).1 (node.conState.divBirthCoord k).2
      = some i) (u : Fin (flatDim d) → ℝ) :
    edgeShearRaw d cse φ u i = u i :=
  edgeShearRaw_fixes_of_displacement_zero cse φ u i
    (shearφ_zero_of_ledgerCorner e node φ hwc k i hcf u)

/-! ## A4 (i) — birth-corner PERSISTENCE: an earlier ledger entry survives every deeper step

Extracted from the mechanism inside `DivBirthInv_conOracle_stepChildren`: case2/case12 births grow the
ledger by `Fin.snoc` (the parent entries ride at `Fin.castSucc`), case11/rollover carry it verbatim. So
every entry of a state persists — SAME birth corner — to every oracle step-child, hence (folded along a
branch) to every deeper node. This supplies A2's freshness target and A4's ledger-membership at the
deeper node for an EARLIER pivot corner. -/

/-- Case-1(1) merge carries the ledger verbatim: every entry persists at the same index. -/
theorem divBirthCoord_persists_stepCase11 {L : ℕ} (s : ConState L) (i : Fin s.numDiv)
    (k : Fin s.numDiv) :
    ∃ k' : Fin (s.stepCase11 i).numDiv, (s.stepCase11 i).divBirthCoord k' = s.divBirthCoord k :=
  ⟨k, rfl⟩

/-- Rollover carries the ledger verbatim: every entry persists at the same index. -/
theorem divBirthCoord_persists_stepRollover {L : ℕ} (s : ConState L) (k : Fin s.numDiv) :
    ∃ k' : Fin s.stepRollover.numDiv, s.stepRollover.divBirthCoord k' = s.divBirthCoord k :=
  ⟨k, rfl⟩

/-- Case-1(2)/case-2 birth `Fin.snoc`s a fresh corner: every parent entry persists at `Fin.castSucc`. -/
theorem divBirthCoord_persists_stepAppendAdvance {L : ℕ} (s : ConState L) (e : ℕ) (t₀ : Fin L → ℕ)
    (k : Fin s.numDiv) :
    ∃ k' : Fin (s.stepAppendAdvance e t₀).numDiv,
      (s.stepAppendAdvance e t₀).divBirthCoord k' = s.divBirthCoord k :=
  ⟨k.castSucc, by simp [ConState.stepAppendAdvance]⟩

/-- **Birth-corner persistence through one oracle step** — mirrors
`DivBirthInv_conOracle_stepChildren` (same dispatch), swapping the conclusion: every ledger entry of
`s` persists (same birth corner) to any step-child `c.child`. Case-2/case-12 append (`Fin.snoc`,
parent entry at `castSucc`); case-11 and rollover carry verbatim; terminal branches have no
children. -/
theorem divBirthCoord_persists_conOracle {L : ℕ} {M : Fin (L + 1) → ℕ} (s : ConState L)
    (c : StepChild M s) (hc : c ∈ (conOracle M s).stepChildren) (k : Fin s.numDiv) :
    ∃ k' : Fin c.child.numDiv, c.child.divBirthCoord k' = s.divBirthCoord k := by
  by_cases h1 : L ≤ s.layer
  · have horacle : conOracle M s = oracleTerminal M s := by unfold conOracle; rw [dif_pos h1]
    rw [horacle] at hc
    simp only [oracleTerminal, ConDecision.stepChildren, List.not_mem_nil] at hc
  · have hlive : s.layer < L := not_le.mp h1
    by_cases h2 : widthMinUpto M (s.layer + 1) ≤ s.cleared
    · have horacle : conOracle M s = rolloverDecision M s (le_of_lt (not_le.mp h1)) h2 := by
        unfold conOracle; rw [dif_neg h1, dif_pos h2]
      rw [horacle] at hc
      simp only [rolloverDecision, ConDecision.stepChildren, List.mem_singleton] at hc
      subst hc
      exact divBirthCoord_persists_stepRollover s k
    · have hlt : s.cleared < widthMinUpto M (s.layer + 1) := not_le.mp h2
      have hcap : s.cleared < layerCap M := lt_of_lt_of_le hlt (widthMinUpto_le_layerCap M _)
      rcases hmin : ((List.finRange s.numDiv).filterMap (fun k =>
          if s.cleared + 1 ≤ s.divTilde k ∧ s.divTilde k + 1 ≤ widthMinUpto M s.layer
          then some (s.divTilde k) else none)).min? with _ | target
      · -- case-2
        have horacle : conOracle M s = case2Decision M s
            (widthMinUpto M s.layer - s.cleared) (M ⟨s.layer + 1, by omega⟩ - s.cleared) hcap := by
          unfold conOracle; rw [dif_neg h1, dif_neg h2]
          split <;> simp_all only [reduceCtorEq]
        rw [horacle] at hc
        simp only [case2Decision, ConDecision.stepChildren, List.mem_singleton] at hc
        subst hc
        exact divBirthCoord_persists_stepAppendAdvance s _ _ k
      · rcases hf : chooseMin s target with _ | f
        · have horacle : conOracle M s = oracleTerminal M s := by
            unfold conOracle; rw [dif_neg h1, dif_neg h2]
            split <;> simp_all only [reduceCtorEq, Option.some.injEq]
            all_goals (try subst_vars)
            all_goals (try (split <;> simp_all only [reduceCtorEq]))
          rw [horacle] at hc
          simp only [oracleTerminal, ConDecision.stepChildren, List.not_mem_nil] at hc
        · -- case-1 (two children: stepCase11, then stepAppendAdvance)
          have hgt : s.cleared < target := by
            obtain ⟨hmemtar, -⟩ := List.min?_eq_some_iff'.mp hmin
            rw [List.mem_filterMap] at hmemtar
            obtain ⟨k0, -, hk0⟩ := hmemtar
            by_cases hc0 : s.cleared + 1 ≤ s.divTilde k0 ∧
                s.divTilde k0 + 1 ≤ widthMinUpto M s.layer
            · rw [if_pos hc0] at hk0
              have hdt : s.divTilde k0 = target := Option.some.inj hk0
              omega
            · rw [if_neg hc0] at hk0; exact absurd hk0 (by simp)
          have horacle : conOracle M s = case1Decision M s f (target - s.cleared)
              (widthMinUpto M s.layer - s.cleared) (M ⟨s.layer + 1, by omega⟩ - s.cleared)
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
          rw [horacle] at hc
          simp only [case1Decision, ConDecision.stepChildren, List.mem_cons,
            List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · exact ⟨k, rfl⟩
          · exact divBirthCoord_persists_stepAppendAdvance s _ _ k

/-! ## A4/A5 substrate — `IsLedgerCorner`, persistence along a real branch, the single-step (★) -/

/-- `c₀` is a birth-corner of state `s`'s ledger: some divisor's immutable birth corner decodes (via
`cornerToFlat`) to the flat coordinate `c₀`. Read by A2's freshness and A4's clause-(III). -/
def IsLedgerCorner {N : ℕ} (d : Fin (N + 1) → ℕ) (s : ConState N) (c₀ : Fin (flatDim d)) : Prop :=
  ∃ k : Fin s.numDiv, cornerToFlat d (s.divBirthCoord k).1 (s.divBirthCoord k).2 = some c₀

/-- **Persistence along one real-branch step**: a ledger corner of the PARENT state `R.conState` is
a ledger corner of the CHILD state `ns` (the `nextState`), via `divBirthCoord_persists_conOracle` on
the oracle step child the `IsRealBranch` `∃sc` conjunct supplies. -/
theorem isLedgerCorner_persists_step {d : Fin (N + 1) → ℕ}
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (R : TreePath d)
    (c : Finset (Fin (flatDim d))) (piv : Fin (flatDim d)) (cse : StepCase) (ns : ConState N)
    (φ : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ))
    (hQ : (TreePath.step R c piv cse ns φ).IsRealBranch e)
    (c₀ : Fin (flatDim d)) (hc0 : IsLedgerCorner d R.conState c₀) :
    IsLedgerCorner d ns c₀ := by
  obtain ⟨_, ⟨sc, hsc_mem, _, hchild, _, _⟩, _⟩ := hQ
  subst hchild
  obtain ⟨k, hk⟩ := hc0
  obtain ⟨k', hk'⟩ := divBirthCoord_persists_conOracle R.conState sc hsc_mem k
  exact ⟨k', by rw [hk']; exact hk⟩

/-- **A5 single-step (★)** — a real-branch step's `stepMapRaw` FIXES every ledger birth-corner `c₀`
of its PARENT state `R.conState`. Blow-up OUTERMOST (`stepMapRaw = blockBlowupMap ∘ edgeShearRaw`):
the blow-up half is `canonCenterOf_disjoint_or_pivot` (A2-package, with the parent-`DivBirthInv`
freshness from A3) fed to A1's fixed-point criterion; the shear half is
`edgeShearRaw_fixes_ledgerCorner` (A4, with the corner PERSISTED into the child state `ns`). -/
theorem stepMapRaw_fixes_parentLedgerCorner {d : Fin (N + 1) → ℕ}
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (R : TreePath d)
    (c : Finset (Fin (flatDim d))) (piv : Fin (flatDim d)) (cse : StepCase) (ns : ConState N)
    (φ : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ))
    (hQ : (TreePath.step R c piv cse ns φ).IsRealBranch e)
    (c₀ : Fin (flatDim d)) (hc0 : IsLedgerCorner d R.conState c₀) (w : Fin (flatDim d) → ℝ) :
    stepMapRaw d cse c piv φ w c₀ = w c₀ := by
  obtain ⟨hR, ⟨sc, hsc_mem, _, hchild, hcenter, hpiv⟩, hwc⟩ := hQ
  subst hchild
  obtain ⟨k, hk⟩ := hc0
  obtain ⟨_, _, hfresh, _⟩ := divBirthInv_of_isRealBranch e R hR
  -- blow-up half: `c₀ = piv` or `c₀ ∉ c` (= the pinned canonCenterOf).
  have hblow : c₀ = piv ∨ c₀ ∉ c := by
    rcases canonCenterOf_disjoint_or_pivot R.conState sc (R.conState.divBirthCoord k).1
        (R.conState.divBirthCoord k).2 c₀ (hfresh k) hk with hoff | hpivot
    · right; rw [hcenter]; exact hoff
    · left; exact hpiv c₀ hpivot
  -- shear half: `c₀` persists into the child ledger, so clause (III) fixes it.
  have hshear : edgeShearRaw d cse φ w c₀ = w c₀ := by
    obtain ⟨k', hk'⟩ := divBirthCoord_persists_conOracle R.conState sc hsc_mem k
    refine edgeShearRaw_fixes_ledgerCorner e (TreePath.step R c piv cse sc.child φ) cse φ hwc
      k' c₀ ?_ w
    change cornerToFlat d (sc.child.divBirthCoord k').1 (sc.child.divBirthCoord k').2 = some c₀
    rw [hk']; exact hk
  change blockBlowupMap c piv (edgeShearRaw d cse φ w) c₀ = w c₀
  rw [blockBlowupMap_fixes_of_pivot_or_offCenter c piv (edgeShearRaw d cse φ w) c₀ hblow, hshear]

/-- **`pathMap` fixes a coordinate if every step in the list does** — list induction (`pathMap [] =
id`; the cons step composes a fixing head with a fixing tail). The glue that lifts the single-step
(★) to the composed deeper suffix. -/
theorem pathMap_fixes {D : ℕ} (c₀ : Fin D) :
    ∀ (l : List ((Fin D → ℝ) → (Fin D → ℝ))),
      (∀ σ ∈ l, ∀ w, σ w c₀ = w c₀) → ∀ u, pathMap l u c₀ = u c₀ := by
  intro l
  induction l with
  | nil => intro _ u; rfl
  | cons σ rest ih =>
    intro hl u
    have hσ := hl σ List.mem_cons_self
    have hrest : ∀ τ ∈ rest, ∀ w, τ w c₀ = w c₀ := fun τ hτ => hl τ (List.mem_cons_of_mem σ hτ)
    change σ (pathMap rest u) c₀ = u c₀
    rw [hσ (pathMap rest u), ih hrest u]

end DLNFibre.DLN.Aoyagi.PivotPres
