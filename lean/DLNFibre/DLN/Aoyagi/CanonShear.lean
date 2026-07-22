import DLNFibre.DLN.Aoyagi.MonumentAtlas
import DLNFibre.DLN.Aoyagi.PivotPreservation

/-!
# `DLN.Aoyagi.CanonShear` — the canonical Q/Schur step shear + within-carve emission (SEAT-L4, M7)

The per-step Schur shear `canonShearOf` a case12/case2 edge emits, and the proof that it satisfies
`ShearWithinCarveRaw`'s three clauses (I write-zero on layers ≥ sl / II reads ignore those layers /
III vanishes on ledger birth-corners). Design (SPECIFY, seat-L4 determination battery + elder): the
shear is **Schur-within-carve** — the displacement acts ONLY within the layer-`s.layer` carve block
INTERIOR (row, col > `s.cleared`), writing the Schur cross-term `−γ·β` (`γ` = the pivot-column tail,
`β` = the pivot-row tail), and is IDENTITY (displacement `0`) on every other coordinate. For a
case12/case2 edge the child sits at `cleared ≥ 1` so `sl = supportLayerOf = s.layer + 1`, and the
carve is layer `s.layer < sl` — hence (I)/(II) hold (write/read on layer `s.layer` only, below the
threshold) and (III) holds because the Schur writes the strict interior `(>J, >J)`, never a diagonal
corner (`= clause3_corner_check.py` A1-A4).

`canonShearOf` is the RAW displacement `shearφ` (the edge stores `blockShear (canonShearOf …)`;
`ShearWithinCarveRaw`/`IsRealBranch` read the raw displacement). At a case11/rollover edge the shear is
`id` (displacement `0`), trivially within-carve — this file is the case12/case2 emitter.
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- The flat coordinate of the layer-`S` block entry at `(row, col)` — general (`cornerToFlat` is the
diagonal `(J,J)` special case). `none` off-cone. Used to read the pivot-row/col tails `β`/`γ`. -/
noncomputable def blockEntryFlat (d : Fin (N + 1) → ℕ) (S row col : ℕ) : Option (Fin (flatDim d)) :=
  if hS : S < N then
    let i : Fin N := ⟨S, hS⟩
    if hr : row < d i.succ then
      if hc : col < d i.castSucc then some (tupIdxEquiv d ⟨⟨i, ⟨row, hr⟩⟩, ⟨col, hc⟩⟩) else none
    else none
  else none

/-- A flat coordinate in `layerCoords d ℓ` decodes (via `tupIdxEquiv`) to layer exactly `ℓ`. -/
theorem decode_layer_of_mem_layerCoords (d : Fin (N + 1) → ℕ) (ℓ : ℕ) (i : Fin (flatDim d))
    (hi : i ∈ layerCoords d ℓ) : (((tupIdxEquiv d).symm i).1.1 : ℕ) = ℓ := by
  simp only [layerCoords, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨q, hq, hqi⟩ := hi
  rw [← hqi, Equiv.symm_apply_apply]
  exact hq

/-- **case-1(2)/case-2 oracle step child: layer preserved, cleared advanced by one.** For a step child
`c` of `conOracle M s` whose edge case is `case12` or `case2`, the child state is `stepAppendAdvance`,
so `c.child.layer = s.layer` and `c.child.cleared = s.cleared + 1`. Dispatch mirrors
`divBirthCoord_persists_conOracle` (per-branch `conOracle`-reduction, terminal/rollover/case-1(1)
branches excluded by the case hypothesis). Supplies the layer-descent `sl = layer + 1` M7 needs. -/
theorem conOracle_child_layer_cleared_of_case12_case2 {L : ℕ} {M : Fin (L + 1) → ℕ} (s : ConState L)
    (c : StepChild M s) (hc : c ∈ (conOracle M s).stepChildren)
    (hcase : c.ecase = StepCase.case12 ∨ c.ecase = StepCase.case2) :
    c.child.layer = s.layer ∧ c.child.cleared = s.cleared + 1 := by
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
      rcases hcase with h | h <;> nomatch h
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
        exact ⟨rfl, rfl⟩
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
          · rcases hcase with h | h <;> nomatch h
          · exact ⟨rfl, rfl⟩

/-- **M7 emission — `canonShearOf` is within-carve.** At a case12/case2 real-branch edge (node = the
step, so `node.conState = ed.nextState`, `cleared ≥ 1`, `sl = layer+1`), the raw shear
`canonShearOf d p.conState` satisfies `ShearWithinCarveRaw`'s three clauses. The clause the shear-pin of
`IsRealBranch` and the L6 (★) A4 consume. -/
theorem canonShearOf_shearWithinCarve (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (p : TreePath d) (ed : TreeEdge d p)
    (hcase : ed.case = StepCase.case12 ∨ ed.case = StepCase.case2)
    (hpar : p.IsRealBranch e) (hdesc : DescendView d p ed)
    (hshear : ed.shearφ = canonShearOf d p.conState) :
    ShearWithinCarveRaw d e (p.extend ed) ed.shearφ := by
  -- map: M7-emission (canonShearOf satisfies ShearWithinCarveRaw I/II/III at case12/case2).
  -- PRODUCER lemma: L5 consumes it to CONSTRUCT `(p.extend ed).IsRealBranch e` (whose step arm
  -- contains this ShearWithinCarveRaw conjunct) — so the carrier is the PARENT's branch-hood + the
  -- edge's oracle data, NOT the child branch (that would be circular). (I) sl = supportLayerOf
  -- ed.nextState = layer+1 since `hdesc`'s sc gives ed.nextState.cleared = p.conState.cleared+1 (the
  -- case12/case2 stepAppendAdvance transition, a conOracle fact) > carve layer S ⟹ the
  -- layer-S-supported shear is 0 on ℓ≥sl (`canonShearOf_support`); (II) the shear reads only layer-S
  -- coords, disjoint from ℓ≥sl; (III) `divBirthInv_of_isRealBranch` at `hpar` + the step-threading
  -- `DivBirthInv_conOracle_stepChildren` give the CHILD ledger freshness (a=layer→b<cleared) ⟹ each
  -- birth corner fails the strict-interior guard (`canonShearOf_support`), so the shear vanishes there.
  obtain ⟨sc, hsc_mem, hecase, hchild⟩ := hdesc
  have hcaseSc : sc.ecase = StepCase.case12 ∨ sc.ecase = StepCase.case2 := by
    rw [hecase]; exact hcase
  obtain ⟨hlayerN, hclearedN⟩ :=
    conOracle_child_layer_cleared_of_case12_case2 p.conState sc hsc_mem hcaseSc
  have hcs : (p.extend ed).conState = sc.child := hchild.symm
  have hlayer : (p.extend ed).conState.layer = p.conState.layer := by rw [hcs]; exact hlayerN
  have hcleared : (p.extend ed).conState.cleared = p.conState.cleared + 1 := by
    rw [hcs]; exact hclearedN
  have hcl0 : ¬ ((p.extend ed).conState.cleared = 0) := by rw [hcleared]; omega
  have hsl : supportLayerOf (p.extend ed).conState = p.conState.layer + 1 := by
    unfold supportLayerOf; rw [if_neg hcl0, hlayer]
  have hchildInv : DivBirthInv d (p.extend ed).conState := by
    have h0 : DivBirthInv d sc.child :=
      DivBirthInv_conOracle_stepChildren p.conState
        (PivotPres.divBirthInv_of_isRealBranch e p hpar) sc hsc_mem
    rwa [← hcs] at h0
  rw [hshear]
  refine ⟨?_, ?_, ?_⟩
  · -- (I) write-zero on layers `≥ sl`: a nonzero displacement forces decode-layer `= p.conState.layer`
    -- (`canonShearOf_support`), but membership forces it `= ℓ ≥ sl > p.conState.layer`.
    intro ℓ hℓ i hi u _
    by_contra hne
    have h1 := (canonShearOf_support d p.conState u i hne).1
    have h2 := decode_layer_of_mem_layerCoords d ℓ i hi
    rw [hsl] at hℓ
    omega
  · -- (II) reads ignore layers `≥ sl`: on the interior branch both reads sit at layer
    -- `p.conState.layer`, disjoint from the updated coord `m` (layer `ℓ > p.conState.layer`).
    intro ℓ hℓ i w _ m hm t
    have hmℓ := decode_layer_of_mem_layerCoords d ℓ m hm
    rw [hsl] at hℓ
    have hmne : (((tupIdxEquiv d).symm m).1.1 : ℕ) ≠ p.conState.layer := by rw [hmℓ]; omega
    simp only [canonShearOf]
    split_ifs with h
    · congr 1
      · congr 1
        apply Function.update_of_ne
        intro heq; apply hmne; rw [← heq, Equiv.symm_apply_apply]; exact h.1
      · apply Function.update_of_ne
        intro heq; apply hmne; rw [← heq, Equiv.symm_apply_apply]; exact h.1
    · rfl
  · -- (III) vanish on ledger birth-corners: the corner decodes to `(a, b, b)`; `DivBirthInv` freshness
    -- at the child gives `a = layer → b < cleared = p.conState.cleared + 1`, so the strict-interior
    -- guard `p.conState.cleared < b` fails ⟹ `canonShearOf_support` forces the displacement to `0`.
    intro k i hcf u _
    by_contra hne
    have hsupp := canonShearOf_support d p.conState u i hne
    simp only [cornerToFlat] at hcf
    split_ifs at hcf with hS hr hc
    obtain rfl : tupIdxEquiv d
        (⟨⟨⟨((p.extend ed).conState.divBirthCoord k).1, hS⟩,
            ⟨((p.extend ed).conState.divBirthCoord k).2, hr⟩⟩,
          ⟨((p.extend ed).conState.divBirthCoord k).2, hc⟩⟩ : tupIdx d) = i :=
      Option.some.inj hcf
    rw [Equiv.symm_apply_apply] at hsupp
    have hAlayer : ((p.extend ed).conState.divBirthCoord k).1 = (p.extend ed).conState.layer := by
      rw [hlayer]; exact hsupp.1
    have hfr := hchildInv.2.2.1 k hAlayer
    rw [hcleared] at hfr
    have hB : p.conState.cleared < ((p.extend ed).conState.divBirthCoord k).2 := hsupp.2.1
    omega

/-- **Positive-branch value of `canonShearOf`** (proof-aid twin of `canonShearOf_support`; elder-sanctioned
2026-07-22). On the strict carve interior (decode-layer `= s.layer`, row & col `> s.cleared`) the
displacement is the explicit Schur cross-term `−u_γ·u_β`: `γ` at `(layer, row, s.cleared)`, `β` at
`(layer, s.cleared, col)`. NOT part of any pin (weakest-that-suffices declined it); the α/β witness of the
boost-readiness proof may want the explicit coefficients. -/
theorem canonShearOf_apply_interior (d : Fin (N + 1) → ℕ) (s : ConState N)
    (u : Fin (flatDim d) → ℝ) (k : Fin (flatDim d))
    (hlay : (((tupIdxEquiv d).symm k).1.1 : ℕ) = s.layer)
    (hrow : s.cleared < (((tupIdxEquiv d).symm k).1.2 : ℕ))
    (hcol : s.cleared < (((tupIdxEquiv d).symm k).2 : ℕ)) :
    canonShearOf d s u k =
      (-(u (tupIdxEquiv d ⟨⟨((tupIdxEquiv d).symm k).1.1, ((tupIdxEquiv d).symm k).1.2⟩,
              ⟨s.cleared, lt_trans hcol ((tupIdxEquiv d).symm k).2.isLt⟩⟩)))
        * (u (tupIdxEquiv d ⟨⟨((tupIdxEquiv d).symm k).1.1,
              ⟨s.cleared, lt_trans hrow ((tupIdxEquiv d).symm k).1.2.isLt⟩⟩,
            ((tupIdxEquiv d).symm k).2⟩)) := by
  simp only [canonShearOf]
  exact dif_pos ⟨hlay, hrow, hcol⟩

end DLNFibre.DLN.Aoyagi
