import DLNFibre.DLN.Aoyagi.MonumentAtlas
import DLNFibre.DLN.Aoyagi.Case1Wire
import DLNFibre.DLN.Aoyagi.Case2Wire
import DLNFibre.DLN.Aoyagi.PivotPreservation
import DLNFibre.DLN.Aoyagi.L5FoldSpec
import DLNFibre.DLN.Aoyagi.CanonShear

/-!
# `DLN.Aoyagi.MultiAffineStepWire` — the per-step multi-affine slot DESCENT (SEAT-L3T2)

The primed leaf `realBranch_multiAffine_step'` (statement-identical to
`MonumentAtlas.realBranch_multiAffine_step`; the controller swaps the MonumentAtlas `sorry` to
`:= realBranch_multiAffine_step' …` at MonumentAssembly — same pattern as `Case2Wire`'s
`case2_preserves_stepInv'`). Lands HERE (not in `MonumentAtlas`) because the machinery it consumes —
`Case1Wire`'s `foldResid_extend_delta0`/`_delta1`/`exists_graded_decomp`/`realBranch_boostReady_case11`
and `PivotPreservation` — all IMPORT `MonumentAtlas`, so the proof cannot live upstream.

This is CONJUNCT B of the wall (both `case1_preserves_stepInv'` and `case2_preserves_stepInv'` consume
it): the child's `Deg1SupportedSlot` follows from the PARENT's (carried in `hslot`) plus the edge's
real-branch pins, `he_lin`-FREE. The ROOT anchoring lives in L5's base case, not here.
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-! ### The (layer, cleared) transition per edge kind (oracle-unfold, mirrors PivotPreservation)

An oracle step child's combinatorial state moves by a fixed law keyed on its case tag: a `rollover`
advances the layer and resets cleared (and fires only at layer exhaustion, `widthMinUpto ≤ cleared`);
a `case2`/`case12` append keeps the layer and advances cleared; a `case11` merge keeps both. Extracted
by the same `conOracle` dispatch as `PivotPres.canonPivotOf_isLedgerCorner_conOracle`. -/
theorem conOracle_child_transition {N : ℕ} {d : Fin (N + 1) → ℕ} (s : ConState N)
    (sc : StepChild d s) (hsc : sc ∈ (conOracle d s).stepChildren) :
    (sc.ecase = StepCase.rollover ∧ widthMinUpto d (s.layer + 1) ≤ s.cleared ∧
        sc.child.layer = s.layer + 1 ∧ sc.child.cleared = 0) ∨
    ((sc.ecase = StepCase.case2 ∨ sc.ecase = StepCase.case12) ∧
        sc.child.layer = s.layer ∧ sc.child.cleared = s.cleared + 1) ∨
    (sc.ecase = StepCase.case11 ∧ sc.child.layer = s.layer ∧ sc.child.cleared = s.cleared) := by
  by_cases h1 : N ≤ s.layer
  · have horacle : conOracle d s = oracleTerminal d s := by unfold conOracle; rw [dif_pos h1]
    rw [horacle] at hsc
    simp only [oracleTerminal, ConDecision.stepChildren, List.not_mem_nil] at hsc
  · have hlive : s.layer < N := not_le.mp h1
    by_cases h2 : widthMinUpto d (s.layer + 1) ≤ s.cleared
    · have horacle : conOracle d s = rolloverDecision d s (le_of_lt (not_le.mp h1)) h2 := by
        unfold conOracle; rw [dif_neg h1, dif_pos h2]
      rw [horacle] at hsc
      simp only [rolloverDecision, ConDecision.stepChildren, List.mem_singleton] at hsc
      subst hsc
      exact Or.inl ⟨rfl, h2, rfl, rfl⟩
    · have hlt : s.cleared < widthMinUpto d (s.layer + 1) := not_le.mp h2
      have hcap : s.cleared < layerCap d := lt_of_lt_of_le hlt (widthMinUpto_le_layerCap d _)
      rcases hmin : ((List.finRange s.numDiv).filterMap (fun k =>
          if s.cleared + 1 ≤ s.divTilde k ∧ s.divTilde k + 1 ≤ widthMinUpto d s.layer
          then some (s.divTilde k) else none)).min? with _ | target
      · -- case-2
        have horacle : conOracle d s = case2Decision d s
            (widthMinUpto d s.layer - s.cleared) (d ⟨s.layer + 1, by omega⟩ - s.cleared) hcap := by
          unfold conOracle; rw [dif_neg h1, dif_neg h2]
          split <;> simp_all only [reduceCtorEq]
        rw [horacle] at hsc
        simp only [case2Decision, ConDecision.stepChildren, List.mem_singleton] at hsc
        subst hsc
        exact Or.inr (Or.inl ⟨Or.inl rfl, rfl, rfl⟩)
      · rcases hf : chooseMin s target with _ | f
        · have horacle : conOracle d s = oracleTerminal d s := by
            unfold conOracle; rw [dif_neg h1, dif_neg h2]
            split <;> simp_all only [reduceCtorEq, Option.some.injEq]
            all_goals (try subst_vars)
            all_goals (try (split <;> simp_all only [reduceCtorEq]))
          rw [horacle] at hsc
          simp only [oracleTerminal, ConDecision.stepChildren, List.not_mem_nil] at hsc
        · -- case-1 (two children: case11 merge, then case12 split)
          have hgt : s.cleared < target := by
            obtain ⟨hmemtar, -⟩ := List.min?_eq_some_iff'.mp hmin
            rw [List.mem_filterMap] at hmemtar
            obtain ⟨k0, -, hk0⟩ := hmemtar
            by_cases hc0 : s.cleared + 1 ≤ s.divTilde k0 ∧
                s.divTilde k0 + 1 ≤ widthMinUpto d s.layer
            · rw [if_pos hc0] at hk0
              have hdt : s.divTilde k0 = target := Option.some.inj hk0
              omega
            · rw [if_neg hc0] at hk0; exact absurd hk0 (by simp)
          have horacle : conOracle d s = case1Decision d s f (target - s.cleared)
              (widthMinUpto d s.layer - s.cleared) (d ⟨s.layer + 1, by omega⟩ - s.cleared)
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
          rw [horacle] at hsc
          simp only [case1Decision, ConDecision.stepChildren, List.mem_cons,
            List.not_mem_nil, or_false] at hsc
          rcases hsc with rfl | rfl
          · -- merge (case11): child = ⟨s.layer, s.cleared, …⟩
            exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
          · -- split (case12): child = stepAppendAdvance
            exact Or.inr (Or.inl ⟨Or.inr rfl, rfl, rfl⟩)

/-- **A `case11` oracle step child carries a valid merge index** (`mergeIdx < numDiv`): the case-1
merge edge's `esubst.mergeIdx = f.val` for `f : Fin s.numDiv`. Same `conOracle` dispatch as
`conOracle_child_transition`; non-case11 branches contradict `hc11`. Unblocks the case11 pivot's
`canonPivotOf = some …` (⟹ it is a ledger corner ⟹ born below the layer). -/
theorem conOracle_case11_mergeIdx_lt {N : ℕ} {d : Fin (N + 1) → ℕ} (s : ConState N)
    (sc : StepChild d s) (hsc : sc ∈ (conOracle d s).stepChildren)
    (hc11 : sc.ecase = StepCase.case11) :
    sc.esubst.mergeIdx < s.numDiv := by
  by_cases h1 : N ≤ s.layer
  · have horacle : conOracle d s = oracleTerminal d s := by unfold conOracle; rw [dif_pos h1]
    rw [horacle] at hsc
    simp only [oracleTerminal, ConDecision.stepChildren, List.not_mem_nil] at hsc
  · have hlive : s.layer < N := not_le.mp h1
    by_cases h2 : widthMinUpto d (s.layer + 1) ≤ s.cleared
    · have horacle : conOracle d s = rolloverDecision d s (le_of_lt (not_le.mp h1)) h2 := by
        unfold conOracle; rw [dif_neg h1, dif_pos h2]
      rw [horacle] at hsc
      simp only [rolloverDecision, ConDecision.stepChildren, List.mem_singleton] at hsc
      subst hsc; exact absurd hc11 (by simp)
    · have hlt : s.cleared < widthMinUpto d (s.layer + 1) := not_le.mp h2
      have hcap : s.cleared < layerCap d := lt_of_lt_of_le hlt (widthMinUpto_le_layerCap d _)
      rcases hmin : ((List.finRange s.numDiv).filterMap (fun k =>
          if s.cleared + 1 ≤ s.divTilde k ∧ s.divTilde k + 1 ≤ widthMinUpto d s.layer
          then some (s.divTilde k) else none)).min? with _ | target
      · have horacle : conOracle d s = case2Decision d s
            (widthMinUpto d s.layer - s.cleared) (d ⟨s.layer + 1, by omega⟩ - s.cleared) hcap := by
          unfold conOracle; rw [dif_neg h1, dif_neg h2]
          split <;> simp_all only [reduceCtorEq]
        rw [horacle] at hsc
        simp only [case2Decision, ConDecision.stepChildren, List.mem_singleton] at hsc
        subst hsc; exact absurd hc11 (by simp)
      · rcases hf : chooseMin s target with _ | f
        · have horacle : conOracle d s = oracleTerminal d s := by
            unfold conOracle; rw [dif_neg h1, dif_neg h2]
            split <;> simp_all only [reduceCtorEq, Option.some.injEq]
            all_goals (try subst_vars)
            all_goals (try (split <;> simp_all only [reduceCtorEq]))
          rw [horacle] at hsc
          simp only [oracleTerminal, ConDecision.stepChildren, List.not_mem_nil] at hsc
        · have hgt : s.cleared < target := by
            obtain ⟨hmemtar, -⟩ := List.min?_eq_some_iff'.mp hmin
            rw [List.mem_filterMap] at hmemtar
            obtain ⟨k0, -, hk0⟩ := hmemtar
            by_cases hc0 : s.cleared + 1 ≤ s.divTilde k0 ∧
                s.divTilde k0 + 1 ≤ widthMinUpto d s.layer
            · rw [if_pos hc0] at hk0
              have hdt : s.divTilde k0 = target := Option.some.inj hk0
              omega
            · rw [if_neg hc0] at hk0; exact absurd hk0 (by simp)
          have horacle : conOracle d s = case1Decision d s f (target - s.cleared)
              (widthMinUpto d s.layer - s.cleared) (d ⟨s.layer + 1, by omega⟩ - s.cleared)
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
          rw [horacle] at hsc
          simp only [case1Decision, ConDecision.stepChildren, List.mem_cons,
            List.not_mem_nil, or_false] at hsc
          rcases hsc with rfl | rfl
          · exact f.isLt
          · exact absurd hc11 (by simp)

/-- **Every canonical-center coordinate decodes to a layer `≤ s.layer`** (the spectator bound). For
`case12`/`case2` the whole block sits at layer `s.layer`; for `case11` the row-block does too and the
reused-pivot corner sits at its birth layer `≤ s.layer` (`DivBirthInv` layer-bound); rollover has an
empty center. Feeds the "deeper-layer coordinate is a blow-up spectator" step of the δ=0 descent. -/
theorem canonCenterOf_decode_layer_le {N : ℕ} {d : Fin (N + 1) → ℕ} (s : ConState N)
    (sc : StepChild d s) (hinv : DivBirthInv d s)
    (x : Fin (flatDim d)) (hx : x ∈ canonCenterOf d s sc) :
    (((tupIdxEquiv d).symm x).1.1 : ℕ) ≤ s.layer := by
  classical
  rcases hc : sc.ecase with _ | _ | _ | _ <;> simp only [canonCenterOf, hc] at hx
  · -- case11: (canonPivotOf).toFinset ∪ row-block
    rw [Finset.mem_union] at hx
    rcases hx with hpiv | hrow
    · rw [Option.mem_toFinset, Option.mem_def] at hpiv
      simp only [canonPivotOf, hc] at hpiv
      split_ifs at hpiv with hm
      simp only [cornerToFlat] at hpiv
      split_ifs at hpiv with hS hr hcc
      obtain rfl : tupIdxEquiv d
          (⟨⟨⟨(s.divBirthCoord ⟨sc.esubst.mergeIdx, hm⟩).1, hS⟩,
              ⟨(s.divBirthCoord ⟨sc.esubst.mergeIdx, hm⟩).2, hr⟩⟩,
            ⟨(s.divBirthCoord ⟨sc.esubst.mergeIdx, hm⟩).2, hcc⟩⟩ : tupIdx d) = x :=
        Option.some.inj hpiv
      rw [Equiv.symm_apply_apply]
      exact hinv.2.1 ⟨sc.esubst.mergeIdx, hm⟩
    · rw [Finset.mem_image] at hrow
      obtain ⟨q, hq, rfl⟩ := hrow
      rw [Finset.mem_filter] at hq
      rw [Equiv.symm_apply_apply]
      exact le_of_eq hq.2.1
  · -- case12: widthMinUpto block, q.1.1 = s.layer
    rw [Finset.mem_image] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    rw [Finset.mem_filter] at hq
    rw [Equiv.symm_apply_apply]
    exact le_of_eq hq.2.1
  · -- case2: widthMinUpto block, q.1.1 = s.layer
    rw [Finset.mem_image] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    rw [Finset.mem_filter] at hq
    rw [Equiv.symm_apply_apply]
    exact le_of_eq hq.2.1
  · -- rollover: empty center
    exact absurd hx (by simp)

/-! ### The reusable descent helper — `Deg1SupportedSlot` composes with a support-fixing map

Both slot-preserving arms (δ=0 pullback; δ=1 case11 strict transform) reduce to: `g ∘ σ` is
`Deg1SupportedSlot` on the SAME support `S`/threshold `fromL` as `g`, provided `σ` FIXES every
coordinate on layers `≥ fromL` (so the `S`-linear part and each per-layer `AffineOn` grade survive) and
`σ` PRESERVES off-`layerCoords ℓ` agreement for each such `ℓ` (so the coefficient/constant parts still
ignore that layer). Continuity rides `σ` continuous. -/
theorem deg1_comp_of_fixing {N : ℕ} {d : Fin (N + 1) → ℕ}
    (g : (Fin (flatDim d) → ℝ) → ℝ)
    (S : Finset (Fin (flatDim d))) (fromL : ℕ)
    (σ : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ)) (hσcont : Continuous σ)
    (hSsub : S ⊆ layerCoords d fromL)
    (hfix : ∀ ℓ, fromL ≤ ℓ → ∀ x ∈ layerCoords d ℓ, ∀ u, σ u x = u x)
    (hagree : ∀ ℓ, fromL ≤ ℓ → ∀ u v : Fin (flatDim d) → ℝ,
        (∀ s, s ∉ layerCoords d ℓ → u s = v s) → ∀ s, s ∉ layerCoords d ℓ → σ u s = σ v s)
    (hc : ∃ c : Fin (flatDim d) → (Fin (flatDim d) → ℝ) → ℝ,
        (∀ i, ContinuousOn (c i) Set.univ) ∧ (∀ u ∈ Set.univ, g u = ∑ i ∈ S, c i u * u i))
    (hpl : PerLayerDeg1From d g fromL Set.univ) :
    (∃ c : Fin (flatDim d) → (Fin (flatDim d) → ℝ) → ℝ,
        (∀ i, ContinuousOn (c i) Set.univ) ∧
          (∀ u ∈ Set.univ, (fun u => g (σ u)) u = ∑ i ∈ S, c i u * u i)) ∧
      PerLayerDeg1From d (fun u => g (σ u)) fromL Set.univ := by
  classical
  refine ⟨?_, ?_⟩
  · -- clause 1: c' i = c i ∘ σ; σ fixes S ⟹ the S-linear part survives.
    obtain ⟨c, hc_cont, hc_repr⟩ := hc
    refine ⟨fun i u => c i (σ u), fun i => ?_, fun u _ => ?_⟩
    · exact ((continuousOn_univ.mp (hc_cont i)).comp hσcont).continuousOn
    · show g (σ u) = ∑ i ∈ S, c i (σ u) * u i
      rw [hc_repr (σ u) (Set.mem_univ _)]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [hfix fromL (le_refl _) i (hSsub hi) u]
  · -- clause 2: per-layer AffineOn composes with σ.
    intro ℓ hℓ
    obtain ⟨a, b, ha_ign, hb_ign, hrepr⟩ := hpl ℓ hℓ
    refine ⟨fun u => a (σ u), fun x u => b x (σ u), ?_, ?_, ?_⟩
    · refine (ignoresCoords_univ_iff_agree _ (layerCoords d ℓ)).mpr (fun u v hag => ?_)
      exact (ignoresCoords_univ_iff_agree a (layerCoords d ℓ)).mp ha_ign (σ u) (σ v)
        (hagree ℓ hℓ u v hag)
    · intro x hx
      refine (ignoresCoords_univ_iff_agree _ (layerCoords d ℓ)).mpr (fun u v hag => ?_)
      exact (ignoresCoords_univ_iff_agree (b x) (layerCoords d ℓ)).mp (hb_ign x hx) (σ u) (σ v)
        (hagree ℓ hℓ u v hag)
    · intro u _
      show g (σ u) = a (σ u) + ∑ x ∈ layerCoords d ℓ, b x (σ u) * u x
      rw [hrepr (σ u) (Set.mem_univ _)]
      congr 1
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [hfix ℓ hℓ x hx u]

/-! ### The δ=0 arm — the pure PULLBACK (all four edge kinds)

At a δ=0 edge (`p.conState.cleared ≠ 0`) the child support and threshold EQUAL the parent's
(`blockCoords (p.layer+1)` / `p.layer+1`, in every subcase), and the child residual is the pullback
`foldResid p (cast ·) ∘ stepMap`. The blow-up center sits at layers `≤ p.layer` (`canonCenterOf`
bound) and the shear vanishes / reads-ignore on layers `≥ p.layer+1` (`ShearWithinCarve` I/II), so
`stepMap` FIXES every coordinate at layers `≥ p.layer+1` and PRESERVES off-`layerCoords ℓ` agreement
there — exactly `deg1_comp_of_fixing`'s inputs. -/
theorem blockCoords_subset_layerCoords (d : Fin (N + 1) → ℕ) (ℓ : ℕ) :
    blockCoords d ℓ ⊆ layerCoords d ℓ := by
  intro x hx
  simp only [blockCoords, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨q, ⟨hq1, _⟩, rfl⟩ := hx
  simp only [layerCoords, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨q, hq1, rfl⟩

theorem descent_delta0 {N : ℕ} {d : Fin (N + 1) → ℕ}
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) (ed : TreeEdge d p) (hlayer : ed.nextState.layer + 1 < N)
    (hδ0 : edgeδ d p = false)
    (hbranch : (p.extend ed).IsRealBranch e)
    (hslot : ∀ j, Deg1SupportedSlot d (foldResid d e p) j
      (supportAt d p.conState.layer p.conState.cleared)
      (supportLayerOf p.conState) (foldRegion d e p)) :
    ∀ j, Deg1SupportedSlot d (foldResid d e (p.extend ed)) j
      (supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared)
      (supportLayerOf (p.extend ed).conState) (foldRegion d e (p.extend ed)) := by
  classical
  intro j
  have hcl : p.conState.cleared ≠ 0 := by
    simp only [edgeδ, decide_eq_false_iff_not] at hδ0; exact hδ0
  have hlt : ¬ N ≤ ed.nextState.layer := by omega
  -- transition of the child state
  obtain ⟨sc, hsc, hecase, hchild⟩ := realBranch_descendView e p ed hbranch
  have hcs : (p.extend ed).conState = sc.child := hchild.symm
  have htrans := conOracle_child_transition p.conState sc hsc
  have hnl : sc.child.layer = ed.nextState.layer := by rw [hchild]
  -- p.layer + 1 < N (needed for the supportAt J≠0 branch)
  have hN1 : p.conState.layer + 1 < N := by
    rcases htrans with ⟨_, _, hL, _⟩ | ⟨_, hL, _⟩ | ⟨_, hL, _⟩ <;> omega
  -- parent support and threshold = `blockCoords (layer+1)`, `layer+1`
  have hFLpar : supportLayerOf p.conState = p.conState.layer + 1 := by
    rw [supportLayerOf, if_neg hcl]
  have hCSpar : supportAt d p.conState.layer p.conState.cleared
      = blockCoords d (p.conState.layer + 1) := by
    rw [supportAt, if_neg hcl, if_pos hN1]
  -- child support and threshold coincide with the parent's (all subcases)
  have hFLchild : supportLayerOf (p.extend ed).conState = p.conState.layer + 1 := by
    rw [hcs]
    rcases htrans with ⟨_, _, hL, hC⟩ | ⟨_, hL, hC⟩ | ⟨_, hL, hC⟩
    · rw [supportLayerOf, hC, if_pos rfl, hL]
    · rw [supportLayerOf, hC, if_neg (by omega : ¬ p.conState.cleared + 1 = 0), hL]
    · rw [supportLayerOf, hC, if_neg hcl, hL]
  have hCSchild : supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared
      = blockCoords d (p.conState.layer + 1) := by
    rw [hcs]
    rcases htrans with ⟨_, _, hL, hC⟩ | ⟨_, hL, hC⟩ | ⟨_, hL, hC⟩
    · rw [hL, hC, supportAt, if_pos rfl]
    · rw [hL, hC, supportAt, if_neg (by omega : ¬ p.conState.cleared + 1 = 0), if_pos hN1]
    · rw [hL, hC, supportAt, if_neg hcl, if_pos hN1]
  -- centre-layer bound (spectator): every centre coord decodes to layer ≤ p.layer
  obtain ⟨sc', hmem', hEq'⟩ := realBranch_centerPin e p ed hbranch
  have hpInv : DivBirthInv d p.conState := PivotPres.divBirthInv_of_isRealBranch e p hbranch.1
  have hcb : ∀ y ∈ ed.center, (((tupIdxEquiv d).symm y).1.1 : ℕ) ≤ p.conState.layer := fun y hy =>
    canonCenterOf_decode_layer_le p.conState sc' hpInv y (hEq' ▸ hy)
  -- ShearWithinCarve at the child threshold `sl = p.layer + 1`
  have hwc := realBranch_shearWithinCarve e p ed hbranch
  rw [ShearWithinCarve, ShearWithinCarveRaw] at hwc
  obtain ⟨hwc1, hwc2, _⟩ := hwc
  have hguniv : foldRegion d e (p.extend ed) = Set.univ := foldRegion_eq_univ e (p.extend ed)
  -- `stepMap` fixes every coord at layers ≥ p.layer+1
  have hfix : ∀ ℓ, p.conState.layer + 1 ≤ ℓ → ∀ x ∈ layerCoords d ℓ, ∀ u,
      stepMap d ed u x = u x := by
    intro ℓ hℓ x hx u
    have hxℓ : (((tupIdxEquiv d).symm x).1.1 : ℕ) = ℓ := decode_layer_of_mem_layerCoords d ℓ x hx
    have hxc : x ∉ ed.center := fun h => by have := hcb x h; omega
    have hφ0 : ed.shearφ u x = 0 :=
      hwc1 ℓ (by rw [hFLchild]; exact hℓ) x hx u (by rw [hguniv]; exact Set.mem_univ _)
    show blockBlowupMap ed.center ed.pivot (edgeShear d ed u) x = u x
    rw [Core.Aoyagi.blockBlowupMap_offCenter_eq ed.center ed.pivot (edgeShear d ed u) hxc]
    exact PivotPres.edgeShearRaw_fixes_of_displacement_zero ed.case ed.shearφ u x hφ0
  -- `stepMap` preserves off-`layerCoords ℓ` agreement at layers ≥ p.layer+1
  have hagree : ∀ ℓ, p.conState.layer + 1 ≤ ℓ → ∀ u v : Fin (flatDim d) → ℝ,
      (∀ s, s ∉ layerCoords d ℓ → u s = v s) →
      ∀ s, s ∉ layerCoords d ℓ → stepMap d ed u s = stepMap d ed v s := by
    intro ℓ hℓ u v hag s hs
    have hES : ∀ w, w ∉ layerCoords d ℓ → edgeShear d ed u w = edgeShear d ed v w := by
      intro w hw
      have hφw : ed.shearφ u w = ed.shearφ v w :=
        (ignoresCoords_univ_iff_agree (fun z => ed.shearφ z w) (layerCoords d ℓ)).mp
          (by have := hwc2 ℓ (by rw [hFLchild]; exact hℓ) w; rwa [hguniv] at this) u v hag
      have huw : u w = v w := hag w hw
      show edgeShearRaw d ed.case ed.shearφ u w = edgeShearRaw d ed.case ed.shearφ v w
      cases ed.case <;> simp only [edgeShearRaw, id_eq, blockShear, Pi.add_apply, huw, hφw]
    have hpivc : ed.pivot ∉ layerCoords d ℓ := by
      intro h
      have hp := hcb ed.pivot ed.hpivot
      have := decode_layer_of_mem_layerCoords d ℓ ed.pivot h
      omega
    show blockBlowupMap ed.center ed.pivot (edgeShear d ed u) s
      = blockBlowupMap ed.center ed.pivot (edgeShear d ed v) s
    unfold blockBlowupMap
    by_cases hsp : s = ed.pivot
    · rw [if_pos hsp, if_pos hsp]; exact hES ed.pivot hpivc
    · by_cases hsc2 : s ∈ ed.center
      · rw [if_neg hsp, if_pos hsc2, if_neg hsp, if_pos hsc2, hES ed.pivot hpivc, hES s hs]
      · rw [if_neg hsp, if_neg hsc2, if_neg hsp, if_neg hsc2, hES s hs]
  -- child residual = parent (cast) pullback ∘ stepMap
  have hfun : foldResid d e (p.extend ed) j
      = fun u => foldResid d e p (Fin.cast (foldNR_extend_of_lt d ed hlt) j) (stepMap d ed u) := by
    funext u; exact foldResid_extend_delta0 d e ed hlt hδ0 j u
  rw [hCSchild, hFLchild, hguniv, Deg1SupportedSlot, hfun]
  have hpar := hslot (Fin.cast (foldNR_extend_of_lt d ed hlt) j)
  rw [Deg1SupportedSlot, hCSpar, hFLpar, foldRegion_eq_univ e p] at hpar
  exact deg1_comp_of_fixing _ (blockCoords d (p.conState.layer + 1)) (p.conState.layer + 1)
    (stepMap d ed) (continuous_stepMap d ed)
    (blockCoords_subset_layerCoords d (p.conState.layer + 1)) hfix hagree hpar.1 hpar.2

/-- **The case11 pivot is born below the current layer** (`decode-layer < p.layer` at δ=1). The reused
pivot is pinned to `canonPivotOf = cornerToFlat` of the merge target's ledger birth corner (valid via
`DivBirthInv`, `some` via the merge index `conOracle_case11_mergeIdx_lt`); `DivBirthInv` freshness at
`cleared = 0` forces its birth layer `< p.layer`. This is the pivot-separation the strict-transform
descent needs (so the `k = pivot ↦ 1` branch never touches a support/support-layer coordinate). -/
theorem case11_pivot_decode_lt {N : ℕ} {d : Fin (N + 1) → ℕ}
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) (ed : TreeEdge d p)
    (hδ1 : edgeδ d p = true) (hc11 : ed.case = StepCase.case11)
    (hbranch : (p.extend ed).IsRealBranch e) :
    (((tupIdxEquiv d).symm ed.pivot).1.1 : ℕ) < p.conState.layer := by
  obtain ⟨hrec, ⟨sc, hsc, hecase, -, -, hpivpin⟩, -, -⟩ := hbranch
  have hcl : p.conState.cleared = 0 := of_decide_eq_true hδ1
  have hsce : sc.ecase = StepCase.case11 := hecase.trans hc11
  have hmi : sc.esubst.mergeIdx < p.conState.numDiv :=
    conOracle_case11_mergeIdx_lt p.conState sc hsc hsce
  obtain ⟨hval, hlayerLE, hfresh, -⟩ := PivotPres.divBirthInv_of_isRealBranch e p hrec
  set bc := p.conState.divBirthCoord ⟨sc.esubst.mergeIdx, hmi⟩ with hbc
  have hcv := hval ⟨sc.esubst.mergeIdx, hmi⟩
  have hS : bc.1 < N := hcv.1
  have hrr : bc.2 < d (⟨bc.1, hS⟩ : Fin N).succ := hcv.2.2 _ rfl
  have hcc : bc.2 < d (⟨bc.1, hS⟩ : Fin N).castSucc := hcv.2.1 _ rfl
  have hcp1 : canonPivotOf d p.conState sc = cornerToFlat d bc.1 bc.2 := by
    simp only [canonPivotOf, hsce]
    rw [dif_pos hmi, ← hbc]
  have hcp2 : cornerToFlat d bc.1 bc.2
      = some (tupIdxEquiv d ⟨⟨⟨bc.1, hS⟩, ⟨bc.2, hrr⟩⟩, ⟨bc.2, hcc⟩⟩) := by
    simp only [cornerToFlat]
    rw [dif_pos hS, dif_pos hrr, dif_pos hcc]
  have hcpsome := hcp1.trans hcp2
  have hpiv : ed.pivot = tupIdxEquiv d ⟨⟨⟨bc.1, hS⟩, ⟨bc.2, hrr⟩⟩, ⟨bc.2, hcc⟩⟩ :=
    (hpivpin _ hcpsome).symm
  rw [hpiv, Equiv.symm_apply_apply]
  -- goal: bc.1 < p.conState.layer, via DivBirthInv freshness at cleared = 0
  rcases eq_or_lt_of_le (hlayerLE ⟨sc.esubst.mergeIdx, hmi⟩) with heq | hlt
  · exact absurd (hfresh ⟨sc.esubst.mergeIdx, hmi⟩ heq) (by rw [hcl]; exact Nat.not_lt_zero _)
  · exact hlt

/-! ### The δ=1 case11 arm — the strict transform with support STAYING

At a δ=1 (`p.conState.cleared = 0`) `case11` MERGE edge the child KEEPS the state (`layer`/`cleared`),
so the support stays `blockCoords (p.layer)` at threshold `p.layer`. The shear is the identity
(`edgeShear = id` at `case11`), and the reused pivot was born in an EARLIER layer
(`case11_pivot_decode_lt`), so the strict-transform map `k ↦ if k = pivot then 1 else u k` FIXES every
coordinate at layers `≥ p.layer` and preserves off-`layerCoords ℓ` agreement — again
`deg1_comp_of_fixing`. No `realBranch_boostReady_case11` (that is conjunct A only). -/
theorem descent_delta1_case11 {N : ℕ} {d : Fin (N + 1) → ℕ}
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) (ed : TreeEdge d p) (hlayer : ed.nextState.layer + 1 < N)
    (hδ1 : edgeδ d p = true) (hc11 : ed.case = StepCase.case11)
    (hbranch : (p.extend ed).IsRealBranch e)
    (hslot : ∀ j, Deg1SupportedSlot d (foldResid d e p) j
      (supportAt d p.conState.layer p.conState.cleared)
      (supportLayerOf p.conState) (foldRegion d e p)) :
    ∀ j, Deg1SupportedSlot d (foldResid d e (p.extend ed)) j
      (supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared)
      (supportLayerOf (p.extend ed).conState) (foldRegion d e (p.extend ed)) := by
  -- map: B-derived-gap3-STEP-δ1-case11 (support STAYS; strict transform = update pivot→1; helper + pivot-sep)
  classical
  intro j
  have hcl : p.conState.cleared = 0 := of_decide_eq_true hδ1
  have hlt : ¬ N ≤ ed.nextState.layer := by omega
  obtain ⟨sc, hsc, hecase, hchild⟩ := realBranch_descendView e p ed hbranch
  have hcs : (p.extend ed).conState = sc.child := hchild.symm
  have hsce : sc.ecase = StepCase.case11 := hecase.trans hc11
  have hchildLC : sc.child.layer = p.conState.layer ∧ sc.child.cleared = 0 := by
    rcases conOracle_child_transition p.conState sc hsc with ⟨he, _, _, _⟩ | ⟨he, _, _⟩ | ⟨_, hL, hC⟩
    · exact absurd (hsce.symm.trans he) (by simp)
    · rcases he with he | he <;> exact absurd (hsce.symm.trans he) (by simp)
    · exact ⟨hL, by rw [hC]; exact hcl⟩
  have hFL : supportLayerOf (p.extend ed).conState = p.conState.layer := by
    rw [hcs, supportLayerOf, hchildLC.2, if_pos rfl, hchildLC.1]
  have hCS : supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared
      = blockCoords d p.conState.layer := by
    rw [hcs, hchildLC.1, hchildLC.2, supportAt, if_pos rfl]
  have hFLpar : supportLayerOf p.conState = p.conState.layer := by rw [supportLayerOf, if_pos hcl]
  have hCSpar : supportAt d p.conState.layer p.conState.cleared = blockCoords d p.conState.layer := by
    rw [supportAt, if_pos hcl]
  have hedge : ∀ u, edgeShear d ed u = u := by
    intro u; show edgeShearRaw d ed.case ed.shearφ u = u; rw [hc11]; rfl
  have hpivlt := case11_pivot_decode_lt e p ed hδ1 hc11 hbranch
  have hguniv : foldRegion d e (p.extend ed) = Set.univ := foldRegion_eq_univ e (p.extend ed)
  set σ : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ) :=
    fun u k => blockBlowupCoordQuot ed.pivot k (edgeShear d ed u) with hσ
  have hfix : ∀ ℓ, p.conState.layer ≤ ℓ → ∀ x ∈ layerCoords d ℓ, ∀ u, σ u x = u x := by
    intro ℓ hℓ x hx u
    have hxℓ := decode_layer_of_mem_layerCoords d ℓ x hx
    have hxp : x ≠ ed.pivot := by intro h; rw [h] at hxℓ; omega
    show blockBlowupCoordQuot ed.pivot x (edgeShear d ed u) = u x
    rw [blockBlowupCoordQuot, if_neg hxp, hedge u]
  have hagree : ∀ ℓ, p.conState.layer ≤ ℓ → ∀ u v : Fin (flatDim d) → ℝ,
      (∀ s, s ∉ layerCoords d ℓ → u s = v s) →
      ∀ s, s ∉ layerCoords d ℓ → σ u s = σ v s := by
    intro ℓ _ u v hag s hs
    show blockBlowupCoordQuot ed.pivot s (edgeShear d ed u)
      = blockBlowupCoordQuot ed.pivot s (edgeShear d ed v)
    rw [blockBlowupCoordQuot, blockBlowupCoordQuot, hedge u, hedge v]
    by_cases hsp : s = ed.pivot
    · rw [if_pos hsp, if_pos hsp]
    · rw [if_neg hsp, if_neg hsp]; exact hag s hs
  have hσcont : Continuous σ := by
    apply continuous_pi; intro k
    by_cases hk : k = ed.pivot
    · have : (fun u => σ u k) = fun _ => (1 : ℝ) := by
        funext u; show blockBlowupCoordQuot ed.pivot k (edgeShear d ed u) = 1
        rw [blockBlowupCoordQuot, if_pos hk]
      rw [this]; exact continuous_const
    · have : (fun u => σ u k) = fun u => u k := by
        funext u; show blockBlowupCoordQuot ed.pivot k (edgeShear d ed u) = u k
        rw [blockBlowupCoordQuot, if_neg hk, hedge u]
      rw [this]; exact continuous_apply k
  have hfun : foldResid d e (p.extend ed) j
      = fun u => foldResid d e p (Fin.cast (foldNR_extend_of_lt d ed hlt) j) (σ u) := by
    funext u; exact foldResid_extend_delta1 d e ed hlt hδ1 j u
  rw [hCS, hFL, hguniv, Deg1SupportedSlot, hfun]
  have hpar := hslot (Fin.cast (foldNR_extend_of_lt d ed hlt) j)
  rw [Deg1SupportedSlot, hCSpar, hFLpar, foldRegion_eq_univ e p] at hpar
  exact deg1_comp_of_fixing _ (blockCoords d p.conState.layer) p.conState.layer σ hσcont
    (blockCoords_subset_layerCoords d p.conState.layer) hfix hagree hpar.1 hpar.2

/-- **Clause-2-only descent** (the `PerLayerDeg1From` half of `deg1_comp_of_fixing`, without the support
clause). Used by the δ=1 append arm, whose support DESCENDS (so the full helper's clause-1 does not
apply), but whose per-layer grade survives the strict transform for the SAME reason as δ=0. -/
theorem perLayerDeg1From_comp_of_fixing {N : ℕ} {d : Fin (N + 1) → ℕ}
    (g : (Fin (flatDim d) → ℝ) → ℝ) (fromL : ℕ)
    (σ : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ))
    (hfix : ∀ ℓ, fromL ≤ ℓ → ∀ x ∈ layerCoords d ℓ, ∀ u, σ u x = u x)
    (hagree : ∀ ℓ, fromL ≤ ℓ → ∀ u v : Fin (flatDim d) → ℝ,
        (∀ s, s ∉ layerCoords d ℓ → u s = v s) → ∀ s, s ∉ layerCoords d ℓ → σ u s = σ v s)
    (hpl : PerLayerDeg1From d g fromL Set.univ) :
    PerLayerDeg1From d (fun u => g (σ u)) fromL Set.univ := by
  intro ℓ hℓ
  obtain ⟨a, b, ha_ign, hb_ign, hrepr⟩ := hpl ℓ hℓ
  refine ⟨fun u => a (σ u), fun x u => b x (σ u), ?_, ?_, ?_⟩
  · refine (ignoresCoords_univ_iff_agree _ (layerCoords d ℓ)).mpr (fun u v hag => ?_)
    exact (ignoresCoords_univ_iff_agree a (layerCoords d ℓ)).mp ha_ign (σ u) (σ v)
      (hagree ℓ hℓ u v hag)
  · intro x hx
    refine (ignoresCoords_univ_iff_agree _ (layerCoords d ℓ)).mpr (fun u v hag => ?_)
    exact (ignoresCoords_univ_iff_agree (b x) (layerCoords d ℓ)).mp (hb_ign x hx) (σ u) (σ v)
      (hagree ℓ hℓ u v hag)
  · intro u _
    show g (σ u) = a (σ u) + ∑ x ∈ layerCoords d ℓ, b x (σ u) * u x
    rw [hrepr (σ u) (Set.mem_univ _)]
    congr 1
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [hfix ℓ hℓ x hx u]

-- `realBranch_appendResidDescent` (the δ=1 append CAP / conjunct-1 descent) now lives on canonical in
-- `MonumentAtlas` (Gap-B AMENDED bake, `hpos`-added, `supportAt(child)` form) as the named FRONTIER LEAF
-- (`canonShearOf`-consuming; the coupled-corank ≥ 2 confinement is the wall). `descent_delta1_append`
-- below consumes it from there; the old in-file copy is retired to avoid the name clash.

/-- **The δ=1 case12/case2 arm — THE DEEP CORE (cofactor / Schur descent).** Clause-1 (the support
DESCENT `blockCoords (p.layer) → blockCoords (p.layer+1)`) consumes `realBranch_cofactorDescent` through
`exists_graded_decomp` — the SINGLE tracked hole. Clause-2 (per-layer grade from `p.layer+1`) is PROVED
here: the strict-transform map `qm` fixes layers `≥ p.layer+1` and preserves off-`layerCoords ℓ`
agreement (spectator centre bound + `ShearWithinCarve` I/II), so the parent grade survives. -/
theorem descent_delta1_append {N : ℕ} {d : Fin (N + 1) → ℕ} (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) (ed : TreeEdge d p) (hlayer : ed.nextState.layer + 1 < N)
    (hδ1 : edgeδ d p = true) (hcase : ed.case = StepCase.case12 ∨ ed.case = StepCase.case2)
    (hbranch : (p.extend ed).IsRealBranch e)
    (hslot : ∀ j, Deg1SupportedSlot d (foldResid d e p) j
      (supportAt d p.conState.layer p.conState.cleared)
      (supportLayerOf p.conState) (foldRegion d e p)) :
    ∀ j, Deg1SupportedSlot d (foldResid d e (p.extend ed)) j
      (supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared)
      (supportLayerOf (p.extend ed).conState) (foldRegion d e (p.extend ed)) := by
  classical
  intro j
  have hcl : p.conState.cleared = 0 := of_decide_eq_true hδ1
  have hlt : ¬ N ≤ ed.nextState.layer := by omega
  obtain ⟨sc, hsc, hecase, hchild⟩ := realBranch_descendView e p ed hbranch
  have hcs : (p.extend ed).conState = sc.child := hchild.symm
  have hsce : sc.ecase = StepCase.case12 ∨ sc.ecase = StepCase.case2 := by
    rcases hcase with h | h
    · exact Or.inl (hecase.trans h)
    · exact Or.inr (hecase.trans h)
  have hchildLC : sc.child.layer = p.conState.layer ∧ sc.child.cleared = 1 := by
    rcases conOracle_child_transition p.conState sc hsc with ⟨he, _, _, _⟩ | ⟨_, hL, hC⟩ | ⟨he, _, _⟩
    · rcases hsce with h | h <;> exact absurd (h.symm.trans he) (by simp)
    · exact ⟨hL, by rw [hC]; omega⟩
    · rcases hsce with h | h <;> exact absurd (h.symm.trans he) (by simp)
  have hN1 : p.conState.layer + 1 < N := by
    have hnl : sc.child.layer = ed.nextState.layer := by rw [hchild]
    have := hchildLC.1; omega
  have hFLchild : supportLayerOf (p.extend ed).conState = p.conState.layer + 1 := by
    rw [hcs, supportLayerOf, hchildLC.2, if_neg (by omega : ¬ (1 : ℕ) = 0), hchildLC.1]
  have hCSchild : supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared
      = blockCoords d (p.conState.layer + 1) := by
    rw [hcs, hchildLC.1, hchildLC.2, supportAt, if_neg (by omega : ¬ (1 : ℕ) = 0), if_pos hN1]
  have hFLpar : supportLayerOf p.conState = p.conState.layer := by rw [supportLayerOf, if_pos hcl]
  have hCSpar : supportAt d p.conState.layer p.conState.cleared = blockCoords d p.conState.layer := by
    rw [supportAt, if_pos hcl]
  -- centre-layer bound + ShearWithinCarve at sl = p.layer + 1
  obtain ⟨sc', hmem', hEq'⟩ := realBranch_centerPin e p ed hbranch
  have hpInv : DivBirthInv d p.conState := PivotPres.divBirthInv_of_isRealBranch e p hbranch.1
  have hcb : ∀ y ∈ ed.center, (((tupIdxEquiv d).symm y).1.1 : ℕ) ≤ p.conState.layer := fun y hy =>
    canonCenterOf_decode_layer_le p.conState sc' hpInv y (hEq' ▸ hy)
  have hwc := realBranch_shearWithinCarve e p ed hbranch
  rw [ShearWithinCarve, ShearWithinCarveRaw] at hwc
  obtain ⟨hwc1, hwc2, _⟩ := hwc
  have hguniv : foldRegion d e (p.extend ed) = Set.univ := foldRegion_eq_univ e (p.extend ed)
  set σ : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ) :=
    fun u k => blockBlowupCoordQuot ed.pivot k (edgeShear d ed u) with hσ
  have hfix : ∀ ℓ, p.conState.layer + 1 ≤ ℓ → ∀ x ∈ layerCoords d ℓ, ∀ u, σ u x = u x := by
    intro ℓ hℓ x hx u
    have hxℓ := decode_layer_of_mem_layerCoords d ℓ x hx
    have hxp : x ≠ ed.pivot := by
      intro h; have := hcb ed.pivot ed.hpivot; rw [h] at hxℓ; omega
    have hφ0 : ed.shearφ u x = 0 :=
      hwc1 ℓ (by rw [hFLchild]; exact hℓ) x hx u (by rw [hguniv]; exact Set.mem_univ _)
    show blockBlowupCoordQuot ed.pivot x (edgeShear d ed u) = u x
    rw [blockBlowupCoordQuot, if_neg hxp]
    exact PivotPres.edgeShearRaw_fixes_of_displacement_zero ed.case ed.shearφ u x hφ0
  have hagree : ∀ ℓ, p.conState.layer + 1 ≤ ℓ → ∀ u v : Fin (flatDim d) → ℝ,
      (∀ s, s ∉ layerCoords d ℓ → u s = v s) →
      ∀ s, s ∉ layerCoords d ℓ → σ u s = σ v s := by
    intro ℓ hℓ u v hag s hs
    have hES : ∀ w, w ∉ layerCoords d ℓ → edgeShear d ed u w = edgeShear d ed v w := by
      intro w hw
      have hφw : ed.shearφ u w = ed.shearφ v w :=
        (ignoresCoords_univ_iff_agree (fun z => ed.shearφ z w) (layerCoords d ℓ)).mp
          (by have := hwc2 ℓ (by rw [hFLchild]; exact hℓ) w; rwa [hguniv] at this) u v hag
      have huw : u w = v w := hag w hw
      show edgeShearRaw d ed.case ed.shearφ u w = edgeShearRaw d ed.case ed.shearφ v w
      cases ed.case <;> simp only [edgeShearRaw, id_eq, blockShear, Pi.add_apply, huw, hφw]
    show blockBlowupCoordQuot ed.pivot s (edgeShear d ed u)
      = blockBlowupCoordQuot ed.pivot s (edgeShear d ed v)
    rw [blockBlowupCoordQuot, blockBlowupCoordQuot]
    by_cases hsp : s = ed.pivot
    · rw [if_pos hsp, if_pos hsp]
    · rw [if_neg hsp, if_neg hsp]; exact hES s hs
  -- parent per-layer grade, weakened to threshold p.layer + 1
  have hpar := hslot (Fin.cast (foldNR_extend_of_lt d ed hlt) j)
  rw [hCSpar, hFLpar, foldRegion_eq_univ e p] at hpar
  have hpar2 : PerLayerDeg1From d (foldResid d e p (Fin.cast (foldNR_extend_of_lt d ed hlt) j))
      (p.conState.layer + 1) Set.univ := fun ℓ hℓ => hpar.2 ℓ (by omega)
  have hfun : foldResid d e (p.extend ed) j
      = fun u => foldResid d e p (Fin.cast (foldNR_extend_of_lt d ed hlt) j) (σ u) := by
    funext u; exact foldResid_extend_delta1 d e ed hlt hδ1 j u
  rw [hCSchild, hFLchild, hguniv, Deg1SupportedSlot]
  refine ⟨?_, ?_⟩
  · -- clause 1: the support DESCENT — the canonical cap (MonumentAtlas frontier sorry; canonShearOf-consuming)
    have happend := realBranch_appendResidDescent d hpos e p ed hlayer hbranch hslot j
    rwa [hCSchild, hguniv] at happend
  · -- clause 2: the per-layer grade survives the strict transform (PROVED, shear-independent)
    rw [hfun]
    exact perLayerDeg1From_comp_of_fixing _ (p.conState.layer + 1) σ hfix hagree hpar2

/-- **The per-step multi-affine slot DESCENT (primed leaf; statement-identical to
`MonumentAtlas.realBranch_multiAffine_step`).** Dispatches: δ=0 pullback (`descent_delta0`, PROVED);
δ=1 `case11` strict transform (`descent_delta1_case11`); δ=1 `case12`/`case2` cofactor descent
(`descent_delta1_append`, the deep core); δ=1 `rollover` is unreachable (`widthMinUpto_pos`). -/
theorem realBranch_multiAffine_step' {N : ℕ} {d : Fin (N + 1) → ℕ}
    (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) (ed : TreeEdge d p) (hlayer : ed.nextState.layer + 1 < N)
    (hbranch : (p.extend ed).IsRealBranch e)
    (hslot : ∀ j, Deg1SupportedSlot d (foldResid d e p) j
      (supportAt d p.conState.layer p.conState.cleared)
      (supportLayerOf p.conState) (foldRegion d e p)) :
    ∀ j, Deg1SupportedSlot d (foldResid d e (p.extend ed)) j
      (supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared)
      (supportLayerOf (p.extend ed).conState) (foldRegion d e (p.extend ed)) := by
  -- map: B-derived-gap3-STEP (parent slot + edge pins → child slot; he_lin-FREE descent; root anchored in L5)
  by_cases hδ : edgeδ d p = true
  · by_cases h11 : ed.case = StepCase.case11
    · exact descent_delta1_case11 e p ed hlayer hδ h11 hbranch hslot
    · by_cases h12 : ed.case = StepCase.case12
      · exact descent_delta1_append hpos e p ed hlayer hδ (Or.inl h12) hbranch hslot
      · by_cases h2 : ed.case = StepCase.case2
        · exact descent_delta1_append hpos e p ed hlayer hδ (Or.inr h2) hbranch hslot
        · -- ed.case = rollover: unreachable at δ=1 (rollover needs cleared ≥ widthMinUpto > 0)
          exfalso
          obtain ⟨sc, hsc, hecase, -⟩ := realBranch_descendView e p ed hbranch
          have hcl : p.conState.cleared = 0 := of_decide_eq_true hδ
          rcases conOracle_child_transition p.conState sc hsc with
            ⟨_, hge, _, _⟩ | ⟨he, _, _⟩ | ⟨he, _, _⟩
          · have := widthMinUpto_pos hpos (p.conState.layer + 1); omega
          · rcases he with he | he
            · exact h2 (hecase.symm.trans he)
            · exact h12 (hecase.symm.trans he)
          · exact h11 (hecase.symm.trans he)
  · have hδ0 : edgeδ d p = false := by
      cases h : edgeδ d p with
      | false => rfl
      | true => exact absurd h hδ
    exact descent_delta0 e p ed hlayer hδ0 hbranch hslot

end DLNFibre.DLN.Aoyagi
