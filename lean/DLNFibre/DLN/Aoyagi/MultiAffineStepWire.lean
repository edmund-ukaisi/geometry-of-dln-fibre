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

/-! ### The δ=1 case11 arm — the strict transform with support STAYING

At a δ=1 (`p.conState.cleared = 0`) `case11` MERGE edge the child KEEPS the state (`layer`/`cleared`),
so the support stays `blockCoords (p.layer)` at threshold `p.layer`. The shear is the identity
(`edgeShear = id` at `case11`), and the reused pivot was born in an EARLIER layer
(`DivBirthInv` freshness at `cleared = 0`), so the strict-transform map `k ↦ if k = pivot then 1 else u k`
FIXES every coordinate at layers `≥ p.layer` and preserves off-`layerCoords ℓ` agreement — again
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
  -- map: B-derived-gap3-STEP-δ1-case11 (support STAYS blockCoords(p.layer); strict transform = update
  -- pivot→1 with edgeShear=id). PROVABLE (Codex 2026-07-22) via `deg1_comp_of_fixing` with
  -- σ = the strict-transform map, ONCE pivot-separation `pivot ∉ layerCoords ℓ (ℓ ≥ p.layer)` is in
  -- hand: the reused case11 pivot = `canonPivotOf` = a ledger birth-corner, whose birth layer < p.layer
  -- by `DivBirthInv` freshness at cleared=0. Deferring that oracle-unfold derivation (mirrors
  -- PivotPres.canonPivotOf_isLedgerCorner_conOracle + the pivot-pin) — a tracked provable hole, NOT the
  -- append blocker.
  sorry

/-- **The δ=1 case12/case2 arm — THE DEEP CORE (cofactor / Schur descent).** At a first-clear append
(`p.conState.cleared = 0 → 1`) the support DESCENDS `blockCoords (p.layer) → blockCoords (p.layer+1)`,
and the child residual is the strict transform `foldResid p (cast ·) (qm ·)`. This is NOT provable from
`hslot` alone: the counterexample `foldResid p = (u ↦ u_pivot)` satisfies `hslot` yet its strict
transform is the constant `1`, which is not `Deg1`-supported on the descended block (fails clause-1 at
`u = 0`). The descent needs the cross-layer cofactor identity `c_i(qm u) = ∑_{k∈S'} a_ik u · u_k` — the
pivot coefficient must carry a next-layer-block (Schur) factor — genuine monument content NOT captured
by `Deg1SupportedSlot`. Codex (xhigh) confirmed 2026-07-22. A SECOND on-cone stub (beside
`realBranch_boostReady_case11`), OR the parent invariant must be strengthened; escalated to the
controller. -/
theorem descent_delta1_append {N : ℕ} {d : Fin (N + 1) → ℕ}
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
  -- map: B-derived-gap3-STEP-δ1-append (cofactor/Schur descent; UNPROVABLE from hslot alone — the
  -- cross-layer identity c_i(qm)=∑_{k∈S'} a_ik·u_k; Codex-confirmed 2026-07-22; 2nd on-cone stub / escalated)
  sorry

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
      · exact descent_delta1_append e p ed hlayer hδ (Or.inl h12) hbranch hslot
      · by_cases h2 : ed.case = StepCase.case2
        · exact descent_delta1_append e p ed hlayer hδ (Or.inr h2) hbranch hslot
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
