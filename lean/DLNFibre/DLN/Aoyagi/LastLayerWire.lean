import DLNFibre.DLN.Aoyagi.MonumentAtlas
import DLNFibre.DLN.Aoyagi.Case1Wire
import DLNFibre.DLN.Aoyagi.Case2TransportWire
import DLNFibre.DLN.Aoyagi.MultiAffineHomogWire

/-!
# `DLN.Aoyagi.LastLayerWire` — L(last)-clear preservation, primed twin (SEAT-LL)

DRAFT primed twin of `MonumentAtlas.lastLayer_clear_preserves`, discharged via the same
downstream divisibility engine `Case2Wire`'s twin uses (`Case1Wire.stepInv_child_delta0`,
`Case2TransportWire.case_child_stepInv_divisibility`) — both IMPORT `MonumentAtlas`, so the proof
cannot live upstream of them (same primed-twin rationale as `case2_preserves_stepInv'`). The
controller swaps the `MonumentAtlas` `sorry` to `:= lastLayer_clear_preserves' …` at integration.

**STATEMENT (elder verbatim REVISED, threads/LL/elder-lastlayer-verbatim.md, 2026-07-23).** Two
guards, not one, both killing the same disease (a δ=0 pullback of a unit-free residual):
* `hparent : p.conState.layer + 1 = N` — with `hlast` forces parent.layer = child.layer = N-1, a
  layer-preserving clear/merge, excluding BOTH rollover directions (the guard-hole seat-LL found:
  the δ=0 rollover INTO N-1 from N-2, whose pure pullback of the vanishing-at-0 interior parent
  makes `GeneratorCleared` false).
* the carried conditional `hgen : p.conState.cleared ≠ 0 → GeneratorCleared d e p` + the conditional
  OUTPUT `(p.extend ed).conState.cleared ≠ 0 → GeneratorCleared d e (p.extend ed)` — the born unit
  is threaded as its own invariant (born at the first genuine clear, carried after), NOT re-derived
  from an all-left `hinv` (`LastLayerInv` admits all-left even at cleared ≥ 1 — the δ=0
  subsequent-clear subtlety the earlier unconditional form missed).
* the pin `he : e = canonFlatten d` (elder idiom ruling 2026-07-23) — the all-Deg1 that conjA δ=1
  needs at cleared=0 is `canonFlatten`-DERIVED (the L3T3 homogeneity lane
  `coreGen_layerHomogeneous` / `foldResid_layerHomogeneous'` is `canonFlatten`-only; an abstract
  `∀ e` + `he_lin` is FALSE-as-stated, MonumentAtlas:1382). Restate-gate catch (seat-LL) → PIN, not
  consume. The interior spine (case1 chain + the two `MonumentAssembly` statements) is pinned
  atomically by L4D; the pinned `lastLayer_clear_preserves` signature (shared: arch-C bakes, L4D
  consumes, this file twins) must be character-identical — `he` placed right after `e` here
  (reconcile with L4D's frozen six).

Case-by-case under hparent (parent@N-1): cleared=0 case11 (merge, keeps 0) → child.cleared=0 →
output clause VACUOUS (no case11 born-unit needed); cleared=0 case12/2 (genuine clear → 1) → born
the unit via the δ=1 pivot dehomogenisation; cleared≥1 (δ=0) → `hgen` carries the unit through the
pullback.

**What is closed here vs the wall.**
* CONJUNCT A (child `∃q, StepInv`) — δ=0 CLOSED (`stepInv_child_delta0`, from `hinv.1`); δ=1 routes
  through `case_child_stepInv_divisibility`, whose `Deg1SupportedOn (foldResid p) ed.center` input
  is the one δ=1 sub-hole. Two parts: (a) all slots take the LEFT disjunct at cleared=0 — needs
  `foldResid p j 0 = 0` (Gap-B `foldResid_layerHomogeneous` vanishing) to rule out the unit
  disjunct; (b) the Deg1 decomp sits on `ed.center`. For case12/case2, `ed.center = supportAt` at
  cleared=0 (so (b) is `hinv`'s decomp directly, as in `case2_conjA`); for case11 (MERGE),
  `ed.center = canonCenterOf` is the merge-block (pivot ∪ `col < runLen`), which is NOT `supportAt`
  (= `col < widthMinUpto`) — so case11-δ=1 needs Deg1 on that merge-block specifically, a genuine
  sub-subtlety (case-split, or examine case11-at-cleared=0 reachability). NOT plain case-blind.
* CONJUNCT 2 (child per-slot disjunction) — the S=L descent (born-unit ∅ at cleared≥1). FRONTIER
  (descent lane).
* `GeneratorCleared` (conditional) — δ=1 genuine clear borns the unit (strict transform sends
  pivot→1, `blockBlowupCoordQuot p p = 1`, so a Deg1 residual is `c_pivot(0) ≠ 0` at the origin);
  δ=0 carries `hgen` through the pullback (CLOSABLE: reindex the parent's nonzero sum through
  `foldResid_extend_delta0`, mirroring `stepInv_child_delta0`).
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- **Conjunct A, case-blind — the child `StepInv` divisibility at an S=L clear.** δ=0 is the pure
pullback (`stepInv_child_delta0`, from the parent's `StepInv` in `hinv.1`); δ=1 (first clear) is the
`u_pivot` crux (`case_child_stepInv_divisibility`), whose `Deg1SupportedOn` input is derived from
`hinv`. Layer guards discharge from `hlast` (`ed.nextState.layer = N-1 < N`). -/
theorem lastLayer_conjA
    (d : Fin (N + 1) → ℕ) (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he : e = canonFlatten d)
    (p : TreePath d) (ed : TreeEdge d p)
    (hparent : p.conState.layer + 1 = N) (hlast : ed.nextState.layer + 1 = N)
    (hinv : LastLayerInv d e (supportAt d p.conState.layer p.conState.cleared) p)
    (hbranch : (p.extend ed).IsRealBranch e) :
    ∃ q : Fin (d (Fin.last N) * d 0) → Fin (foldNR d (p.extend ed)) → (Fin (flatDim d) → ℝ) → ℝ,
      StepInv (coreGen d e) (foldG d e (p.extend ed)) (foldB d e (p.extend ed))
        (foldResid d e (p.extend ed)) q (foldRegion d e (p.extend ed)) := by
  classical
  have hlt : ¬ N ≤ ed.nextState.layer := by omega
  by_cases hδ : edgeδ d p = true
  · -- δ=1 (parent.cleared = 0, first step at S=L): the u_pivot crux. Pin `e = canonFlatten d`, then
    -- the homogeneity feeder gives `foldResid p j 0 = 0`, which rules out the unit disjunct
    -- (all-left), and the Deg1 decomp on `ed.center` follows (case12/2: center = supportAt; case11:
    -- merge-block, the open sub-subtlety; rollover: excluded by hparent + hlast).
    subst he
    have hcl : p.conState.cleared = 0 := of_decide_eq_true hδ
    obtain ⟨hpbr, ⟨sc, hsc, hecase, hchild, hcenter, -⟩, -⟩ := hbranch
    have hpnt : ¬ N ≤ p.conState.layer := by omega
    have hsl : supportLayerOf p.conState = p.conState.layer := by
      unfold supportLayerOf; rw [if_pos hcl]
    have hguniv : foldRegion d (canonFlatten d) p = Set.univ :=
      foldRegion_eq_univ (canonFlatten d) p
    -- the born-at-canonFlatten vanishing: `foldResid p j 0 = 0` (homogeneity clause at the origin).
    have hvanish : ∀ j, foldResid d (canonFlatten d) p j 0 = 0 := by
      intro j
      have hhom := foldResid_layerHomogeneous' d hpos p hpnt hpbr j p.conState.layer
        (le_of_eq hsl) (by omega)
      exact hhom.2 0 (zero_mem_foldRegion d (canonFlatten d) p) (fun x _ => rfl)
    -- so every slot takes the LEFT (Deg1SupportedSlot) disjunct (unit dies at cleared=0).
    have hslot : ∀ j, Deg1SupportedSlot d (foldResid d (canonFlatten d) p) j
        (supportAt d p.conState.layer p.conState.cleared) (supportLayerOf p.conState)
        (foldRegion d (canonFlatten d) p) := by
      intro j
      rcases hinv.2 j with hd | ⟨unit, _, hne0, hunit⟩
      · exact hd
      · refine absurd ?_ hne0
        rw [← hunit 0 (by rw [hguniv]; exact Set.mem_univ _)]; exact hvanish j
    have htrans := conOracle_child_transition p.conState sc hsc
    rcases htrans with ⟨-, -, hL, -⟩ | ⟨hc12or2, -, -⟩ | ⟨-, -, -⟩
    · -- rollover: child.layer = parent.layer + 1 = N, contradicting hlast (child.layer = N-1).
      exfalso; rw [hchild] at hL; omega
    · -- case12/case2: ed.center = supportAt, then extract Deg1SupportedOn (mirrors case2_conjA).
      have hce : ed.center = supportAt d p.conState.layer p.conState.cleared := by
        rw [hcenter, supportAt, if_pos hcl, blockCoords]
        rcases hc12or2 with h | h <;>
          · simp only [canonCenterOf, h]; congr 1; ext q
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcl, Nat.zero_le, true_and]
      have hSX : supportAt d p.conState.layer p.conState.cleared
          ⊆ layerCoords d p.conState.layer := by
        rw [← hce, hcenter]
        exact canonCenterOf_append_subset_layerCoords d p.conState sc hc12or2.symm
      have hdeg1 : Deg1SupportedOn (foldResid d (canonFlatten d) p) ed.center
          (foldRegion d (canonFlatten d) p) := by
        rw [hce, hguniv]
        intro j
        obtain ⟨⟨c, hc_cont, hc_repr⟩, hperlayer⟩ := hslot j
        have haff : AffineOn (foldResid d (canonFlatten d) p j)
            (layerCoords d p.conState.layer) Set.univ := by
          have h := hperlayer p.conState.layer (by rw [hsl])
          rwa [hguniv] at h
        obtain ⟨c', hc'_cont, hc'_repr, hc'_ign⟩ := exists_ignoresCoords_decomp
          (foldResid d (canonFlatten d) p j) (supportAt d p.conState.layer p.conState.cleared)
          (layerCoords d p.conState.layer) hSX c
          (fun i => continuousOn_univ.mp (by rw [← hguniv]; exact hc_cont i))
          (fun u => hc_repr u (by rw [hguniv]; exact Set.mem_univ u)) haff
        exact ⟨c', fun i => (hc'_cont i).continuousOn, fun u _ => hc'_repr u, hc'_ign⟩
      exact case_child_stepInv_divisibility d (canonFlatten d) p ed (by omega) hdeg1 hinv.1
    · -- case11 (MERGE): `ed.center = canonCenterOf` is the merge-block (pivot ∪ `col < runLen`),
      -- NOT `supportAt` (`col < widthMinUpto`). Needs Deg1 on that merge-block — the parent's Deg1
      -- on `supportAt` (from `hslot`) is on a DIFFERENT (larger) set — a genuine sub-hole.
      -- map: B-Llast-conjA-delta1-case11 (merge-block Deg1; open sub-subtlety)
      sorry
  · -- δ=0 (subsequent clear, parent.cleared ≥ 1): pure pullback — CLOSED, case-blind, from hinv.1.
    have hδ0 : edgeδ d p = false := by
      cases h : edgeδ d p with
      | false => rfl
      | true => exact absurd h hδ
    obtain ⟨q, hq⟩ := hinv.1
    exact stepInv_child_delta0 d e ed hlt hδ0 q hq

/-- **L(last)-clear preservation, primed twin (DRAFT).** Statement-identical to the elder's REVISED
`MonumentAtlas.lastLayer_clear_preserves` verbatim (`hparent` guard + carried-conditional
`GeneratorCleared`). Conjunct A via `lastLayer_conjA`; the per-slot disjunction and the born-unit /
carried `GeneratorCleared` are the frontier (see file header). -/
theorem lastLayer_clear_preserves'
    (d : Fin (N + 1) → ℕ) (hN : 0 < N) (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he : e = canonFlatten d)
    (p : TreePath d) (ed : TreeEdge d p) (hlast : ed.nextState.layer + 1 = N)
    (hparent : p.conState.layer + 1 = N)
    (hinv : LastLayerInv d e (supportAt d p.conState.layer p.conState.cleared) p)
    (hgen : p.conState.cleared ≠ 0 → GeneratorCleared d e p)
    (hbranch : (p.extend ed).IsRealBranch e) :
    LastLayerInv d e
        (supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared) (p.extend ed)
      ∧ ((p.extend ed).conState.cleared ≠ 0 → GeneratorCleared d e (p.extend ed)) := by
  classical
  -- Conjunct A (child StepInv divisibility) — reused by both the invariant and GeneratorCleared.
  have hSI := lastLayer_conjA d hpos e he p ed hparent hlast hinv hbranch
  refine ⟨⟨hSI, ?_⟩, ?_⟩
  · -- CONJUNCT 2: per-slot disjunction at supportAt(child). At S=L the descent exhausts to the
    -- born-unit ∅ at cleared ≥ 1; uncleared slots vanish/descend, the cleared slot flips to a unit.
    -- map: B-Llast-clear-conjunct2 (S=L descent-to-∅ slot disjunction; descent lane)
    sorry
  · -- CONDITIONAL GeneratorCleared: only when the child has cleared a pivot.
    intro hcleared
    by_cases hδ : edgeδ d p = true
    · -- δ=1 (parent.cleared = 0). Under `hcleared` (child.cleared ≠ 0) this is a GENUINE clear
      -- (case12/case2 → child.cleared = 1; case11 keeps cleared = 0, excluded by hcleared). The
      -- strict transform dehomogenises the pivot (→ 1) to born the unit.
      -- map: B-Llast-clear-generatorCleared-born (δ=1 genuine clear born-unit via pivot→1)
      sorry
    · -- δ=0 (parent.cleared ≥ 1): `hgen` fires; carry GeneratorCleared(parent) through pullback.
      -- CLOSED: child witness `q' i j' u = q i (cast j') (stepMap u)` (StepInv via the pure
      -- pullback, as in `stepInv_child_delta0`); the nonzero sum at 0 reindexes the parent's
      -- through `foldResid_extend_delta0` + `stepMap_zero`.
      have hpc : p.conState.cleared ≠ 0 := by
        simp only [edgeδ, decide_eq_true_eq] at hδ; exact hδ
      have hlt : ¬ N ≤ ed.nextState.layer := by omega
      have hδ0 : edgeδ d p = false := by
        cases h : edgeδ d p with
        | false => rfl
        | true => exact absurd h hδ
      obtain ⟨i₀, q, ⟨hqc, hq0, hqd⟩, hne⟩ := hgen hpc
      have hcast := foldNR_extend_of_lt d ed hlt
      have hg : foldG d e (p.extend ed) = foldG d e p ∘ stepMap d ed := rfl
      have hb : ∀ u, foldB d e (p.extend ed) u = foldB d e p (stepMap d ed u) := by
        intro u; rw [foldB_extend_eq]; simp [hδ0]
      have hmem : ∀ w : Fin (flatDim d) → ℝ, w ∈ foldRegion d e p := by
        rw [foldRegion_eq_univ]; exact fun w ↦ Set.mem_univ w
      refine ⟨i₀, fun i j' u ↦ q i (Fin.cast hcast j') (stepMap d ed u), ⟨?_, ?_, ?_⟩, ?_⟩
      · -- q' continuity
        intro i j'
        have hc : Continuous (q i (Fin.cast hcast j')) :=
          continuousOn_univ.mp (by rw [← foldRegion_eq_univ e p]; exact hqc i (Fin.cast hcast j'))
        exact (hc.comp (continuous_stepMap d ed)).continuousOn
      · -- child S3 vanishing
        intro i
        show (coreGen d e i ∘ foldG d e (p.extend ed)) 0 = 0
        rw [hg]
        show (coreGen d e i ∘ foldG d e p) (stepMap d ed 0) = 0
        rw [stepMap_zero]; exact hq0 i
      · -- child divisibility factorization (pure pullback, reindexed)
        intro u _ i
        show (coreGen d e i ∘ foldG d e (p.extend ed)) u = _
        rw [hg]
        show (coreGen d e i ∘ foldG d e p) (stepMap d ed u) = _
        rw [hqd (stepMap d ed u) (hmem _) i]
        refine (Equiv.sum_comp (finCongr hcast)
          (fun j ↦ q i j (stepMap d ed u) *
            (foldB d e p (stepMap d ed u) * foldResid d e p j (stepMap d ed u)))).symm.trans ?_
        refine Finset.sum_congr rfl (fun j' _ ↦ ?_)
        simp only [finCongr_apply]
        rw [hb, foldResid_extend_delta0 d e ed hlt hδ0]
      · -- the born unit carries: the child's nonzero sum at 0 reindexes the parent's.
        show ∑ j', q i₀ (Fin.cast hcast j') (stepMap d ed 0)
            * foldResid d e (p.extend ed) j' 0 ≠ 0
        have heq : (∑ j' : Fin (foldNR d (p.extend ed)),
              q i₀ (Fin.cast hcast j') (stepMap d ed 0) * foldResid d e (p.extend ed) j' 0)
            = ∑ j, q i₀ j 0 * foldResid d e p j 0 := by
          rw [stepMap_zero]
          rw [← Equiv.sum_comp (finCongr hcast) (fun j ↦ q i₀ j 0 * foldResid d e p j 0)]
          refine Finset.sum_congr rfl (fun j' _ ↦ ?_)
          simp only [finCongr_apply]
          rw [foldResid_extend_delta0 d e ed hlt hδ0 j' 0, stepMap_zero]
        rw [heq]; exact hne

end DLNFibre.DLN.Aoyagi
