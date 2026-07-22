import DLNFibre.DLN.Aoyagi.MonumentAtlas
import DLNFibre.Core.Aoyagi.BlockDivision

/-!
# `DLN.Aoyagi.Case2TransportWire` — the DIVISIBILITY half of the one-step transport (SEAT-L3T)

**SCOPE — the HONEST, provable content, wired to the fold defs.** This file banks the DIVISIBILITY
conjunct (conjunct A of `FoldStepInvAt`) of the one-step INTERIOR preservation, case-BLIND (serves the
case-2 leaf `case2_preserves_stepInv` AND the case-1 wall `case1_preserves_stepInv`): from the parent
`StepInv` + `Deg1SupportedOn`, the child `StepInv` against the fold's own `foldG/foldB/foldResid`, with
`q' = q∘stepMap`. (The terminal-edge unit-residual `StepInv` — the elder's "whole quotient absorbs into
q′" collapse — is a natural companion but needs the Deg1-rep continuity plumbing to sum the residual
into a single `Fin 1` quotient; not banked here pending the invariant decision below.)

**WHAT IS NOT HERE, AND WHY (seat-L3T SPECIFY finding, decorrelated-Codex-confirmed).** The other two
conjuncts of the two leaves are FALSE-AS-STATED from the current hypotheses; they are NOT filled here
(a `sorry` with a wrong statement misleads — charter §0(iv), "fix wrong statements first"):
* `terminal_edge_stepInv` conjunct (2) — the born-terminally generator `∃ i₀ unit, unit 0 ≠ 0 ∧
  coreGen i₀∘foldG = foldB·unit`. Divisibility + `Deg1SupportedOn` force EVERY quotient to vanish at the
  deepest point, so no bare generator exists at δ=0 (refuted); at δ=1 the cleared-pivot combination is
  underivable. The born-terminally is genuine cleared-pivot geometry, absent from the signature.
* `case2_preserves_stepInv` / `case1_preserves_stepInv` conjunct (B) — `Deg1SupportedOn` of the CHILD
  residual. Under the strict transform the parent's pivot-coordinate term collapses to a degree-0 unit
  (nonzero at 0 ⟹ breaks child Deg1), and a non-block-preserving shear breaks the non-pivot part.
  Codex counterexample: center {p,i}, shear (u_p,u_i)↦(u_p,u_i+u_p), residual u_p+u_i is valid parent
  Deg1 but the child (δ=1) residual 1+u_i+u_p is nonzero at 0.

The DIVISIBILITY half below is unaffected by those defects — it is a true identity for both δ (the δ=1
branch rides seat-L4's `foldResid_stepMap_eq_pivot_mul` crux, re-proved here as
`foldResid_pullback_pivot_factor` to keep this file standalone during parallel-dev — DEDUPE with
`Case1Wire.foldResid_stepMap_eq_pivot_mul` at integration). It feeds whatever repaired invariant the
elder/controller adopts.

**HYPOTHESIS SHAPE — PRE-REVISION (controller round, fork (A) ruled 2026-07-22).** The elder ruled
fork (A): the interior leaf's Deg1 conjunct restates on the STRICT-TRANSFORMED residual over
`ed.center \ {ed.pivot}` with IDEAL-MEMBERSHIP coefficients, and the born-terminally pivot content
becomes a tracked datum (`LastLayerInv`'s unit disjunct, feeding the transport's `hcleared`). The two
lemmas here are stated against the CURRENT `FoldStepInvAt`/Deg1-on-center hypotheses; under fork (A)
those inputs are supplied by `LastLayerInv` (its divisibility + ideal conjuncts). The lemmas'
CONCLUSIONS and the divisibility CONTENT are unchanged — they are the round's confirmed FLOOR
(elder pin 4). Re-check the hypothesis wiring at the arch-C rebase that pins `LastLayerInv`.
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- **The edge shear keeps the pivot coordinate** — `id` at case11/rollover, `blockShear` (via
`hshear_pivot`) at case12/case2. (Same fact as `Case1Wire.edgeShear_keeps_pivot`; standalone here.) -/
theorem edgeShear_keeps_pivot' (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p)
    (u : Fin (flatDim d) → ℝ) : edgeShear d ed u ed.pivot = u ed.pivot := by
  change edgeShearRaw d ed.case ed.shearφ u ed.pivot = u ed.pivot
  cases ed.case
  · rfl
  · exact ed.hshear_pivot u
  · exact ed.hshear_pivot u
  · rfl

/-- **The pivot-factor crux** (seat-L4, re-proved standalone). For a `Deg1SupportedOn` parent residual
(center `ed.center`), the parent residual pulled back through `stepMap` (blow-up OUTERMOST) factors as
`u_pivot ·` the residual at the `blockBlowupCoordQuot`-map (the strict transform). DEDUPE with
`Case1Wire.foldResid_stepMap_eq_pivot_mul` at integration. -/
theorem foldResid_pullback_pivot_factor (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) {p : TreePath d} (ed : TreeEdge d p)
    (hdeg1 : Deg1SupportedOn (foldResid d e p) ed.center (foldRegion d e p))
    (j : Fin (foldNR d p)) (u : Fin (flatDim d) → ℝ) :
    foldResid d e p j (stepMap d ed u)
      = u ed.pivot
        * foldResid d e p j (fun k ↦ blockBlowupCoordQuot ed.pivot k (edgeShear d ed u)) := by
  classical
  set qm : Fin (flatDim d) → ℝ := fun k ↦ blockBlowupCoordQuot ed.pivot k (edgeShear d ed u) with hqm
  set σu : Fin (flatDim d) → ℝ := stepMap d ed u with hσu
  have hσu_eq : ∀ k, σu k = blockBlowupMap ed.center ed.pivot (edgeShear d ed u) k := fun k ↦ rfl
  have hagree : ∀ s, s ∉ ed.center → σu s = qm s := by
    intro s hs
    have hsp : s ≠ ed.pivot := fun h ↦ hs (h ▸ ed.hpivot)
    rw [hσu_eq s, blockBlowupMap_spectator_eq ed.center ed.hpivot hs (edgeShear d ed u), hqm]
    change edgeShear d ed u s = (if s = ed.pivot then (1 : ℝ) else edgeShear d ed u s)
    rw [if_neg hsp]
  obtain ⟨c, _hc, hrepr, hign⟩ := hdeg1 j
  have hmem : ∀ w : Fin (flatDim d) → ℝ, w ∈ foldRegion d e p := by
    rw [foldRegion_eq_univ]; exact fun w ↦ Set.mem_univ w
  have hceq : ∀ i, c i σu = c i qm := by
    intro i
    have := (ignoresCoords_univ_iff_agree (c i) ed.center)
    rw [foldRegion_eq_univ] at hign
    exact (this.mp (hign i)) σu qm hagree
  rw [hrepr σu (hmem _), hrepr qm (hmem _), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi ↦ ?_)
  have hcenter : σu i = u ed.pivot * qm i := by
    rw [hσu_eq i, hqm]
    exact blockBlowupMap_shear_center_eq ed.center ed.pivot hi (edgeShear d ed)
      (edgeShear_keeps_pivot' d ed) u
  rw [hceq i, hcenter]; ring

/-- `foldNR` at an INTERIOR extend collapses to the parent width. -/
theorem foldNR_extend_interior (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p)
    (hlayer : ed.nextState.layer < N) :
    foldNR d (p.extend ed) = foldNR d p := by
  show (if N ≤ ed.nextState.layer then 1 else foldNR d p) = foldNR d p
  rw [if_neg (Nat.not_le.mpr hlayer)]

/-- **The unified one-step product identity** — for an INTERIOR edge, the child's dominant×residual
equals the parent's dominant×residual pulled through `stepMap`, at the cast index. Holds for BOTH δ:
δ=0 by the pure-pullback def; δ=1 the child dominant's `u_pivot` balances the residual's strict-transform
factor via `foldResid_pullback_pivot_factor`. This is the divisibility content; it does NOT touch the
(false-as-stated) `Deg1SupportedOn` conjunct. -/
theorem foldB_foldResid_extend_interior (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) {p : TreePath d} (ed : TreeEdge d p)
    (hlayer : ed.nextState.layer < N)
    (hdeg1 : Deg1SupportedOn (foldResid d e p) ed.center (foldRegion d e p))
    (j' : Fin (foldNR d (p.extend ed))) (u : Fin (flatDim d) → ℝ) :
    foldB d e (p.extend ed) u * foldResid d e (p.extend ed) j' u
      = foldB d e p (stepMap d ed u)
        * foldResid d e p (Fin.cast (foldNR_extend_interior d ed hlayer) j') (stepMap d ed u) := by
  classical
  have hnot : ¬ N ≤ ed.nextState.layer := Nat.not_le.mpr hlayer
  -- the child residual at an interior edge, reduced to the δ-dispatch (via `change` to the raw
  -- `.step` arm — defeq: `p.extend ed` reduces to `.step`, `edgeShearRaw = edgeShear`,
  -- `stepMapRaw = stepMap`, and the cast proofs are proof-irrelevant).
  have hResid : foldResid d e (p.extend ed) j' u
      = if edgeδ d p then
          foldResid d e p (Fin.cast (foldNR_extend_interior d ed hlayer) j')
            (fun k ↦ blockBlowupCoordQuot ed.pivot k (edgeShear d ed u))
        else
          foldResid d e p (Fin.cast (foldNR_extend_interior d ed hlayer) j') (stepMap d ed u) := by
    change (if h : N ≤ ed.nextState.layer then (fun _ ↦ (1 : (Fin (flatDim d) → ℝ) → ℝ))
            else fun j u ↦ if edgeδ d p then
                foldResid d e p (Fin.cast (if_neg h) j)
                  (fun k ↦ blockBlowupCoordQuot ed.pivot k (edgeShearRaw d ed.case ed.shearφ u))
              else foldResid d e p (Fin.cast (if_neg h) j)
                  (stepMapRaw d ed.case ed.center ed.pivot ed.shearφ u)) j' u = _
    rw [dif_neg hnot]; rfl
  rw [hResid, foldB_extend_eq]
  by_cases hδ : edgeδ d p
  · -- δ=1: u_pivot^1 · foldB p(σu) · strict = foldB p(σu) · (u_pivot · strict) = foldB p(σu)·foldResid p(σu)
    rw [if_pos hδ, if_pos hδ, pow_one]
    rw [foldResid_pullback_pivot_factor d e ed hdeg1 _ u]
    ring
  · -- δ=0: u_pivot^0 · foldB p(σu) · foldResid p(σu) = foldB p(σu)·foldResid p(σu)
    rw [if_neg hδ, if_neg hδ, pow_zero, one_mul]

/-- **The DIVISIBILITY conjunct (conjunct A) of the one-step preservation — CASE-BLIND.** From the
parent's `StepInv` (divisibility) + `Deg1SupportedOn`, the child (interior edge) `StepInv` holds against
the fold's own `foldG`/`foldB`/`foldResid`, with child quotient `q' = q∘stepMap` at the cast index. Serves
both `case2_preserves_stepInv` and `case1_preserves_stepInv`'s divisibility half. (The `Deg1SupportedOn`
conjunct (B) is the open/false part — see the file header.) -/
theorem case_child_stepInv_divisibility (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (p : TreePath d) (ed : TreeEdge d p)
    (hlayer : ed.nextState.layer < N)
    (hdeg1 : Deg1SupportedOn (foldResid d e p) ed.center (foldRegion d e p))
    (hSI : ∃ q : Fin (d (Fin.last N) * d 0) → Fin (foldNR d p) → (Fin (flatDim d) → ℝ) → ℝ,
      StepInv (coreGen d e) (foldG d e p) (foldB d e p) (foldResid d e p) q (foldRegion d e p)) :
    ∃ q : Fin (d (Fin.last N) * d 0) → Fin (foldNR d (p.extend ed)) → (Fin (flatDim d) → ℝ) → ℝ,
      StepInv (coreGen d e) (foldG d e (p.extend ed)) (foldB d e (p.extend ed))
        (foldResid d e (p.extend ed)) q (foldRegion d e (p.extend ed)) := by
  classical
  obtain ⟨q, hq_cont, hq_S3, hq_fact⟩ := hSI
  have hnr := foldNR_extend_interior d ed hlayer
  have hguniv : foldRegion d e p = Set.univ := foldRegion_eq_univ e p
  have hguniv' : foldRegion d e (p.extend ed) = Set.univ := foldRegion_eq_univ e (p.extend ed)
  refine ⟨fun i j' u ↦ q i (Fin.cast hnr j') (stepMap d ed u), ?_, ?_, ?_⟩
  · -- continuity of q' = q∘stepMap
    intro i j'
    rw [hguniv']
    exact (hq_cont i (Fin.cast hnr j')).comp (continuous_stepMap d ed).continuousOn
      (by rw [hguniv]; exact Set.mapsTo_univ _ _)
  · -- child S3
    intro i
    have h1 : (coreGen d e i ∘ foldG d e (p.extend ed)) 0
        = (coreGen d e i ∘ foldG d e p) (stepMap d ed 0) := rfl
    rw [h1, stepMap_zero]; exact hq_S3 i
  · -- child divisibility factorization
    intro u _ i
    have hLHS : (coreGen d e i ∘ foldG d e (p.extend ed)) u
        = (coreGen d e i ∘ foldG d e p) (stepMap d ed u) := rfl
    rw [hLHS, hq_fact (stepMap d ed u) (by rw [hguniv]; exact Set.mem_univ _) i]
    -- RHS: rewrite each summand via the product identity, then reindex by `Fin.cast hnr`.
    rw [show (∑ j', q i (Fin.cast hnr j') (stepMap d ed u)
              * (foldB d e (p.extend ed) u * foldResid d e (p.extend ed) j' u))
          = ∑ j', q i (Fin.cast hnr j') (stepMap d ed u)
              * (foldB d e p (stepMap d ed u)
                * foldResid d e p (Fin.cast hnr j') (stepMap d ed u)) from
        Finset.sum_congr rfl (fun j' _ ↦ by
          rw [foldB_foldResid_extend_interior d e ed hlayer hdeg1 j' u])]
    exact (Equiv.sum_comp (finCongr hnr)
      (fun j ↦ q i j (stepMap d ed u)
        * (foldB d e p (stepMap d ed u) * foldResid d e p j (stepMap d ed u)))).symm ▸ rfl

/-- **Continuity of a parent residual entry pulled back through a continuous map**, via the
`Deg1SupportedOn` representation (each `foldResid p j` is a center-coordinate combination with
continuous coefficients). Needed to collapse the residual family into a single continuous quotient. -/
theorem continuous_foldResid_comp (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) {p : TreePath d} {S : Finset (Fin (flatDim d))}
    (hdeg1 : Deg1SupportedOn (foldResid d e p) S (foldRegion d e p))
    (j : Fin (foldNR d p)) {F : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ)} (hF : Continuous F) :
    Continuous (fun u ↦ foldResid d e p j (F u)) := by
  classical
  obtain ⟨c, hc, hrepr, _⟩ := hdeg1 j
  have hguniv : foldRegion d e p = Set.univ := foldRegion_eq_univ e p
  have hEq : (fun u ↦ foldResid d e p j (F u))
      = fun u ↦ ∑ k ∈ S, c k (F u) * (F u) k := by
    funext u; rw [hrepr (F u) (by rw [hguniv]; exact Set.mem_univ _)]
  rw [hEq]
  refine continuous_finset_sum _ (fun k _ ↦ ?_)
  exact ((continuousOn_univ.mp (by rw [← hguniv]; exact hc k)).comp hF).mul
    ((continuous_apply k).comp hF)

/-- **The terminal-edge unit-residual `StepInv`** (the elder's "whole quotient absorbs into q′" HALF of
`terminal_edge_stepInv` — conjunct (1) ONLY). At a TERMINAL-reaching edge, from the parent `StepInv` +
`Deg1SupportedOn`, the child `StepInv` holds against the LITERAL `Fin 1` unit residual `fun _ ↦ 1`, with
the parent residual family collapsed into a single continuous quotient (δ=0: pure pullback; δ=1: the
`u_pivot` of `foldB` balances the residual's strict-transform factor via the crux). This is the honest,
stable content that a REPAIRED `terminal_edge_stepInv` keeps; it does NOT produce conjunct (2) (the
born-terminally `unit 0 ≠ 0` generator), which is false-as-derivable — see the file header. -/
theorem terminal_edge_unit_stepInv (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (p : TreePath d) (ed : TreeEdge d p)
    (hterm : N ≤ ed.nextState.layer)
    (hdeg1 : Deg1SupportedOn (foldResid d e p) ed.center (foldRegion d e p))
    (hSI : ∃ q : Fin (d (Fin.last N) * d 0) → Fin (foldNR d p) → (Fin (flatDim d) → ℝ) → ℝ,
      StepInv (coreGen d e) (foldG d e p) (foldB d e p) (foldResid d e p) q (foldRegion d e p)) :
    ∃ q : Fin (d (Fin.last N) * d 0) → Fin 1 → (Fin (flatDim d) → ℝ) → ℝ,
      StepInv (coreGen d e) (foldG d e (p.extend ed)) (foldB d e (p.extend ed))
        (fun _ : Fin 1 ↦ (1 : (Fin (flatDim d) → ℝ) → ℝ)) q (foldRegion d e (p.extend ed)) := by
  classical
  obtain ⟨q, hq_cont, hq_S3, hq_fact⟩ := hSI
  have hguniv : foldRegion d e p = Set.univ := foldRegion_eq_univ e p
  have hguniv' : foldRegion d e (p.extend ed) = Set.univ := foldRegion_eq_univ e (p.extend ed)
  -- the argument map: quot-map at δ=1, the step map at δ=0.
  set argMap : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ) :=
    fun u ↦ if edgeδ d p then (fun k ↦ blockBlowupCoordQuot ed.pivot k (edgeShear d ed u))
            else stepMap d ed u with hargMap
  have hargCont : Continuous argMap := by
    by_cases hδ : edgeδ d p
    · have : argMap = fun u ↦ (fun k ↦ blockBlowupCoordQuot ed.pivot k (edgeShear d ed u)) := by
        funext u; rw [hargMap]; simp only [if_pos hδ]
      rw [this]
      exact continuous_pi (fun k ↦
        (continuous_blockBlowupCoordQuot ed.pivot k).comp
          (continuousOn_univ.mp (analyticOnNhd_edgeShear d ed).continuousOn))
    · have : argMap = fun u ↦ stepMap d ed u := by funext u; rw [hargMap]; simp only [if_neg hδ]
      rw [this]; exact continuous_stepMap d ed
  refine ⟨fun i _ u ↦ ∑ j, q i j (stepMap d ed u) * foldResid d e p j (argMap u), ?_, ?_, ?_⟩
  · -- continuity of the collapsed quotient
    intro i _
    rw [hguniv']
    refine (continuous_finset_sum _ (fun j _ ↦ ?_)).continuousOn
    exact ((continuousOn_univ.mp ((by rw [hguniv] at hq_cont; exact hq_cont i j))).comp
        (continuous_stepMap d ed)).mul (continuous_foldResid_comp d e hdeg1 j hargCont)
  · -- child S3
    intro i
    have h1 : (coreGen d e i ∘ foldG d e (p.extend ed)) 0
        = (coreGen d e i ∘ foldG d e p) (stepMap d ed 0) := rfl
    rw [h1, stepMap_zero]; exact hq_S3 i
  · -- factorization with the collapsed residual (Fin 1)
    intro u _ i
    rw [Fin.sum_univ_one]
    show (coreGen d e i ∘ foldG d e (p.extend ed)) u
        = (∑ j, q i j (stepMap d ed u) * foldResid d e p j (argMap u))
          * (foldB d e (p.extend ed) u * 1)
    have hLHS : (coreGen d e i ∘ foldG d e (p.extend ed)) u
        = (coreGen d e i ∘ foldG d e p) (stepMap d ed u) := rfl
    rw [hLHS, hq_fact (stepMap d ed u) (by rw [hguniv]; exact Set.mem_univ _) i, foldB_extend_eq,
      mul_one]
    -- (∑ q·foldB p(σu)·foldResid p(σu)) = (∑ q·foldResid p(argMap))·(u_pivot^δ·foldB p(σu))
    by_cases hδ : edgeδ d p
    · -- δ=1: use the crux to turn foldResid p(σu) into u_pivot·foldResid p(quotMap u)
      have hArg : argMap u = fun k ↦ blockBlowupCoordQuot ed.pivot k (edgeShear d ed u) := by
        simp only [hargMap]; rw [if_pos hδ]
      rw [if_pos hδ, pow_one]
      simp only [hArg, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ ↦ ?_)
      rw [foldResid_pullback_pivot_factor d e ed hdeg1 j u]; ring
    · -- δ=0: pure pullback
      have hArg : argMap u = stepMap d ed u := by simp only [hargMap]; rw [if_neg hδ]
      rw [if_neg hδ, pow_zero, one_mul]
      simp only [hArg, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ ↦ ?_); ring

/-! ## Post-bake leaves (fork-(A) invariant: `Deg1SupportedSlot` over the descending `supportAt`)

SPECIFY skeletons (statement-identical to `MonumentAtlas`), carrying TRACKED-OPEN sorries while the
conjunct-B `supportAt`-descent re-factoring is built (coordinated with seat-L4 — same wall). The
divisibility conjunct rides the banked engine; the geometric fact driving both: the δ discriminator
ALIGNS with the support layer — J=0 ⟹ δ=1 ⟹ `supportAt` = layer S (the blow-up layer, residual gains
`u_pivot`); J≥1 ⟹ δ=0 ⟹ `supportAt` = layer S+1 (deeper — SPECTATORS of the layer-S blow-up, residual
fixed, pure pullback). -/

/-- **L3 — a case-2 edge preserves the foldState invariant** (statement-identical to
`MonumentAtlas.case2_preserves_stepInv`; primed to avoid the import clash — arch-C swaps the leaf's
`sorry` to `:= case2_preserves_stepInv' …` at integration). TRACKED-OPEN: the `supportAt`-descent
conjunct-B re-factoring. -/
theorem case2_preserves_stepInv'
    {N : ℕ} (d : Fin (N + 1) → ℕ) (hN : 0 < N) (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) (ed : TreeEdge d p) (hcase2 : ed.isCase2)
    (hlayer : ed.nextState.layer + 1 < N)
    (hcenter : ed.center ⊆ blockCoords d p.conState.layer)
    (hinv : FoldStepInvAt d e (supportAt d p.conState.layer p.conState.cleared) p)
    (hgrade : ShearGrades d e ed) :
    FoldStepInvAt d e
      (supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared) (p.extend ed) := by
  -- map: B-L3-case2-preserves-stepInv (support DESCENDS parent→child supportAt; Deg1SupportedSlot)
  classical
  have hlt : ed.nextState.layer < N := by omega
  have hnr := foldNR_extend_interior d ed hlt
  have hguniv : foldRegion d e p = Set.univ := foldRegion_eq_univ e p
  have hguniv' : foldRegion d e (p.extend ed) = Set.univ := foldRegion_eq_univ e (p.extend ed)
  obtain ⟨⟨qp, hqp_cont, hqp_S3, hqp_fact⟩, hslot⟩ := hinv
  refine ⟨?_, ?_⟩
  · -- CONJUNCT A (divisibility). δ=0 (ruling-independent, pure pullback) proved; δ=1 ruling-gated.
    by_cases hδ : edgeδ d p
    · -- δ=1: needs the u_pivot crux (support ⊆ ed.center); gated on the hcenter-direction ruling.
      -- map: B-L3-case2 conjA δ=1 (crux; hcenter direction — TRACKED-OPEN)
      sorry
    · -- δ=0: pure pullback, q' = qp∘stepMap; no crux, no hcenter.
      refine ⟨fun i j' u ↦ qp i (Fin.cast hnr j') (stepMap d ed u), ?_, ?_, ?_⟩
      · intro i j'
        rw [hguniv']
        exact (hqp_cont i (Fin.cast hnr j')).comp (continuous_stepMap d ed).continuousOn
          (by rw [hguniv]; exact Set.mapsTo_univ _ _)
      · intro i
        have h1 : (coreGen d e i ∘ foldG d e (p.extend ed)) 0
            = (coreGen d e i ∘ foldG d e p) (stepMap d ed 0) := rfl
        rw [h1, stepMap_zero]; exact hqp_S3 i
      · intro u _ i
        have hLHS : (coreGen d e i ∘ foldG d e (p.extend ed)) u
            = (coreGen d e i ∘ foldG d e p) (stepMap d ed u) := rfl
        rw [hLHS, hqp_fact (stepMap d ed u) (by rw [hguniv]; exact Set.mem_univ _) i]
        -- product identity δ=0: foldB(child)·foldResid(child) j' = (foldB p·foldResid p(cast j'))∘σ
        have hpid : ∀ j' : Fin (foldNR d (p.extend ed)),
            foldB d e (p.extend ed) u * foldResid d e (p.extend ed) j' u
              = foldB d e p (stepMap d ed u)
                * foldResid d e p (Fin.cast hnr j') (stepMap d ed u) := by
          intro j'
          have hnotle : ¬ N ≤ ed.nextState.layer := by omega
          have hResid : foldResid d e (p.extend ed) j' u
              = foldResid d e p (Fin.cast hnr j') (stepMap d ed u) := by
            change (if h : N ≤ ed.nextState.layer then (fun _ ↦ (1 : (Fin (flatDim d) → ℝ) → ℝ))
                else fun j u ↦ if edgeδ d p then
                    foldResid d e p (Fin.cast (if_neg h) j)
                      (fun k ↦ blockBlowupCoordQuot ed.pivot k (edgeShearRaw d ed.case ed.shearφ u))
                  else foldResid d e p (Fin.cast (if_neg h) j)
                      (stepMapRaw d ed.case ed.center ed.pivot ed.shearφ u)) j' u = _
            rw [dif_neg hnotle, if_neg hδ]; rfl
          rw [hResid, foldB_extend_eq, if_neg hδ, pow_zero, one_mul]
        rw [show (∑ j', qp i (Fin.cast hnr j') (stepMap d ed u)
                  * (foldB d e (p.extend ed) u * foldResid d e (p.extend ed) j' u))
              = ∑ j', qp i (Fin.cast hnr j') (stepMap d ed u)
                  * (foldB d e p (stepMap d ed u)
                    * foldResid d e p (Fin.cast hnr j') (stepMap d ed u)) from
            Finset.sum_congr rfl (fun j' _ ↦ by rw [hpid j'])]
        exact (Equiv.sum_comp (finCongr hnr)
          (fun j ↦ qp i j (stepMap d ed u)
            * (foldB d e p (stepMap d ed u) * foldResid d e p j (stepMap d ed u)))).symm ▸ rfl
  · -- CONJUNCT B (Deg1SupportedSlot on supportAt(child)): the ShearGrades re-factoring.
    -- map: B-L3-case2 conjB (child Deg1SupportedSlot via ShearGrades; δ=0 spectator + δ=1) — TRACKED-OPEN
    sorry

/-- **Terminal-edge transport** (statement-identical to `MonumentAtlas.terminal_edge_stepInv`; primed).
δ=0 (the S=L rollover, `p.cleared ≥ 1`) is proved fully: conjunct 1 the pure-pullback Fin-1 unit
`StepInv`, conjunct 2 the born-terminally generator from `hgen`. δ=1 (the case-blind N=1 corner) is a
TRACKED-OPEN sorry — its conjunct-1 divisibility needs the `u_pivot` crux (support ⊆ ed.center), which
`terminal_edge` lacks an `hcenter` for; flagged to the controller. -/
theorem terminal_edge_stepInv'
    {N : ℕ} (d : Fin (N + 1) → ℕ) (hN : 0 < N) (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) (ed : TreeEdge d p) (hterm : N ≤ ed.nextState.layer)
    (hinv : LastLayerInv d e (supportAt d p.conState.layer p.conState.cleared) p)
    (hgen : GeneratorCleared d e p) :
    ∃ (q : Fin (d (Fin.last N) * d 0) → Fin 1 → (Fin (flatDim d) → ℝ) → ℝ)
      (i₀ : Fin (d (Fin.last N) * d 0)) (unit : (Fin (flatDim d) → ℝ) → ℝ),
      StepInv (coreGen d e) (foldG d e (p.extend ed)) (foldB d e (p.extend ed))
          (fun _ : Fin 1 ↦ (1 : (Fin (flatDim d) → ℝ) → ℝ)) q (foldRegion d e (p.extend ed))
        ∧ ContinuousOn unit (foldRegion d e (p.extend ed))
        ∧ unit 0 ≠ 0
        ∧ (∀ u ∈ foldRegion d e (p.extend ed),
            (coreGen d e i₀ ∘ foldG d e (p.extend ed)) u = foldB d e (p.extend ed) u * unit u) := by
  classical
  obtain ⟨i₀, qg, hSIg, hgne⟩ := hgen
  obtain ⟨hqg_cont, hqg_S3, hqg_fact⟩ := hSIg
  have hguniv : foldRegion d e p = Set.univ := foldRegion_eq_univ e p
  have hguniv' : foldRegion d e (p.extend ed) = Set.univ := foldRegion_eq_univ e (p.extend ed)
  -- each residual slot is continuous (from LastLayerInv's per-slot disjunction).
  have hresid_cont : ∀ j, Continuous (fun u ↦ foldResid d e p j u) := by
    intro j
    rcases hinv.2 j with ⟨⟨c, hc, hrepr⟩, _⟩ | ⟨unitj, hunit_cont, _, hunit_eq⟩
    · have hEq : (fun u ↦ foldResid d e p j u)
          = fun u ↦ ∑ i ∈ supportAt d p.conState.layer p.conState.cleared, c i u * u i := by
        funext u; exact hrepr u (by rw [hguniv]; exact Set.mem_univ _)
      rw [hEq]
      refine continuous_finset_sum _ (fun i _ ↦ ?_)
      exact ((continuousOn_univ.mp (by rw [← hguniv]; exact hc i)).mul (continuous_apply i))
    · have hEq : (fun u ↦ foldResid d e p j u) = unitj := by
        funext u; exact hunit_eq u (by rw [hguniv]; exact Set.mem_univ _)
      rw [hEq]; exact continuousOn_univ.mp (by rw [← hguniv]; exact hunit_cont)
  by_cases hδ : edgeδ d p
  · -- δ=1 (case-blind N=1 corner): conjunct-1 divisibility needs the u_pivot crux (no hcenter here).
    -- map: B-L4t-terminal-edge-stepInv δ=1 corner (support⊆ed.center crux gap; TRACKED-OPEN)
    sorry
  · -- δ=0 (the S=L rollover): pure pullback; born-terminally from hgen.
    refine ⟨fun i _ u ↦ ∑ j, qg i j (stepMap d ed u) * foldResid d e p j (stepMap d ed u), i₀,
      fun u ↦ ∑ j, qg i₀ j (stepMap d ed u) * foldResid d e p j (stepMap d ed u), ?_, ?_, ?_, ?_⟩
    · -- conjunct 1: the Fin-1 unit-residual StepInv
      refine ⟨fun i _ ↦ ?_, fun i ↦ ?_, fun u _ i ↦ ?_⟩
      · -- continuity of the collapsed quotient
        rw [hguniv']
        refine (continuous_finset_sum _ (fun j _ ↦ ?_)).continuousOn
        exact ((continuousOn_univ.mp (by rw [← hguniv]; exact hqg_cont i j)).comp
          (continuous_stepMap d ed)).mul ((hresid_cont j).comp (continuous_stepMap d ed))
      · -- S3
        have h1 : (coreGen d e i ∘ foldG d e (p.extend ed)) 0
            = (coreGen d e i ∘ foldG d e p) (stepMap d ed 0) := rfl
        rw [h1, stepMap_zero]; exact hqg_S3 i
      · -- factorization: coreGen i∘foldG(child) = (∑ q·resid)∘σ · (foldB(child)·1)
        rw [Fin.sum_univ_one]
        show (coreGen d e i ∘ foldG d e (p.extend ed)) u
            = (∑ j, qg i j (stepMap d ed u) * foldResid d e p j (stepMap d ed u))
              * (foldB d e (p.extend ed) u * 1)
        have hLHS : (coreGen d e i ∘ foldG d e (p.extend ed)) u
            = (coreGen d e i ∘ foldG d e p) (stepMap d ed u) := rfl
        rw [hLHS, hqg_fact (stepMap d ed u) (by rw [hguniv]; exact Set.mem_univ _) i,
          foldB_extend_eq, if_neg hδ, pow_zero, one_mul, mul_one, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _ ↦ by ring)
    · -- ContinuousOn unit
      rw [hguniv']
      refine (continuous_finset_sum _ (fun j _ ↦ ?_)).continuousOn
      exact ((continuousOn_univ.mp (by rw [← hguniv]; exact hqg_cont i₀ j)).comp
        (continuous_stepMap d ed)).mul ((hresid_cont j).comp (continuous_stepMap d ed))
    · -- unit 0 ≠ 0 (from hgen, δ=0 collapse at the origin)
      show (∑ j, qg i₀ j (stepMap d ed 0) * foldResid d e p j (stepMap d ed 0)) ≠ 0
      rw [stepMap_zero]; exact hgne
    · -- the born-terminally equation
      intro u _
      show (coreGen d e i₀ ∘ foldG d e (p.extend ed)) u
          = foldB d e (p.extend ed) u * ∑ j, qg i₀ j (stepMap d ed u) * foldResid d e p j (stepMap d ed u)
      have hLHS : (coreGen d e i₀ ∘ foldG d e (p.extend ed)) u
          = (coreGen d e i₀ ∘ foldG d e p) (stepMap d ed u) := rfl
      rw [hLHS, hqg_fact (stepMap d ed u) (by rw [hguniv]; exact Set.mem_univ _) i₀,
        foldB_extend_eq, if_neg hδ, pow_zero, one_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ ↦ by ring)

end DLNFibre.DLN.Aoyagi
