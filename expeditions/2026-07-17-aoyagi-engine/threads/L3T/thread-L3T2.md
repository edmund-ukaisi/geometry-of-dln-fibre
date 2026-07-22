# Thread L3T2 (succeeds seat-L3T at context limit)

Branch `expedition/aoyagi-engine-L3T2`, based on the post-redirect tip. Lanes: 0 port
LeafGeometryWire; 1 realBranch_terminal_edgeδ + terminal_edge_stepInv re-wire; 2 realBranch_cover
+ realBranch_descendView; 3 case2_preserves_stepInv; 4 GeneratorCleared consume-fit + Case1Wire dedupe.

## Status — PLAN COMPLETE (all 4 lanes landed)
- Lane 0 DONE — LeafGeometryWire.lean ported file-level, green, axiom-clean; integrated on canonical.
- Lane 1 DONE — after the STOP-ON-SUSPECT (kill-condition below) the elder rendered `hpos`;
  realBranch_terminal_edgeδ + terminal_edge_stepInv CLOSED in-place in MonumentAtlas, both
  `[propext, Classical.choice, Quot.sound]` (terminal_edgeδ closed with hpos ALONE — the soundness
  criterion). δ=1 terminal is a DEAD branch via realBranch_terminal_edgeδ.
- Lane 2 DONE — realBranch_descendView (obtain-projection) + realBranch_cover (cleared=0 block
  equality); both `[propext, Classical.choice, Quot.sound]`.
- Lane 3 DONE — Case2Wire.lean: case2_conjA (divisibility ∃q, both δ) axiom-clean; case2_preserves_stepInv'
  = ⟨case2_conjA, conjB⟩ with conjunct-B the SINGLE tracked on-cone sorry (seat-L4's shared re-factoring
  wall). δ=1 conjunct-A rides seat-L4's exists_ignoresCoords_decomp bridge (Codex-cross-checked TRUE).
- Lane 4 DONE — crux dedupe (Case2TransportWire.foldResid_pullback_pivot_factor now delegates to the
  canonical Case1Wire.foldResid_stepMap_eq_pivot_mul; local edgeShear_keeps_pivot' retired) +
  GeneratorCleared consume-fit regression example (lastLayer_clear_preserves emit → terminal_edge_stepInv
  consume, elaborates cleanly). Case2Wire green, cordon OK.

Open (not mine): Case2Wire conjunct-B (seat-L4 companion), realBranch_shearWithinCarve /
realBranch_multiAffine (held for their rounds), MonumentAtlas case2 stub swap (arch-C Assembly module).

## KILL-CONDITION (permanent record): realBranch_terminal_edgeδ MUST carry `hpos : ∀ k, 0 < d k`

`realBranch_terminal_edgeδ` as first extracted had NO `hpos`. It is then **FALSE**. Do not drop `hpos`.

Statement (broken form): `(hterm : N ≤ ed.nextState.layer) (hbranch : (p.extend ed).IsRealBranch e) ⊢
edgeδ d p = false`.

**Why the only proof route needs positivity.** The conclusion needs `p.conState.cleared ≠ 0`. A
terminal-reaching edge forces a ROLLOVER (case11/case12/case2 keep the layer — EngineConstruction
stepCase11/stepAppendAdvance; only stepRollover advances; and a non-terminal parent has `layer < N`).
The oracle rollover guard (conOracle) is `widthMinUpto d (layer+1) ≤ cleared`. To get `cleared ≥ 1`
you need `widthMinUpto d N ≥ 1`, i.e. `widthMinUpto_pos` — which REQUIRES `∀ i, 0 < d i`.
`widthMinUpto d n = (univ.filter (·≤n)).inf' _ d` (EngineDefs:154), so `d 0 = 0 ⟹ widthMinUpto d n = 0`
for every `n`. Positivity is not otherwise available: `e`'s existence does not force it (with `d 0 = 0`
the `d₁×0` matrix factor is a single point, so the homeomorphism still exists); there is no
`IsRealBranch → StateInvariant` reachability lemma; and `StateInvariant.live_width` is only an UPPER
bound on `cleared`.

**Concrete counterexample (`N ≥ 1`, `d 0 = 0`).** `widthMinUpto d ≡ 0`, so from `conRoot` (layer 0,
cleared 0) the rollover guard `0 ≤ 0` fires at every layer. `N−1` successive rollovers build a real
branch `p` at layer `N−1`, `cleared = 0` (each step: case = rollover, center `= ∅ = canonCenterOf
rollover`, pivot free since `canonPivotOf rollover = none`, shear `id` satisfies `ShearWithinCarveRaw`).
The rollover edge `ed` off `p` has `ed.nextState.layer = N ≥ N` (`hterm` ✓) and
`(p.extend ed).IsRealBranch e` ✓ — yet `edgeδ d p = decide (0 = 0) = true ≠ false`. Refuted.

**Fix (wiring-compatible):** add `hpos : ∀ k, 0 < d k`. The sole consumer `terminal_edge_stepInv`
already carries `hpos` (as do the case1/case2/lastLayer leaves), so it passes down — no downstream
statement change. This is an extraction oversight (every sibling redirect leaf has `hpos`; only this
one dropped it), the cheapest defect class.

### VALIDATED lane-1 proof body (drop-in once `hpos` is added to the statement)

Validated standalone (axiom-clean `[propext, Classical.choice, Quot.sound]`) against a local `hpos`'d
copy. Terminal-forced-rollover argument: a terminal-reaching edge advances the layer (`sc.child.layer =
ed.nextState.layer ≥ N > p.conState.layer`), and only a rollover advances the layer (case1/case2 keep
it; reduction mirrors `OracleInv_conOracle_stepChildren`), so the rollover guard `widthMinUpto d
(layer+1) ≤ cleared` holds — `widthMinUpto_pos hpos` then gives `cleared ≥ 1`, i.e. `edgeδ = false`.

    obtain ⟨-, ⟨sc, hsc, -, hchild, -, -⟩, -⟩ := hbranch
    suffices h : p.conState.cleared ≠ 0 by
      simp only [edgeδ, decide_eq_false_iff_not]; exact h
    by_cases h1 : N ≤ p.conState.layer
    · exfalso
      have horacle : conOracle d p.conState = oracleTerminal d p.conState := by
        unfold conOracle; rw [dif_pos h1]
      rw [horacle] at hsc
      simp only [oracleTerminal, ConDecision.stepChildren, List.not_mem_nil] at hsc
    · have hchild_adv : p.conState.layer < sc.child.layer := by rw [hchild]; omega
      by_cases h2 : widthMinUpto d (p.conState.layer + 1) ≤ p.conState.cleared
      · have hpos' := widthMinUpto_pos hpos (p.conState.layer + 1); omega
      · exfalso
        have hlive : p.conState.layer < N := not_le.mp h1
        have hcap : p.conState.cleared < layerCap d :=
          lt_of_lt_of_le (not_le.mp h2) (widthMinUpto_le_layerCap d _)
        have hkeep : sc.child.layer = p.conState.layer := by
          rcases hmin : ((List.finRange p.conState.numDiv).filterMap (fun k =>
              if p.conState.cleared + 1 ≤ p.conState.divTilde k ∧
                  p.conState.divTilde k + 1 ≤ widthMinUpto d p.conState.layer
              then some (p.conState.divTilde k) else none)).min? with _ | target
          · have horacle : conOracle d p.conState = case2Decision d p.conState
                (widthMinUpto d p.conState.layer - p.conState.cleared)
                (d ⟨p.conState.layer + 1, by omega⟩ - p.conState.cleared) hcap := by
              unfold conOracle; rw [dif_neg h1, dif_neg h2]
              split <;> simp_all only [reduceCtorEq]
            rw [horacle] at hsc
            simp only [case2Decision, ConDecision.stepChildren, List.mem_singleton] at hsc
            simp only [hsc, ConState.stepAppendAdvance]
          · rcases hf : chooseMin p.conState target with _ | f
            · exfalso
              have horacle : conOracle d p.conState = oracleTerminal d p.conState := by
                unfold conOracle; rw [dif_neg h1, dif_neg h2]
                split <;> simp_all only [reduceCtorEq, Option.some.injEq]
                all_goals (try subst_vars)
                all_goals (try (split <;> simp_all only [reduceCtorEq, Option.some.injEq]))
              rw [horacle] at hsc
              simp only [oracleTerminal, ConDecision.stepChildren, List.not_mem_nil] at hsc
            · obtain ⟨hmemtar, hminle⟩ := List.min?_eq_some_iff'.mp hmin
              rw [List.mem_filterMap] at hmemtar
              obtain ⟨k0, _, hk0⟩ := hmemtar
              have htar : p.conState.cleared + 1 ≤ target ∧
                  target + 1 ≤ widthMinUpto d p.conState.layer := by
                by_cases hc0 : p.conState.cleared + 1 ≤ p.conState.divTilde k0 ∧
                    p.conState.divTilde k0 + 1 ≤ widthMinUpto d p.conState.layer
                · rw [if_pos hc0] at hk0
                  have hdt : p.conState.divTilde k0 = target := Option.some.inj hk0
                  omega
                · rw [if_neg hc0] at hk0; exact absurd hk0 (by simp)
              have htgt : p.conState.divTilde f = target := (chooseMin_spec p.conState target hf).1
              have horacle : conOracle d p.conState = case1Decision d p.conState f
                  (target - p.conState.cleared) (widthMinUpto d p.conState.layer - p.conState.cleared)
                  (d ⟨p.conState.layer + 1, by omega⟩ - p.conState.cleared)
                  (not_le.mp h1) (by omega) (by rw [htgt]; omega) hcap := by
                unfold conOracle; rw [dif_neg h1, dif_neg h2]
                split <;> simp_all only [reduceCtorEq, Option.some.injEq]
                all_goals (try subst_vars)
                all_goals (try (split <;> simp_all only [reduceCtorEq, Option.some.injEq]))
              rw [horacle] at hsc
              simp only [case1Decision, ConDecision.stepChildren, List.mem_cons,
                List.not_mem_nil, or_false] at hsc
              rcases hsc with h | h <;>
                simp only [h, ConState.stepCase11, ConState.stepAppendAdvance]
        omega

(Opens needed: `DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine`. `List.min?_eq_some_iff'` is deprecated →
`List.min?_eq_some_iff` but still works.)

## Gap-B homogeneity round (2026-07-22, post-WAKE; branch merged canonical 72e96304f)

LANDED + PUSHED (`MultiAffineHomogWire.lean`, axiom-clean `[propext, Classical.choice, Quot.sound]`):
- `homogeneousDeg1On_comp_of_fixing` (step helper) — support-fixing σ preserves `HomogeneousDeg1On`;
  AffineOn half mirrors `deg1_comp_of_fixing`, vanishing half rides `hfix`.
- `coreGen_layerHomogeneous'` (BASE atom, the genuinely-new math) — isolate `A_ℓ` in `mult` via a
  double `Core.submult_comp` (`mult = M·A_ℓ·R`, M/R via `submult_congr` read layers ≠ ℓ), so `coreGen`
  is a linear form `∑ coeff·(A_ℓ entry)`; reindex the layer-ℓ double sum onto `layerCoords` with a
  `bcoeff x u := ∑ p, if enc p = x then coeff p u else 0` + `Finset.sum_ite_eq`/`sum_comm` (needs only
  `enc` maps INTO layerCoords — no bijection). Helpers: `canonFlatten_apply` (rfl), `submult_congr`
  (interval congruence, Fin.induction), `agree_on_layerCoords_of_agree_off`. Codex xhigh validated the
  route (`codex/coreGen-homog-{prompt,answer}.md`).
- Clash reconcile: retired the old in-file `realBranch_appendResidDescent`; `descent_delta1_append`
  + `realBranch_multiAffine_step'` (both hpos-threaded) consume the canonical cap; `step'` still routes
  its sole `sorryAx` through the frontier cap. `MultiAffineStepWire` green.

OPEN — `foldResid_layerHomogeneous'` (induction), pending controller call (see the two findings I sent):
- **FINDING 1 (hpos gap).** Baked `foldResid_layerHomogeneous` LACKS `hpos`, unlike siblings
  `realBranch_multiAffine_step`/`realBranch_appendResidDescent`. Without it, δ=1 rollover is reachable
  (`widthMinUpto=0` needs some `d k=0`; `widthMinUpto_pos` requires hpos) and rollover's pivot is
  UNCONSTRAINED (`canonPivotOf=none`), so the δ=1 step map `blockBlowupCoordQuot pv` can set a
  layer-ℓ coord to 1, defeating the pivot-below-threshold mechanism. Statement still TRUE (zero-width
  ⟹ `mult≡0` ⟹ `foldResid≡0`), but the intended proof needs hpos (kills δ=1 rollover, as
  `realBranch_multiAffine_step'` does). RECOMMEND adding hpos. Trace: `d=![1,0,1,1]`.
- **FINDING 2 (N_p timing).** The induction STEP consumes `foldResid` δ=1 + `IsRealBranch` shear
  conjuncts — exactly what the N_p re-bake (tasks #27-30) is re-authoring now, and where
  comp_of_fixing→comp_of_linear shifts. Building the step now is likely throwaway. RECOMMEND: build
  the induction AFTER N_p lands, with hpos, writing the correct step once.

INDUCTION DESIGN (for whoever finishes it): raw `TreePath` induction (pattern = `foldG_eq_pathMap`),
region `= univ` via `foldRegion_eq_univ`. Root = `coreGen_layerHomogeneous'`. Step: unfold `foldResid`
on the raw `.step` (dif_neg non-term; if δ), get `foldResid p' (cast j) ∘ σ`; apply
`homogeneousDeg1On_comp_of_fixing` with IH (thresholds: `supportLayerOf(parent) ≤ supportLayerOf(child)
≤ ℓ`, all σ-moved coords at layers ≤ p'.layer < ℓ). δ=0/case11/append derive hfix/hagree from the raw
`IsRealBranch` conjuncts (ShearWithinCarveRaw is the 3rd conjunct; center pin via
`canonCenterOf_decode_layer_le`; case11 pivot via `case11_pivot_decode_lt`). δ=1 rollover: kill via hpos
(`widthMinUpto_pos`) OR zero-width `mult≡0`.
