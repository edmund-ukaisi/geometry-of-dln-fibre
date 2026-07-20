# Decorrelated adjudication: is an EXISTENTIAL child-read in StepRel sufficient, or does it need a per-divisor embedding?

You are an independent reviewer. Judge one sharp question about a Lean 4 skeleton (blueprint forecast,
holes allowed) that certifies Aoyagi's resolution of the deep-linear-network multiplication-map
singularity. I want a verdict with a concrete counterexample if you find one, not reassurance.
Distinguish what you INFER from what you can assert as fact.

## The setup

The engine's sole downstream output is `∀ M, RouteMBoxThresholdFinite M`: the parameter-box integral
`∫_{box} frobSq(prod M A)^{−c'}` is finite for every `c' < ½·minAdm M`, where `minAdm M` is defined
INDEPENDENTLY (banked) as `min` over admissible rank profiles `T ∈ Adm M` of `Mval M T` (the geometric
codimension). RLCT = ½·codim.

A `CanonicalResolution M t` bundles these conjuncts on a resolution tree `t`:
1. `IsFullMonomialization t`: `∀ leaf l, ∀ k, l.divExp k = (Mval M (l.divProfile k)).toNat ∧
   l.divProfile k ∈ Adm M`.
2. `∀ (n,e) ∈ stepEdges t, StepRel n e`  (the per-step invariant — SEE BELOW).
3. branch-rooted base `S=J=0`.
4. `ChartBridge M t`: an upstairs-open image cover of the zero-locus by `⋃ leaf, chartMap '' srcBox`,
   plus per-leaf a.e.-injectivity, injective/disjoint `divCoord`/`resCoord`, `LeafPullback`,
   `LeafJacobian`, and coherence (`chartMap` = fold of edge substitutions).
5. exponent hooks: `∀ e ∈ terminalExponents t, minAdm M ≤ e` AND `minAdm M ∈ terminalExponents t`,
   where `terminalExponents t` = flatMap over EMITTED leaves of `(their divExp values) ++ (resRank if
   >0)`.
6. live attainment: `∃ leaf l, l.srcBox.Nonempty ∧ minAdm M ∈ (l.divExp values)`.

`monomialization_terminates : ∃ t, CanonicalResolution M t` is a SORRIED hole (the construction tide
proves it). The finiteness theorem is:

```
engine_box_threshold_finite M : RouteMBoxThresholdFinite M :=
  fun c' hc' => region_glue M (coverage_theorem M) c' (fun e he =>
     -- from exponent_ledger_bridge: minAdm M ≤ e, and hc' : c' < minAdm/2, so c' < e/2
     ...)
```

where `region_glue (hbridge : ChartBridge …) (hrat : ∀ e ∈ terminalExponents, c' < e/2) :
box_integral < ⊤` is the other sorried hole (analytic assembly). **KEY STRUCTURAL FACT:**
`engine_box_threshold_finite` consumes ONLY `region_glue` (needs `ChartBridge` + `hrat`) and
`exponent_ledger_bridge` (the `minAdm ≤ e` / `minAdm ∈ terminalExponents` facts). It does NOT consume
`StepRel` / `case_step_invariant` at all.

## The StepRel definition under review

`StepRel n e` (n = parent node, e = one outgoing edge; the edge carries `case`, `subst.runLen`, and
`child` — a subtree whose root ledger is read via `rootNumDiv`/`rootDivExp`/`rootCleared`):

```
(e.case = case2 →
    (∃ kp : Fin n.numDiv, ∀ g, kp ∈ n.support g) ∧
    (∃ kc : ℕ, kc < rootNumDiv e.child ∧ rootDivExp e.child kc = n.resRows * n.resCols)) ∧
(e.case = case11 →
    ∃ kp : Fin n.numDiv, n.divTilde kp = n.cleared ∧
      ∃ kc : ℕ, kc < rootNumDiv e.child ∧
        rootDivExp e.child kc = n.divExp kp + e.subst.runLen * n.resCols) ∧
(e.case = case12 →
    rootCleared e.child = n.cleared + 1 ∧ 0 < rootNumDiv e.child)
```

The child read is an EXISTENTIAL: "SOME child divisor `kc` has the merged/codim exponent". It is NOT a
per-parent-divisor embedding `Fin n.numDiv ↪ Fin (child).numDiv`, and NOT a stable-divisor-id read.
So it leaves the OTHER child divisors and the child's `support` (sharing) map unconstrained, and does
not identify WHICH child divisor is the updated one.

## Background: the sharing-mistrack kill-condition

A separate battery (`g-coverage-sharing-killcond`) shows: at corank ≥ 2, MIS-TRACKED divisor-sharing
invents a spurious LOW-ratio divisor — e.g. `⟨δx, δy⟩` (shared δ) has rlct = ½ vs `⟨δ₁x, δ₂y⟩`
(unshared) has rlct = 1, identical "light" data, different value. Fork 3 of the expedition makes the
divisor-support (sharing) map mandatory typed data precisely because flattening it changes the RLCT.
Note: in the current bundle, `support` (the sharing map) is read ONLY by `StepRel`'s case-2 clause; it
is NOT read by `LeafPullback`/`LeafJacobian`/`ChartBridge`/`terminalExponents`/`IsFullMonomialization`.

## The questions

**Q1.** Given that `engine_box_threshold_finite` (the finiteness certificate) does NOT consume
`StepRel`, and its soundness rests on: `minAdm` banked as the true `min` over `Adm M`; the exponent
hooks forcing every terminal exponent `≥ minAdm` and `minAdm` attained; `IsFullMonomialization`
forcing every terminal exponent `= Mval(admissible profile)`; and `ChartBridge` forcing a genuine
cover — is the EXISTENTIAL child-read in `StepRel` SUFFICIENT for the certificate's SOUNDNESS (the
finiteness result)? Or can you exhibit a tree `t` satisfying the FULL `CanonicalResolution` bundle
(all six conjuncts, with the existential StepRel) for which the finiteness conclusion `box_integral <
⊤ for c' < ½·minAdm` is FALSE — i.e. a genuine soundness break traceable to StepRel's weakness?

**Q2.** Can MIS-TRACKED sharing (a corrupted `support` map, or a child whose sharing is wrong) satisfy
the full bundle and thereby (a) make `minAdm ∈ terminalExponents` hold with the WRONG (too large)
minimum — hiding a genuine smaller-ratio divisor — so that `region_glue` claims finiteness for a `c'`
where the true integral diverges? Trace whether the guard against an untracked smaller-ratio divisor
is `StepRel` (weak here) or `ChartBridge` + `IsFullMonomialization` + banked `minAdm` (independent of
StepRel). Is the corank-≥2 `⟨δx,δy⟩`-vs-`⟨δ₁x,δ₂y⟩` obstruction reachable through this bundle?

**Q3.** Separately from soundness: for the FIDELITY claim "this tree is a faithful Aoyagi resolution"
(the map node `case-step-lemmas` flipping to validated), does the existential suffice, or is the
per-divisor embedding needed to prevent a tree that has the merged exponent at some index but corrupts
the other divisors / the sharing? State clearly whether this is a soundness issue or only a
construction-fidelity nicety.

**Q4.** If you judge the existential insufficient for EITHER soundness or the certificate's stated
purpose, give the minimal strengthening (per-divisor embedding? a `support`-propagation clause? tie
`minAdm ∈ terminalExponents` to the live-attainment leaf's profile?) and the concrete tree that breaks
the current form.
