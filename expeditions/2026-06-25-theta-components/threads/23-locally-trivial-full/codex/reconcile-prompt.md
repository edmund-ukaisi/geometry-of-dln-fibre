<task>
Resolve a framing conflict before I spend ~300-600 LoC. Decisive answer needed.

STATE (Lean 4, sorry-free, axiom-clean), Lehalleur–Rimányi Lemma 4.6 fibre bundle over rank-=r locus:
- BASE: `sweepSigmaRing = O(Σ̄^r)` = MvPolynomial(RepCoord d)/vanishingIdeal(Σ^r) = coord ring of the
  CLOSURE of the rank-=r product locus.
- I have an assembled `PivotLocalProductAtlas` over sweepSigmaRing: per-pivot trivializations
  `chartLocalizedAlgEquivAt : Away(chartDsigAt s t) ≃ₐ SchurLoc ⊗ sweepFibreRing`, the BASE-SIDE
  overlap cocycle `chartOverlapTransition I J := awayOverlapTransition (chartDsigAt I)(chartDsigAt J)`
  over sweepSigmaRing (with laws), the intertwining (transition factors through base gauges), and the
  POINT-SET cover `sweepSigma_subset_chartOpen` (∀ x ∈ Σ^r ∃ pivot, IsUnit(eval x ΔPdeepAt)).
- SEPARATELY BANKED (thread 18/19): the AMBIENT cover of `Mat^{=r}` (the rank-=r MATRIX locus, target
  of mult) by `minorChart s t = {M | (M.submatrix s t).det invertible}`
  (`rankEqLocus_eq_iUnion_inter_minorChart`), and the ambient cocycle `awayOverlapTransition` over the
  AMBIENT ring `MvPolynomial (Fin p × Fin q) k` (= O(Mat), the matrix space, NOT sweepSigmaRing).

TWO PRIOR CODEX CONSULTS (yours, decorrelated) established:
(A) the ambient-MvPolynomial identification is a RED HERRING for local triviality — the genuine cocycle
    is base-side over sweepSigmaRing;
(B) `span {chartDsigAt} = ⊤` over sweepSigmaRing = O(Σ̄^r) is FALSE (closure has rank-<r points where
    all r×r minors vanish); the charts cover only the OPEN rank-=r locus; the residual to a bare
    scheme-theoretic locallyTrivial is `span=⊤` over the rank-=r OPEN localization.

THE CONFLICT. My team lead insists (re-assignment) on the ORIGINAL target: "restrict two per-pivot
charts to the double overlap and identify the restricted composite e_{s,t}∘e_{s',t'}⁻¹ with the AMBIENT
`FibreBundleTransition.awayOverlapTransition`" (~300-600 LoC, "comparing two localization presentations
over different coordinate rings"). This is the framing prior consult (A) called a red herring.

THE QUESTION I need resolved: is there a reading under which the lead's "ambient identification" is
actually the RIGHT next step — namely, does identifying my base-side charts with the AMBIENT
`Mat^{=r}` charts let me PULL BACK the ambient cover (rankEqLocus_eq_iUnion_inter_minorChart, which is
over the rank-=r MATRIX locus) to get a genuine SCHEME-LEVEL cover of the rank-=r locus on the bundle
side — thereby supplying exactly the `span=⊤`-over-the-open residual from (B)? Or are these two
genuinely orthogonal (the ambient identification gives nothing toward the cover, and the cover residual
must be proved directly over the rank-=r open of sweepSigmaRing)?
</task>

<output_contract>
Terse, decisive:

1. ARE THEY THE SAME RUNG OR ORTHOGONAL? Does the lead's ambient cross-ring identification of the
   cocycles, IF BUILT, supply the scheme-level cover residual from (B)? Or is the cover residual a
   SEPARATE proof (span=⊤ over the rank-=r open of sweepSigmaRing) that the ambient identification does
   not touch? Be concrete about why.

2. WHAT ACTUALLY EARNS A `locallyTrivial`-FAMILY NAME, cheapest-first? Rank:
   (a) prove `span=⊤` over the rank-=r open localization of sweepSigmaRing directly (Nullstellensatz
       over the open: the r×r minors generate the unit ideal after inverting the rank-=r condition);
   (b) build the ambient cross-ring cocycle identification (the lead's target);
   (c) something else.
   Which is the genuine final rung, and does (b) contribute to it at all?

3. IS THE LEAD'S TARGET WORTH BUILDING regardless? Even if (b) is not needed for locallyTrivial, is the
   ambient cross-ring identification valuable (e.g. connects the base-side atlas to thread-18/19's
   ambient cover for exposition / for someone who wants the matrix-space picture)? Or is it busywork
   that should be declined in favour of (a)?

4. MY RECOMMENDED ACTION. Given I should not overclaim and should land what genuinely advances toward
   locallyTrivial: do I (i) build the scheme-level cover (a) and assemble a `locallyTrivialOnRankOpen`
   headline; (ii) build the lead's ambient identification (b); or (iii) report that the cocycle is done
   and the only real residual is (a), and build (a)? State the single best action.
</output_contract>

<grounding_rules>
You cannot see the files. Flag inference vs derivation. If the lead's target is genuinely orthogonal to
earning locallyTrivial (busywork), say so plainly — I will report that and build the real rung (a)
instead. If the ambient identification DOES supply the cover, say that too and I'll build it.
</grounding_rules>
