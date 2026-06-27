<task>
I am formalising in Lean 4 + Mathlib v4.29 the FINAL rung of the "locally trivial bundle" content of
Lehalleur–Rimányi Lemma 4.6 for the DLN multiplication-map fibre. I need you to adjudicate the
CLEANEST CORRECT formulation of the transition cocycle, and whether it earns the name `locallyTrivial`,
BEFORE I build ~300-600 LoC. The tower has repeatedly revealed further rungs; be skeptical.

WHAT IS ALREADY BUILT (sorry-free, axiom-clean), all over a fixed dim vector d : Fin (N+2) → ℕ,
field k, [Infinite k], rank r:

- `sweepSigmaRing k d r` = O(Σ^r) = MvPolynomial (RepCoord d) k ⧸ vanishingIdeal(sweepSigma) — the
  chart-closure coordinate ring (the BASE of the bundle, the rank-=r product locus's coord ring).
- For each pivot (s,t) (injective row/col selectors into Fin (d last) / Fin (d 0)), with permutations
  σ,τ carrying the first r indices to s,t: `chartDsigAt d r s t : sweepSigmaRing k d r` is the class of
  the (s,t) deep minor. The top-left case is `chartDsig`.
- `gaugeEquivSigma d r (pivotGauge σ τ) : sweepSigmaRing ≃ₐ[k] sweepSigmaRing`, a k-algebra
  AUTOMORPHISM of the base ring, with `gaugeEquivSigma (pivotGauge σ τ) chartDsig = chartDsigAt s t`.
- `chartLocalizedAlgEquivAt … : Localization.Away (chartDsigAt s t) ≃ₐ[k] Localization.Away (chartGfib)`
  — the per-pivot trivialization e_{s,t}, defined as
  `(awayCongr (gaugeEquivSigma (pivotGauge σ τ)) chartDsig (chartDsigAt s t)).symm ≪≫ e_β`,
  where `e_β = chartLocalizedAlgEquiv : Away chartDsig ≃ₐ Away chartGfib` is the deep chart (top-left),
  and `awayCongr e a b (hb : e a = b) : Away a ≃ₐ Away b` is the localization transport of an AlgEquiv.
  ALL pivots land in the SAME `Away chartGfib`.
- `perPivotLocalTrivializationDatum` — a genuine LocalTrivializationDatum (an `≃ₐ[k]` to
  `SchurLoc ⊗_k sweepFibreRing`) at EVERY pivot.

ALSO BANKED (thread 19, `FibreBundleTransition.lean`), abstract over ANY CommRing R and f g : R:
- `awayOverlap f g := Localization.Away (algebraMap R (Localization.Away f) g)` — both `awayOverlap f g`
  and `awayOverlap g f` are `IsLocalization.Away (f*g) R`.
- `awayOverlapTransition f g : awayOverlap f g ≃ₐ[R] awayOverlap g f` (= `IsLocalization.algEquiv`),
  with cocycle laws `_commutes`, `_symm`, `_trans_symm`, and `awayTriple_cocycle` (triple overlap
  composite = id). These hold by localization initiality (`IsLocalization.algHom_subsingleton`).
- Instantiated at the AMBIENT cover: `detMinorPoly s t : MvPolynomial (Fin p × Fin q) k` and
  `minorChartTransition` = `awayOverlapTransition (detMinorPoly s t) (detMinorPoly s' t')` over the
  AMBIENT single-matrix coordinate ring `MvPolynomial (Fin p × Fin q) k`.

KEY STRUCTURAL OBSERVATION (the crux of my question): my per-pivot charts are all localizations of the
SAME base ring `sweepSigmaRing` at the elements `chartDsigAt s t`. So the transition on the double
overlap between chart (s,t) and chart (s',t') is between two localizations of `sweepSigmaRing` at
`powers (chartDsigAt s t * chartDsigAt s' t')` — which is EXACTLY the abstract `awayOverlapTransition`
instantiated at `R = sweepSigmaRing`, `f = chartDsigAt s t`, `g = chartDsigAt s' t'`. The cocycle laws
come for free from the banked engine.

The team lead's framing asks me to identify `e_{s,t} ∘ e_{s',t'}⁻¹` (restricted to the overlap) with
the AMBIENT `awayOverlapTransition` over `MvPolynomial (Fin p × Fin q) k`. But my charts live over
`sweepSigmaRing` (the QUOTIENT, a DIFFERENT ring than the ambient `MvPolynomial (Fin p × Fin q) k`).
</task>

<output_contract>
Answer terse, in these sections:

1. WHAT DOES `locallyTrivial` ACTUALLY DEMAND HERE? For an affine fibre bundle presented as: a base
   ring B (= sweepSigmaRing), an open cover by principal opens D(g_i) (g_i = chartDsigAt at the pivots),
   and per-chart trivializations `Away g_i ≃ₐ[k] (localized base direction) ⊗ Fibre` — what is the
   PRECISE cocycle/coherence condition that makes this "locally trivial"? Is it (a) the transitions
   between the per-chart trivializations on overlaps form a cocycle valued in the structure group /
   are B-algebra isos respecting the base, or (b) something stronger? State the minimal honest
   condition.

2. IS THE RIGHT COCYCLE OVER `sweepSigmaRing` (the base) OR OVER THE AMBIENT `MvPolynomial`? Given my
   charts are localizations of `sweepSigmaRing`, is the team lead's "identify with the ambient
   `awayOverlapTransition` over `MvPolynomial (Fin p × Fin q) k`" actually REQUIRED for `locallyTrivial`,
   or is it a RED HERRING — the genuine transition cocycle being the one over `sweepSigmaRing`
   (instantiating the banked abstract engine at R = sweepSigmaRing, f,g = chartDsigAt …)? The ambient
   `MvPolynomial (Fin p × Fin q) k` is the AMBIENT MATRIX SPACE coord ring (target of mult), NOT the
   base `sweepSigmaRing`. Adjudicate: does `locallyTrivial` need the cross-ring (ambient) identification,
   or only the base-side (sweepSigmaRing) cocycle?

3. THE CHEAPEST CORRECT LEAN HEADLINE. Give the exact statement(s) to prove. I expect something like:
   (i) define `chartOverlapTransition (s t) (s' t') := awayOverlapTransition (chartDsigAt s t)
       (chartDsigAt s' t')` over sweepSigmaRing — INSTANT from the banked engine;
   (ii) show this transition INTERTWINES the two per-pivot trivializations restricted to the overlap,
       i.e. `e_{s',t'} ∘ (transition) = e_{s,t}` on the overlap (the genuine coherence — does this hold,
       and is it cheap given e_{s,t} = awayCongr.symm ≪≫ e_β with the SAME e_β?).
   For (ii): since both e_{s,t} and e_{s',t'} factor through the SAME e_β after the gauge transports,
   does the e_β CANCEL, reducing the coherence to a statement purely about the gauge localization
   transports `awayCongr (gaugeEquivSigma (pivotGauge σ τ))`? Is that cancellation real and does it
   make (ii) cheap or is there a subtlety (the gauges P_{st} ≠ P_{s't'} are different automorphisms)?

4. THE HONEST `locallyTrivial` HEADLINE — what to name it and what it must bundle. Can I assemble
   cover (proven, #18) + per-pivot trivializations (#22) + this cocycle into ONE `…locallyTrivial…`
   definition/theorem? What is the right Lean SHAPE (a structure? a Prop? a record bundling the datum
   family + the coherence)? Or is `locallyTrivial` in the algebraic-geometry sense NOT capturable as a
   single clean Lean object here, so the honest deliverable is the cocycle + a documented assembly?

5. HIDDEN FURTHER RUNG. Name the single most likely place THIS reveals yet another rung (e.g. the
   intertwining (ii) failing without an extra compatibility, or the gauge `pivotGauge` not being
   canonical so the transition depends on the choice of σ,τ). Be specific.
</output_contract>

<grounding_rules>
Distinguish what you can PROVE from the setup vs what you INFER about my Lean encoding (you can't see
the files). Flag where you're guessing. If the team lead's "ambient identification" framing is a red
herring (the base-side cocycle being the genuine content), say so plainly — I would rather build the
correct cheaper thing than the lead's literal-but-wrong target. If the intertwining (ii) is the real
content and it's NOT automatic, tell me what compatibility it needs.
</grounding_rules>
