<task>
I am a fidelity reviewer auditing a Lean 4 / Mathlib formalisation (commutative-algebra localization
theory). I need an independent soundness read on a "naturality" claim. Judge the MATH, flag any
inference vs. fact.

SETUP (all rings commutative, over a base field k; Base a k-algebra; M a fixed model k-algebra):
- A chart is (chartElt : Base, trivK : Localization.Away chartElt ≃ₐ[k] M).
- For charts C,D: overlapElt C D = image of D.chartElt in Away(C.chartElt). Its Away is
  awayOverlap(C.chartElt, D.chartElt), = localization of Base at powers(C.chartElt * D.chartElt)
  (via IsLocalization.Away.mul').
- targetChartLoc C D = Away( C.trivK(overlapElt C D) )  [model M localized]; overlapTriv C D is the
  awayCongr' transport of C.trivK, an iso awayOverlap(C,D) ≃ₐ[k] targetChartLoc C D.
- The 2-fold transition overlapTransition C D : targetChartLoc C D ≃ₐ[k] targetChartLoc D C is
  (overlapTriv C D).symm ≫ (chartOverlapTransitionK C D) ≫ (overlapTriv D C), where
  chartOverlapTransitionK is the k-restriction of the canonical Base-algebra localization iso
  awayOverlapTransition(C.chartElt, D.chartElt) between awayOverlap(C,D) and awayOverlap(D,C).
- tripleElt C D E = image of (D.chartElt * E.chartElt) in Away(C.chartElt); Away(tripleElt C D E) =
  localization of Base at powers(C.chartElt * D.chartElt * E.chartElt) (any reorder, via mul' +
  Away.of_associated). targetTripleLoc C D E = Away( C.trivK(tripleElt C D E) ).

THE CLAIM (P2.g naturality). We define:
1. chartOverlapTripleBase C D E : Away(tripleElt C D E) ≃ₐ[Base] Away(tripleElt D C E)  :=
   IsLocalization.algEquiv at powers(C.chartElt*D.chartElt*E.chartElt) (both are localizations of
   Base at that submonoid). [BASE-algebra iso, at the triple submonoid.]
2. tripleReorderBase C D E : Away(tripleElt D C E) ≃ₐ[Base] Away(tripleElt D E C) := awayCongr' of
   AlgEquiv.refl on Away(D.chartElt), carrying tripleElt D C E ↦ tripleElt D E C, proof obligation
   discharged by mul_comm (C.chartElt * E.chartElt = E.chartElt * C.chartElt).
3. baseRestrTriple C D E : awayOverlap(C.chartElt,D.chartElt) →ₐ[Base] Away(tripleElt C D E) :=
   IsLocalization.liftAlgHom at powers(C.chartElt*D.chartElt), lifting Algebra.ofId Base
   Away(tripleElt C D E); units-check: powers(C·D) are units because C·D·E is the localizing unit and
   C·D divides C·D·E. [The genuine "further localization at E" of the 2-fold overlap.]
4. restrictTriple C D E : targetChartLoc C D →ₐ[k] targetTripleLoc C D E := conjugate baseRestrTriple
   through (overlapTriv C D).symm and (tripleTriv C D E), k-restricted.
5. restrictedOverlapTripleTransition C D E : targetTripleLoc C D E ≃ₐ[k] targetTripleLoc D C E :=
   conjugate (chartOverlapTripleBase C D E) through tripleTriv (built like overlapTransition).

Proved theorems (all axiom-clean, build green):
(A) baseRestr_square: (baseRestrTriple D C E) ∘ (awayOverlapTransition C.chartElt D.chartElt)
      = (chartOverlapTripleBase C D E) ∘ (baseRestrTriple C D E)
    as Base-algebra maps awayOverlap(C,D) →ₐ[Base] Away(tripleElt D C E). Proof: BOTH are Base-algebra
    maps OUT of awayOverlap(C,D) (= loc of Base at powers(C·D)), so equal by
    IsLocalization.algHom_subsingleton at powers(C·D).
(B) restrictTriple_comp_overlapTransition: (restrictTriple D C E) ∘ (overlapTransition C D)
      = (restrictedOverlapTripleTransition C D E) ∘ (restrictTriple C D E)
    as k-algebra maps targetChartLoc C D → targetTripleLoc D C E. Proof: unfold both restrictTriple
    applications + restrictedOverlapTripleTransition_apply, cancel an overlapTriv D C round-trip,
    reduce to baseRestr_square (pointwise). Key middle step: (overlapTriv D C).symm(overlapTransition
    C D x) = awayOverlapTransition C.chartElt D.chartElt ((overlapTriv C D).symm x) — by unfolding
    overlapTransition and cancelling overlapTriv D C.
(C) restrict_overlapTransition_eq_tripleTransition: (restrictedOverlapTripleTransition C D E) ≫
      (targetTripleReorder C D E) = tripleTransition C D E (the canonical triple transition).
    Proof: groupoid conjugation collapse to the k-restriction of
    (chartOverlapTripleBase C D E ≫ tripleReorderBase C D E = chartTripleTransitionBase C D E), which
    is itself a Base-subsingleton (algHom_subsingleton at powers(C·D·E)).

QUESTIONS:
Q1. Is baseRestr_square SOUND? Specifically: are BOTH composites genuinely Base-algebra maps out of
    the localization awayOverlap(C,D) at powers(C·D)? (awayOverlapTransition is a Base-algebra iso;
    baseRestrTriple is a Base-algebra map; chartOverlapTripleBase is a Base-algebra iso. The domain
    awayOverlap(C,D) is a localization of Base at powers(C·D).) Does algHom_subsingleton legitimately
    force equality here? Any hidden requirement (e.g. must the codomain be a Base-algebra, must the
    maps commute with algebraMap Base — do they, given they're all built as Base-algebra maps)?
Q2. Does (B) genuinely exhibit restrictedOverlapTripleTransition as the further-localization of the
    ACTUAL overlapTransition (not merely of the canonical iso)? I.e. is the commuting square (B) the
    correct categorical statement of "restrictedOverlapTripleTransition = localize overlapTransition
    at E"? Note restrictTriple is a genuine localization/restriction map (liftAlgHom-based,
    conjugated), NOT an iso.
Q3. Prior Codex review of an EARLIER attempt flagged that doing the subsingleton OVER THE MODEL M
    would be UNSOUND (the maps aren't M-algebra maps). Confirm: the CURRENT route does the
    subsingleton over BASE (in baseRestr_square, chartOverlapTripleBase_trans_reorder), then
    transports to the target by pure AlgEquiv-groupoid conjugation (no subsingleton on M). Is that
    the correct fix, and is it sound?
Q4. Is the reorder (2) honest? awayCongr' of refl carrying tripleElt D C E ↦ tripleElt D E C: the
    proof obligation is refl(tripleElt D C E) = tripleElt D E C, i.e.
    algebraMap Base (Away D.chartElt) (C.chartElt*E.chartElt) =
    algebraMap ... (E.chartElt*C.chartElt), closed by mul_comm. Is this genuine commutativity of the
    two non-pivot chart elements, or does it smuggle an unjustified identification?
Q5. Overclaim check: docstrings now say "naturality is PROVED" and "R1 = GLOBAL gluing only remains".
    Given (A)(B)(C) are PER-TRIPLE compatibilities (commuting squares/cocycle for fixed C,D,E), is it
    an overclaim to say the R1 gap is closed EXCEPT for global gluing? Or is the per-triple naturality
    genuinely the correct local input, with only the gluing (patching per-chart projections into one
    morphism over U) remaining?
</task>

<output_contract>
Answer Q1-Q5 in order. For each: a one-word verdict (SOUND / UNSOUND / OVERCLAIM / FAITHFUL /
INCONCLUSIVE) then <=4 sentences. Flag explicitly any point where you are INFERRING from the
description vs. stating a mathematical fact. End with one line: the single biggest residual soundness
risk, if any.
</output_contract>

<grounding_rules>
You do NOT have the Lean source; reason from the mathematical description. Do NOT claim a Lean API
behaves a certain way unless it is a standard, well-known Mathlib fact (algHom_subsingleton,
liftAlgHom, IsLocalization.algEquiv, Away.mul'); if you're guessing at Lean behavior, say so. Judge
the MATHEMATICAL soundness of the argument structure.
</grounding_rules>
