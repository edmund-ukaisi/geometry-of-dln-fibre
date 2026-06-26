<task>
Lean 4 + Mathlib v4.29. Prove: the number of top-dimensional minimal primes of a
multiplication-map fibre coordinate ring depends only on the rank of the target B.

LANDED ingredients:
(a) topDimMinPrimes_ncard_eq_of_ringEquiv (e : A ≃+* B) :
    (TopDimMinPrimes A).ncard = (TopDimMinPrimes B).ncard  -- ANY RingEquiv preserves the count
(b) topDimMinPrimes_quotient_radical_ncard_eq (J) :
    (TopDimMinPrimes (R⧸J)).ncard = (TopDimMinPrimes (R⧸J.radical)).ncard  -- radical-insensitive
(c) vanishingIdeal_image_fibre_eq_radical :
    vanishingIdeal k (canonicalCoord d '' fibre d B) = (fibreGenIdeal d B).radical
(d) vanishingIdeal_image_smul :
    vanishingIdeal k (canonicalCoord d '' ((P • ·) '' Z))
      = (vanishingIdeal k (canonicalCoord d '' Z)).comap (baseChangePullback P)
    where baseChangeAlgEquiv P : R ≃ₐ[k] R is the coordinate-ring automorphism of A ↦ P•A,
    and baseChangePullback P = (baseChangeAlgEquiv P).toRingHom.
(e) reducedFibre_baseChangeHomogeneous : for B.rank = r,
    ∃ P : BaseChangeGroup d, fibre d B = (fun A ↦ P • A) '' fibre d (normalForm …).
R = MvPolynomial (RepCoord d) k.

PLAN: take E = normalForm, B with B.rank = r. By (e) get P with fibre d B = (P•·) '' fibre d E.
Then:
  radical(fibreGenIdeal d B)
    = vanishingIdeal(canonicalCoord '' fibre d B)                         [(c) symm]
    = vanishingIdeal(canonicalCoord '' ((P•·)'' fibre d E))               [rewrite by (e)]
    = comap (baseChangeAlgEquiv P) (vanishingIdeal(canonicalCoord '' fibre d E))  [(d)]
    = comap (baseChangeAlgEquiv P) (radical(fibreGenIdeal d E))           [(c)]
So radical(fibreGenIdeal d B) = comap φ (radical(fibreGenIdeal d E)), φ = baseChangeAlgEquiv P RingEquiv.
Then R⧸radical(fibreGenIdeal d B) = R ⧸ comap φ J_E ≃+* R ⧸ J_E via Ideal.quotientEquiv
(needs J_E = (comap φ J_E).map φ, true since φ equiv). Apply (a) to the radical quotients,
then strip radicals by (b) on both sides.
Conclusion: numTop(R⧸fibreGenIdeal d B) = numTop(R⧸fibreGenIdeal d E).
</task>

<output_contract>
Three short numbered answers:
(1) Does the RingEquiv ⟹ equal-TopDimMinPrimes-count step need any properness / "no-drop"
    argument, or is the bare RingEquiv between the two QUOTIENT rings enough? (Both are genuine
    finitely-generated k-algebras; no localization in this step.)
(2) Is Ideal.quotientEquiv the right gluing lemma here; is `map φ (comap φ J) = J` the cleanest
    hypothesis discharge, and which Mathlib lemma name (Ideal.map_comap_of_equiv vs others)?
(3) Any universe / Fin(N+2)-vs-Fin(N+1) indexing trap, or any other concrete gap. Flag actual gaps.
Be terse.
</output_contract>

<grounding_rules>
Flag inference vs certainty. If a Mathlib lemma name is a guess, say so.
</grounding_rules>
