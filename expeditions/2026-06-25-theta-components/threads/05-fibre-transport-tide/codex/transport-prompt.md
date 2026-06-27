<task>
Lean 4 / Mathlib v4.29 formalisation. I am transporting a PROVED top-dimensional-component
count from a determinantal locus Σ̄^r to a fibre mult⁻¹(E), via an existing chart isomorphism.
I need a decorrelated read on the CLEANEST route and the realistic scope (is this one tide or
several?).

SETTING (concrete objects, all in a working library):
- R = MvPolynomial (RepCoord d) k, k an algebraically closed field of char 0.
- Σ̄^r locus has aggregate ideal `sigmaIdeal d r` (radical, = vanishingIdeal of the rank-≤r locus).
  Its top-dim components are PROVED counted: `topComponents d r` := minimal primes of `sigmaIdeal`
  of minimal height (= cCodim d r); and `numTop d r = #topComponents` is PROVED unconditionally.
- Fibre over the rank-r normal form E=diag(I_r,0): ideal `fibreGenIdeal d E = span{multPoly r c - C(E r c)}`,
  with `vanishingIdeal(fibre) = radical(fibreGenIdeal)` (Nullstellensatz, proved).
- ENTRY LEMMA just proved: in R/fibreGenIdeal, the deep pivot minor detΔ = ΔPdeep d r is ≡ 1
  (a UNIT) — `ΔPdeep_sub_one_mem_fibreGenIdeal`. So localizing R/fibreGenIdeal at detΔ changes nothing.
- THE EXISTING CHART (built for a CODIMENSION result, used via ringKrullDim only):
  `e : Localization.Away dsig ≃ₐ[k] Localization.Away gF`  (an AlgEquiv = k-algebra iso), where
    * dsig = class of detΔ (ΔPdeep) in O(Σ^r) = R/vanishingIdeal(Σ^r);  Away dsig = (O(Σ^r))[1/detΔ].
    * gF lives in `MvPolynomial (SchurVar) (O(F))`, O(F) = R/vanishingIdeal(fibre);
      Away gF = (O(F)[SchurVar...])[1/detSchurS], where SchurVar is a FINITE index set of |δ| extra
      polynomial variables (the affine H-stratum from block-triangular structure).
  So e's fibre side carries an EXTRA polynomial extension by |δ| variables AND a localization.

GOAL: prove `#topComponents(fibre d E) = #topComponents(Σ̄^r d)` (a cardinality of two sets of minimal
primes of minimal height), where topComponents(fibre) is defined analogously (min primes of fibreGenIdeal
of minimal height). The combinatorial side `#topComponents(Σ̄^r) = cTheta(d-r)` is already proved.

MATHLIB BRICKS AVAILABLE (confirmed present at v4.29):
- IsLocalization.orderIsoOfPrime (primes of localization ↔ primes of ring not meeting the monoid)
- IsLocalization.minimalPrimes_map / minimalPrimes_comap (minimal primes under localization)
- Ideal.minimalPrimes.equivIrreducibleComponents
- RingEquiv.height_comap (height transport under ring iso)
- Polynomial / MvPolynomial minimal-primes correspondence: UNSURE what exists. I know
  Ideal.height under polynomial extension; need to check `minimalPrimes (P.map C) = (minimalPrimes P).image`
  type results for MvPolynomial over a general (non-domain) base.

KEY DIFFICULTY: the fibre side of e is NOT O(F) directly — it is O(F) tensored-up by |δ| poly variables
and localized. So transporting through e gives min primes of (O(F)[SchurVar])[1/detSchurS], and I must
then descend the count to min primes of O(F) itself (hence fibreGenIdeal). The height also shifts by |δ|
across the polynomial extension. The COUNT should be preserved (poly extension is a bijection on minimal
primes; min-height components correspond), but each step is a real lemma.
</task>

<output_contract>
1. ROUTE: the cleanest chain of Lean lemmas to get from #topComponents(fibre) to #topComponents(Σ̄^r),
   step by step, naming the Mathlib or hand-built lemma for each arrow. Be explicit about the
   polynomial-extension descent step (the minimal-primes-of-R[X]-over-non-domain-R correspondence) —
   is there a clean Mathlib lemma, or must it be hand-built, and how?
2. The "TOP = minimal height" matching across the |δ|-shift and the localization: how to keep it a
   COUNT-preserving correspondence cleanly (do I even need heights, or can I phrase top via an order-iso
   of the minimal-prime posets + a height predicate transported by RingEquiv.height_comap)?
3. SCOPE verdict: is this realistically ONE focused tide (≤ ~400 LoC, a few lemmas) or does the
   polynomial-extension + localization + height-matching make it a multi-module sub-project? If the
   latter, what is the SINGLE cleanest correct-statement intermediate theorem to land now (with the rest
   as a precisely-stated sorry), so a successor tide can finish it?
4. Any CHEAPER reformulation I'm missing — e.g. defining topComponents(fibre) directly as the image
   under e of topComponents(Σ̄^r-localized), or counting via an OrderIso of posets rather than heights,
   that sidesteps the polynomial-extension descent entirely.
</output_contract>

<grounding_rules>
Flag clearly which Mathlib lemma names you are CONFIDENT exist at v4.29 vs which you are INFERRING /
guessing (I will verify before use). Distinguish a genuine mathematical obstruction from a mere
Lean-plumbing cost. If a step is mathematically false as I've stated it, say so.
</grounding_rules>
