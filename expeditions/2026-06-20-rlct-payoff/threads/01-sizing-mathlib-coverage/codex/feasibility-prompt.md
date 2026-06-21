<task>
You are a decorrelated second reviewer on a Lean 4 + Mathlib (v4.29.0) formalisation
expedition. We are sizing the Mathlib coverage that gates an expedition to formalise the
"RLCT payoff" of Lehalleur–Rimányi 2024 ("Geometry of the fibers of the multiplication map
of deep linear neural networks"). Adjudicate the FEASIBILITY VERDICT below; red-team it.

CONTEXT — what is already LANDED in the repo's engine (Lean, zero-sorry, [IsAlgClosed k][CharZero k]):
- Per-orbit GEOMETRIC codimension: codimRep(orbitRankLocus M) = orbitLinearCodim M = dim Ext^1(M,M)
  (Voigt's theorem, proved). codimRep Z := Ideal.height (MvPolynomial.vanishingIdeal (coord '' Z)),
  i.e. height of the vanishing ideal of the image under the canonical entry-flattening
  coord : Tuple d ≃ (RepCoord d → k).
- Orbit closures are irreducible + prime (engine predicate IsZariskiIrreducible Z :=
  IsIrreducible (pointToPoint '' Z) in PrimeSpectrum; equiv to vanishingIdeal Z prime).
- Abeasis–Del Fra Thm 3.8: orbitRankLocus M = Ō_M (closure of the orbit), proved set- and ideal-level.
- The combinatorial (C, θ): cCodim = min over Kostant partitions of codimForm; numTop = number of
  Kostant partitions attaining that minimum. Rank-shift Lemma 4.5 proved.
- cCodim_eq_inf_geomCodim: cCodim = min over partitions of the genuine geometric orbit-closure codim.
- Note: there is NO Zariski topology on the point space (σ → k) in Mathlib; the engine routes all
  irreducibility through pointToPoint into PrimeSpectrum (which DOES carry zariskiTopology).

MATHLIB COVERAGE I VERIFIED by #check (v4.29.0, all type-check):
- Half A (Σ^r geometry + components):
  * irreducibleComponents X = {s | Maximal IsIrreducible s}; irreducibleComponents_eq_maximals_closed.
  * isIrreducible_iff_sUnion_isClosed: an irreducible set covered by a finite collection of closeds is
    contained in one of them. (THE engine of "component of finite union = one piece".)
  * Ideal.minimalPrimes.equivIrreducibleComponents (I : Ideal R) :
      I.minimalPrimes ≃o (irreducibleComponents (zeroLocus I))ᵒᵈ   [CommSemiring]
    plus vanishingIdeal_irreducibleComponents, zeroLocus_minimalPrimes,
    zeroLocus_ideal_mem_irreducibleComponents.
  * PrimeSpectrum.zeroLocus_inf : zeroLocus (I ⊓ J) = zeroLocus I ∪ zeroLocus J;
    zeroLocus_union, zeroLocus_iSup, union_zeroLocus — ALL on the PrimeSpectrum side only.
  * Ideal.height I = ⨅ J ∈ I.minimalPrimes, primeHeight J  (holds by rfl — codim = min over components
    is DEFINITIONAL); Ideal.primeHeight = Order.height (point in PrimeSpectrum); height_eq_primeHeight.
  * ringKrullDim, Order.coheight present. NO `equidimensional`/`pureDimension` predicate (absent).
  * The point-space MvPolynomial.zeroLocus / vanishingIdeal has NO union/intersection/iSup/minimalPrimes
    lemmas — that algebra exists only on the PrimeSpectrum side.
- Half R (RLCT / SLT): logCanonicalThreshold, Function.logCanonicalThreshold, realLogCanonicalThreshold,
  rlct — ALL unknown identifiers (ABSENT). No Watanabe / singular-learning / learning-coefficient /
  free-energy / Igusa / local-zeta / Newton-polyhedron / resolution-of-singularities / Hilbert–Samuel
  multiplicity. PRESENT: MeasureTheory.integral, lintegral, Real.rpow, Module.length.

PAPER FACTS I confirmed from the source:
- Σ^r := {A | rk(mult A) = r}; c̄Σ^r := {rk ≥ r}; Σ^r = ⋃_{m, m_{0N}=r} O_m (orbit stratification).
- Components of c̄Σ^r ↔ minimal elements (maximal orbit closures); θ = number of TOP-dimensional
  (= minimal-codimension) components; numTop counts the min-codim orbits and the paper argues a non-component
  orbit closure cannot be min-codim, so numTop = θ.
- rlct definition (Def): rlct(F) := sup { s ∈ ℝ | |F|^{-s} locally integrable } — ANALYTIC.
- Theorem (aoyagi-rlct): rlct(K^DLN_B) = codim(mult^{-1}(B))/2. PROOF is purely a notation translation
  matching the engine's codim formula to Aoyagi [Thm 1]'s λ. The paper proves NO independent
  rlct ≤ codim/2 bound; that bound (eqn rlct_upper_bound) is cited (their Prop, Aoyagi/Watanabe).
- CRITICAL: the paper's own Remark states "there is NO simple relationship between
  rlcm(K^DLN_B) = m^2{S̃/m}(1−{S̃/m}) and the number k = C(m, S̃ − m⌊S̃/m+1/2⌋) of irreducible
  components of mult^{-1}(B)". I.e. the RLCT MULTIPLICITY (rlcm) ≠ θ (component count). The expedition
  brief assumes "rlcm = θ" (the SLT multiplicity is the top-component count); the paper contradicts this.

MY DRAFT VERDICT:
- Half A (Σ^r geometry + components + θ): BOUNDED / buildable in-expedition. Reuses Mathlib's
  minimalPrimes ≃o irreducibleComponents + height = inf primeHeight + the engine's per-orbit
  irreducibility/codim. The single hardest must-build lemma: the finite-union assembly
  Σ^r = ⋃ Ō_M as a CLOSED VARIETY with vanishingIdeal(Σ^r) = ⋂ vanishingIdeal(Ō_M), bridged from the
  point-space (Tuple d) into PrimeSpectrum so the minimalPrimes machinery applies — because the
  union/intersection lemmas live on the PrimeSpectrum side, not the point side. (G2.)
- Half R (the RLCT payoff): NOT a from-scratch analytic sub-library within scope. The cleanest honest
  route is a CITED/INTERFACED rlct: define (or axiomatise via a typeclass/structure) an rlct functional
  with the two cited properties (rlct ≤ codim/2; the Aoyagi value), and state rlct(K^DLN_B) = C/2 against
  that interface. The "θ = rlct multiplicity" half should be DROPPED from the payoff: the paper says they
  are unrelated. So the honest payoff is rlct = C/2 (Cited bound + Aoyagi value), with θ kept as the
  GEOMETRIC component count (Half A), NOT as rlcm.
</task>

<output_contract>
Respond in these sections, terse:
1. VERDICT-A: agree/disagree that Half A is bounded; name the single likeliest underestimate
   (the lemma or instance that will cost more than expected), and whether the point-space→PrimeSpectrum
   bridge is the right move or whether to define Σ^r directly in PrimeSpectrum.
2. VERDICT-R: agree/disagree that Phase R must be a cited/interfaced rlct (not from-scratch). If you think
   a from-scratch local-integrability rlct DEFINITION is cheaper than I think, say what minimal Mathlib
   pieces it needs and a rough lemma count.
3. The θ-vs-rlcm finding: is dropping "rlcm = θ" from the payoff the correct call? Any reading under which
   θ legitimately enters the SLT story (e.g. as Watanabe's free-energy multiplicity m vs. the geometric
   component count)? Be precise about what is Cited vs provable.
4. Single hardest must-build lemma in EACH half — do you agree with my picks? Propose better ones if so.
5. Any coverage I plausibly MISSED (a Mathlib brick that changes the verdict).
</output_contract>

<grounding_rules>
Distinguish what you can infer from the facts I gave vs. what you'd need to verify in Mathlib/the paper.
Do NOT invent Mathlib lemma names as if confirmed — mark any you propose as "candidate, verify".
If you think my paper reading (esp. the rlcm ≠ θ remark) is misread, say so and how to check.
</grounding_rules>
