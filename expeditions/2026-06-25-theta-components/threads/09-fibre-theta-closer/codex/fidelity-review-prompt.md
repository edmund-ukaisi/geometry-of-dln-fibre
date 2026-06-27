<task>
You are an independent fidelity/soundness reviewer for a Lean 4 + Mathlib formalisation in algebraic
geometry / quiver representation theory. I want a DECORRELATED second opinion on whether a composed
"headline" theorem faithfully captures an informal mathematical claim, and whether its proof chain
composes soundly. Do NOT trust my framing; reason from the mathematics.

BACKGROUND (the paper being formalised: Lehalleur–Rimányi 2024, "Geometry of the fibers of the
multiplication map of deep linear neural networks"). For a dimension vector d = (d_0,...,d_N) and a
target matrix B of rank r, the multiplication-map fibre mult^{-1}(B) is a quasi-affine variety. The
paper's invariants: C = codimension, and θ = the number of TOP-DIMENSIONAL irreducible components.
A separate, distinct invariant is the SLT (singular learning theory) "real log canonical threshold
multiplicity" / pole order, which for the equal-width case is a(ℓ−a)+1. These are KNOWN to be
different invariants for |δ|≥2 (e.g. widths (2,2,2,2,2), r=0: the component count θ = C(5,1)... wait,
let me give the actual claim): θ (component count) = C(m,|δ|) where m and δ are combinatorial data of
the shifted width vector d−r. For (2,2,2,2,2) r=0 the component count is 6 (= number of TOP-dim
components), whereas the total number of minimal primes / all components is 10, and the SLT pole order
is 5. So a faithful "θ = component count" formalisation must count ONLY the top-dimensional components
(6), NOT all minimal primes (10), and must NOT be conflated with the SLT order (5).

THE HEADLINE (Lean):
  ncard_topDimMinPrimes_fibre_eq_cTheta_dminus :
    (TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d E_r)).ncard = cTheta (dminus d r)
where:
  - TopDimMinPrimes A := { p ∈ minimalPrimes A | ringKrullDim (A ⧸ p) = ringKrullDim A }
  - fibreGenIdeal d E_r = Ideal.span { multPoly r c − C (E_r r c) }  (the GENERATOR ideal of the
    fibre's defining equations — NOT a priori radical)
  - cTheta e := Nat.choose (qipM e) (qipDelta e).natAbs   (= C(m, |δ|), a closed combinatorial form)
  - dminus d r = (fun i ↦ d i − r)   (the shifted width vector)
  - Hypotheses: k alg. closed, char 0; Monotone d; r ≤ d i for all i; certain kostantPartitions
    nonempty; rank bounds r ≤ d 0, r ≤ d (last).

THE PROOF CHAIN (7 rungs, all claimed sorry-free, axiom set {propext, Classical.choice, Quot.sound}):
  cTheta(d−r)
   =[E0]   ncard TopDimMinPrimes(O(Σ̄^r))         via numTop = #topComponents (unconditional) + Lemma 4.5 shift + Thm 7.10 closed form
   =[W0]   ncard TopDimMinPrimes(O(Σ^r))          O(Σ̄^r) vanishing ideal = O(Σ^r) (same ncard)
   =[W1]   ncard TopDimMinPrimes(O(Σ^r)[1/dsig])  away-survival: invert a localizing element dsig
   =[chartE] ncard TopDimMinPrimes((O(F)[Schur])[1/gF])  a ring iso (chart e)
   =[W2]   ncard TopDimMinPrimes(O(F)[Schur])     away-survival: invert gF over a polynomial ring over O(F)
   =[poly] ncard TopDimMinPrimes(O(F))            strip the polynomial extension (minimal primes of R[X] ↔ R)
   =[W3]   ncard TopDimMinPrimes(O(fibre))         radical-insensitive: O(F)=R⧸radical, O(fibre)=R⧸gen-ideal

Key supporting facts I have verified in the Lean source:
 - TopDimMinPrimes count is a ring-isomorphism invariant (transport along RingEquiv via comap).
 - W3: count is radical-insensitive because J and radical(J) have equal minimalPrimes
   (Ideal.radical_minimalPrimes) and equal quotient Krull dim (ringKrullDim_quotient + zeroLocus_radical).
 - E0: TopDimMinPrimes(O(Σ̄^r)) ↔ topComponents (height = cCodim minimal primes), and
   numTop_eq_ncard_topComponents is UNCONDITIONAL (the corner-monotonicity / Gabriel-recovery gating
   hypotheses are discharged).
 - poly: ncard TopDimMinPrimes(MvPolynomial ι A) = ncard TopDimMinPrimes(A), claimed via the classical
   fact that minimal primes of A[X] are p·A[X] for p minimal in A.
 - W1/W2 away-survival wrapper: needs (a) global ringKrullDim no-drop AND (b) f avoids every top-dim
   minimal prime; the per-prime no-drop is discharged generically for f.g. k-domains
   (ringKrullDim_localizationAway_eq_of_fg_domain), and avoidance is proven (not assumed).
</task>

<questions>
 Q1. FIDELITY. Is "TopDimMinPrimes A := {p ∈ minimalPrimes A | ringKrullDim(A⧸p)=ringKrullDim A}" a
     correct formalisation of "the number of top-dimensional irreducible components"? In particular:
     (a) Does it correctly EXCLUDE lower-dimensional components (the (2,2,2,2,2) 6-vs-10 distinction)?
     (b) Are there pitfalls where ringKrullDim(A⧸p)=ringKrullDim A could select the WRONG primes —
         e.g. if ringKrullDim A is +∞ or if the ring is not equidimensional / not catenary, could a
         non-top minimal prime spuriously satisfy the equation, or a genuine top one fail it? For a
         finite-type algebra over a field (which all rings in the chain are), is the criterion exactly
         "dim V(p) = dim Spec A" = "top-dimensional component"?
 Q2. SOUNDNESS of the away-survival rungs (W1, W2). Inverting an element f and counting top-dim
     minimal primes: is it TRUE that if f avoids every top-dim minimal prime AND ringKrullDim does not
     drop, then ncard TopDimMinPrimes is preserved under localization A → A[1/f]? Localization A[1/f]
     keeps exactly the primes not meeting {f^n}. The danger: could localization (i) DROP a top-dim
     minimal prime (excluded by avoidance), or (ii) PROMOTE a previously-non-top minimal prime to
     top-dim in A[1/f] because the ambient dimension dropped? The "global no-drop" hypothesis
     ringKrullDim(A[1/f])=ringKrullDim(A) is meant to kill (ii). Is global no-drop + avoidance
     genuinely SUFFICIENT, or is a per-prime condition also needed (the Lean wrapper also threads a
     per-prime no-drop)? State the cleanest correct sufficient condition.
 Q3. THE poly RUNG. Is ncard TopDimMinPrimes(A[X_1..X_n]) = ncard TopDimMinPrimes(A) actually TRUE
     for the TOP-DIMENSIONAL count (not just minimal primes)? Minimal primes biject (p ↦ p·A[X]). But
     does the TOP-DIMENSIONAL selection survive? dim A[X] = dim A + n for Noetherian A, and
     dim(A[X]/p A[X]) = dim(A/p) + n. So dim(A/p)=dim A ⟺ dim(A[X]/pA[X])=dim A[X]. Confirm this
     equivalence holds (Noetherian / finite-type over a field) so the poly rung is faithful, or flag
     a counterexample.
 Q4. OVERCLAIM / hidden gaps. Given the hypotheses (alg-closed char-0 field; Monotone d; r ≤ d i;
     kostantPartitions nonempty; rank bounds): are these the honest minimal set, or could one of them
     be masking a gap (e.g. is Monotone d load-bearing for the COMBINATORIAL identity cTheta only, or
     also silently needed for the geometry)? Is there any standard failure mode in such a 7-rung
     ncard-transport chain where the calc endpoints could line up syntactically while the underlying
     ring at a junction is subtly mismatched (e.g. an instance-diamond making two "equal" rings
     actually different)?
</questions>

<output_contract>
 Answer Q1–Q4 in order, each with a clear PASS / CONCERN / FAIL verdict and a one-paragraph
 justification. For any CONCERN/FAIL give the cheapest discriminating check or a concrete
 counterexample (specific ring / dimension). End with a single overall verdict line:
 OVERALL: PASS or OVERALL: CONCERNS(list). Be terse and precise. Flag inference vs. established fact
 explicitly — say "standard fact:" or "I infer:".
</output_contract>

<grounding_rules>
 You are reasoning about mathematical correctness from the statements given; you cannot see the full
 Lean source. Do NOT assert a Lean proof is wrong merely because you can't see it — instead state the
 mathematical condition that MUST hold for the rung to be valid, and whether it is a standard theorem
 or a subtle/false claim. Distinguish "this is a true theorem (standard)" from "this requires a
 hypothesis not obviously present" from "this is false in general (counterexample: ...)".
</grounding_rules>
