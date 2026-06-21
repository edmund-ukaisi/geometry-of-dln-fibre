<task>
FOLLOW-UP, sharper. Lean4/Mathlib v4.29. Network-free commutative algebra. I need to decide if a
bounded (1-2 module) proof of the affine-domain dimension formula EXISTS given my exact inventory, or
whether it needs catenary content Mathlib lacks (in which case I report the gap, no sorry-patching).

GOAL: A = R⧸I where R = MvPolynomial (Fin n) k, k a field, I prime (so A is a finite-type k-domain).
p prime of A.  Want:  height_A(p) + ringKrullDim(A⧸p) = ringKrullDim A.

INVENTORY (exact Lean lemmas I HAVE, all proved, reusable as black boxes):
  H1 height_add_ringKrullDim_quotient_eq : for prime P of R=MvPoly(Fin n)k,
       P.height + ringKrullDim(R⧸P) = n.   (poly-ring equidimensionality, EQUALITY, any field)
  H2 ringKrullDim_quotient_eq_coheight : ringKrullDim(R'⧸p.asIdeal) = coheight p  (any comm ring R').
  H3 ringKrullDim_eq_of_integral_injective : integral + injective ring hom A'→S' ⟹ dim S' = dim A'.
  H4 exists_integral_inj_algHom_of_quotient : Noether normalization of R⧸P: ∃ s≤n, injective integral
       k[y_1..y_s] →ₐ[k] (R⧸P).   (so dim(R⧸P)=s.)
  H5 exists_ltSeries_comap_last_of_isIntegral : integral injective A'→S', a chain (LTSeries) in
       Spec A' lifts to a chain in Spec S' of SAME length whose comap-of-last = the original last.
       (going-UP chain lift; this is how I proved dim A' ≤ dim S'.)
  H6 strictMono_comap_of_isIntegral : for integral A'→S', comap is strictly monotone on Spec.
  Mathlib: IsLocalization.AtPrime.ringKrullDim_eq_height ; IsLocalization.primeHeight_comap /
       height_comap (localization preserves height of comap) ; Ideal.height_eq_height_add_of_liesOver_
       of_hasGoingDown (needs HasGoingDown, only HasGoingDown.of_flat available — integral ext is NOT
       flat) ; Ideal.under_def ; primeSpectrumQuotientOrderIsoIci (Spec(R⧸I) ≃o Set.Ici I).
  ABSENT in Mathlib (I grepped): IsCatenary/equidimensional (0 hits), going-down for integral+normal,
       integral height transport height_A(p)=height_B(comap).

MY REDUCTION (verify): both natural routes reduce the GOAL to ONE missing fact.
  Route N (Noether-normalize A): pick integral injective φ: B=k[y_1..y_s] →ₐ A with dim A = s = dim B
     (H4 on I gives B↪A; H3 gives dim A=s). Set q = p.comap φ (prime of B). Then:
        dim(A⧸p) = dim(B⧸q)   [because B⧸q ↪ A⧸p is integral injective (restriction of φ), H3]
        L5 on B (H1, B is a poly ring): height_B(q) + dim(B⧸q) = s = dim A.
     So GOAL  ⟺  height_A(p) = height_B(q) = height_B(p.comap φ).    (★ integral height transport)
  Route Q (quotient split): P = comap of (R→A) at p (prime ⊇ I); A⧸p ≅ R⧸P (H2 gives coheights);
     GOAL ⟺ height_R(P) = height_R(I) + height_A(p).               (★★ catenary split at I)

QUESTIONS:
 Q1. Confirm the reduction: is GOAL really equivalent to (★) under Route N given H1–H3? Write the
     exact additive derivation of GOAL from (★)+H1(on B)+H3, watching ℕ∞ (all terms ≤ s < ⊤, so
     left-cancellation of finite elements is OK — name the lemma WithTop.add_left_cancel or ENat
     analogue).
 Q2. THE CRUX. Is (★) height_A(p) = height_B(p.comap φ), for φ: B→A integral injective with B = poly
     ring over a field and A a domain, PROVABLE from H1–H6 + Mathlib WITHOUT a going-down/catenary
     theorem? Two sub-directions:
       (★-easy) height_B(comap) ≤ height_A(p): which Mathlib/my-lemma gives this? (going-up: chains
         below comap lift; does H5 give it, or is it the OTHER direction?)
       (★-hard) height_A(p) ≤ height_B(comap): is THIS the going-down content (needs incomparability
         /lying-over-below)? If so it is NOT bounded from my inventory — say so plainly.
     Be decisive: is (★-hard) derivable from H1–H6, or does it genuinely need going-down (=> L4d is
     NOT bounded, report gap)?
 Q3. ESCAPE HATCH. Is there a route to GOAL that AVOIDS (★)/(★★) entirely by reusing H1's proof
     STRUCTURE? Specifically: H1 was proved by induction on n peeling one variable via monic
     positioning of a nonzero f ∈ P (giving A[X]⧸P integral over A⧸q + a flat going-down additive
     height law on the 1-variable tower A→A[X], which IS HasGoingDown.of_flat since A→A[X] is free).
     Could the affine-domain GOAL be proved by the SAME peeling on a presentation A = R/I, i.e. an
     induction that reduces s by one via a monic element, using only the FLAT 1-variable tower
     going-down (which I HAVE) rather than the unavailable integral going-down? Sketch it or reject it.
 Q4. VERDICT: Given the operator mandate is "build it zero-cited, but L4d was SIZED as bounded 1-2
     modules reusing existing bricks", classify L4d as one of:
       (a) BOUNDED: closes from H1–H6+Mathlib in 1-2 modules — give the spine.
       (b) NEEDS-ONE-BRICK: needs exactly one new general lemma X (name it precisely, state if X is
           itself bounded or is the multi-week catenary core).
       (c) UNBOUNDED: genuinely needs the catenary/going-down core Mathlib lacks — report gap.
     Pick one and justify in ≤6 lines.
</task>

<output_contract>
  Q1: exact additive derivation + cancellation lemma name. Q2: decisive YES/NO on (★-hard) being
  bounded, with the one-line reason. Q3: concrete sketch or crisp rejection. Q4: (a)/(b)/(c) + the
  spine or the named brick. Total ≤ 35 lines. Mark every Mathlib lemma name you are unsure of with
  GUESS:.
</output_contract>

<grounding_rules>
  Standard comm-alg facts (going-up/going-down behaviour, catenary-ness of affine domains, that
  integral extensions need going-down for the hard height inequality) you may assert as math. For
  whether a Lean PROOF is bounded, reason ONLY from the listed inventory H1–H6 + named Mathlib
  lemmas; do not assume unlisted Mathlib API exists. If (★-hard) needs going-down, say L4d is not
  bounded — do not invent a shortcut that secretly assumes catenary.
</grounding_rules>
