<task>
I am a fidelity reviewer auditing a Lean 4 + Mathlib formalisation. The math goal: count the
top-dimensional irreducible components of a fibre of matrix multiplication for deep linear networks,
and show that count equals a combinatorial closed form cTheta(d-r). The thread under audit builds a
reusable framework and lands two ENDPOINTS of a transport chain, but explicitly does NOT yet prove
the full headline numTop(fibre)=cTheta(d-r).

Three definitions/statements to vet for FAITHFULNESS (are these the RIGHT formalisations of the
informal notions?), purely as commutative algebra:

(1) The "top-dimensional irreducible component" notion is formalised as:
    TopDimMinPrimes A := { p ∈ minimalPrimes A | ringKrullDim (A ⧸ p) = ringKrullDim A }
    i.e. the minimal primes p whose quotient A/p carries the FULL Krull dimension of A.
    The count of interest is (TopDimMinPrimes A).ncard.
    An alternative would be a HEIGHT-based reading: { p ∈ minimalPrimes A | p.height = (0).height } or
    height-minimal. The thread chose the dimension/quotient reading deliberately, arguing it is
    "transport-clean" (invariant under ring iso and unit localization).
    QUESTION 1a: Is "minimal prime p with dim(A/p) = dim(A)" a faithful formalisation of
    "top-dimensional irreducible component of Spec A"? Any case where this misfires (e.g. dim A = ⊤
    infinite; A trivial; A not equidimensional / not catenary; mixed-dimensional Spec)?
    QUESTION 1b: For a ring that is NOT equidimensional, does this notion still capture exactly the
    maximal-dimensional components, or could it (a) miss a genuine top component, or (b) include a
    spurious one? Is the dimension-reading vs height-reading discrepancy a real fidelity risk for the
    downstream use (the rings here are quotients of polynomial rings over a field, hence catenary /
    equidimensional in the relevant cases)?

(2) The polynomial-extension descent (claimed as the main math wall, proved unconditionally for A
    Noetherian, ι finite):
    (TopDimMinPrimes (MvPolynomial ι A)).ncard = (TopDimMinPrimes A).ncard
    The proof: comap C : Ideal (MvPolynomial ι A) → Ideal A is a bijection TopDimMinPrimes(poly) ≃
    TopDimMinPrimes(A), inverse map C. Key facts used:
      - comap C (map C q) = q for q prime.
      - map C q is prime when q is (quotient ≅ MvPolynomial ι (A/q), a domain).
      - minimality transports both ways via the map C ⊣ comap C adjunction.
      - ringKrullDim (poly ⧸ map C q) = ringKrullDim (A ⧸ q) + Nat.card ι, AND
        ringKrullDim (MvPolynomial ι A) = ringKrullDim A + Nat.card ι, so the +card ι shift cancels
        on both sides of the top-dim equality. Cancellation lemma: a + ↑c = b + ↑c ↔ a = b in
        WithBot ℕ∞ (valid even when a,b = ⊤).
    QUESTION 2: Is this the honest GENERAL fact (no hidden hypothesis missing)? In particular: is the
    +card ι dimension shift correct for ALL minimal primes (not just the top ones)? Is the bijection
    genuinely two-sided (does comap C hit EVERY minimal prime of the poly ring, i.e. is every minimal
    prime of MvPolynomial ι A extended from A — true because ι finite & we only need minimal primes)?
    Any Noetherian-ness subtlety: the dimension formula dim(MvPolynomial ι A) = dim A + card ι needs
    A Noetherian — is that the ONLY place Noetherian is used, and is it genuinely needed?

(3) The fibre-side endpoint:
    ncard_topDimMinPrimes_fibre_eq_localization :
      (TopDimMinPrimes (O(fibre))).ncard = (TopDimMinPrimes (O(fibre)[1/detΔ])).ncard
    where detΔ is proved to be a UNIT on O(fibre), so the localization is a ring iso. The NAME says
    only "count preserved under the detΔ-unit localization". It does NOT claim = cTheta.
    QUESTION 3: Confirm this is a true statement (unit localization is a ring iso, ncard preserved)
    and that the name does not overclaim.

(4) THE CHAIN GAP CHECK. The documented transport chain (each arrow with status) is:
    topComponents(Σ̄^r) ↔ TopDimMinPrimes(O(Σ̄^r)) = cTheta(d−r)      [LANDED]
      │ W0: exact-rank Σ^r (Fin N+2) ↔ closed Σ̄^r (Fin N+1) — NOT a TopDimMinPrimes wire yet
      ▼
    TopDimMinPrimes(O(Σ^r))
      │ W1: localization at dsig (detΔ) — NON-unit on O(Σ^r); needs all-top avoidance + no-drop  [NOT BUILT]
      ▼
    TopDimMinPrimes(O(Σ^r)[1/dsig])
      │ chart e (ring iso) — available, NOT yet wired
      ▼
    TopDimMinPrimes((O(F)[SchurVar])[1/gF])
      │ W2: localization at gF — NON-unit; avoidance EASY after poly descent  [NOT BUILT]
      ▼
    TopDimMinPrimes(O(F)[SchurVar])
      │ poly descent  [LANDED]
      ▼
    TopDimMinPrimes(O(F))
      │ W3: O(F) (radical) ↔ O(fibre) (generator) — same minimal primes [NOT BUILT, "a wire"]
      ▼
    TopDimMinPrimes(O(fibre)) = TopDimMinPrimes(O(fibre)[1/detΔ])  [LANDED, unit case]

    The thread classifies W1 (the dsig all-top avoidance certificate) as a "genuine pen-and-paper
    math input", and W0/W2/W3 + the chart-e wire as "wiring / mechanical / dim-level wires".
    QUESTION 4: Is any arrow the thread labels "wiring / mechanical / a wire" actually a HIDDEN MATH
    WALL that I should re-classify? Specifically scrutinise:
      - W1 "localization survival at a NON-unit f": for S = Localization (powers f) A, the claim is
        comap (algebraMap A S) is a bijection TopDimMinPrimes S ≃ TopDimMinPrimes A GIVEN (i) every
        top-dim minimal prime of A avoids f, and (ii) ringKrullDim S = ringKrullDim A. Is that the
        complete set of hypotheses, or is there a subtlety (e.g. a surviving prime of S could fail to
        be top-dimensional in S even if its contraction is top in A, or vice versa; the per-prime
        quotient-dim equality dim(S/P) = dim(A/comap P) — does this need MORE than "S/P is a
        localization of the domain A/comap P"? localization of a domain can DROP dimension)?
      - W0: are the top-dim minimal primes of the exact-rank locus Σ^r and the closed Σ̄^r genuinely
        the SAME, or does the closure / the +1 ambient dimension shift change the top-component set?
        Is this a real math question (not a "wire")?
      - W3: O(F) = P/radical(J), O(fibre) = P/J. Same minimal primes (radical_minimalPrimes). But
        does TopDimMinPrimes coincide — i.e. is dim(O(F)/p) = dim(O(F)) ↔ dim(O(fibre)/p) =
        dim(O(fibre)) for the shared minimal primes p? (dim of a ring = dim of its reduction, and
        quotient by a minimal prime is already reduced, so this should be fine — but confirm.)
    Rank these four (W0,W1,W2,W3) by how much genuine math they hide. Tell me if the thread has
    MIS-LABELLED any "wire" that is actually a wall, which would make the card's honesty claim wrong.
</task>

<output_contract>
  Five short sections, in order:
  1. Q1 verdict (TopDimMinPrimes faithfulness): FAITHFUL / FAITHFUL-WITH-CAVEAT / UNFAITHFUL + the
     precise misfire case if any, and whether it bites the polynomial-ring-quotient downstream use.
  2. Q2 verdict (poly descent honesty): SOUND / SOUND-WITH-CAVEAT / GAP + any missing hypothesis.
  3. Q3 verdict (fibre endpoint): one line.
  4. Q4: rank W0,W1,W2,W3 by hidden-math content; explicitly name any arrow the thread calls a
     "wire/mechanical" that is actually a math wall (this is the load-bearing answer).
  5. Single-sentence bottom line: is the card's honesty claim ("two endpoints + the poly-descent wall
     LANDED; the rest is the remaining wall, with W1 the genuine math input") accurate, or does it
     under/over-state what remains?
</output_contract>

<grounding_rules>
  This is pure commutative-algebra reasoning; you do not have the Lean files. Reason from the
  mathematical statements as given. Flag clearly when you are INFERRING vs stating a standard fact.
  Where a claim depends on equidimensionality / catenary / domain-localization-dimension behaviour,
  state the exact hypothesis under which it holds and whether quotients of a polynomial ring over a
  field satisfy it. Do not invent Mathlib lemma names.
</grounding_rules>
