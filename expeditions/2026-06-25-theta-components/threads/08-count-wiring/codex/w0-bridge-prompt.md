<task>
Lean 4 + Mathlib v4.29. Algebraic geometry over an alg-closed field k. Assess whether a "bridge"
step in a component-count transport is a real math wall or has a cheap route.

SETUP. Two coordinate rings over the same ambient polynomial ring R = MvPolynomial (RepCoord d) k:
  - O(Σ̄^r)  = R ⧸ sigmaIdeal,        sigmaIdeal = vanishingIdeal (canonicalCoord '' productRankLocusLE d r)
  - O(Σ^r)   = R ⧸ vanishingIdeal(canonicalCoord '' productRankLocus d r)
where:
  - productRankLocus d r    = { tuples M : (mult d M).rank = r }      (rank EXACTLY r)
  - productRankLocusLE d r  = { tuples M : (mult d M).rank ≤ r }      (rank ≤ r, the CLOSED locus)
So productRankLocus ⊆ productRankLocusLE, hence vanishingIdeal(LE) ⊆ vanishingIdeal(exact)  [one inclusion FREE].

DEFINITION of the count: TopDimMinPrimes(A) = {p ∈ minimalPrimes A | ringKrullDim (A⧸p) = ringKrullDim A}.
I want: (TopDimMinPrimes O(Σ̄^r)).ncard = (TopDimMinPrimes O(Σ^r)).ncard  (the "W0" bridge).

WHAT IS ALREADY PROVED IN THE CODEBASE:
  - varietyDim (Σ^r) = varietyDim (Σ̄^r)   [equal DIMENSION; proved by catenary cancellation
    codim+dim=card with codim Σ^r = C = codim Σ̄^r — NOT via any set/ideal equality].
  - productRankLocusLE d r = ⋃_{M : rank ≤ r} orbitRankLocus M   [stratification: closed locus is
    the union of orbit-rank-loci of all rank-≤r tuples].
  - The closure operator repClosure S = zeroLocus(vanishingIdeal(canonicalCoord '' S)), with
    vanishingIdeal_repClosure : vanishingIdeal(repClosure S) = vanishingIdeal(canonicalCoord '' S).
  - The codebase EXPLICITLY DECLINED proving "Σ̄^r = repClosure(Σ^r)" as a set equality, calling it
    needing "an unbuilt rank-raising/density theorem".
  - Over O(Σ̄^r): TopDimMinPrimes(O(Σ̄^r)) ↔ topComponents = the min-height minimal primes of sigmaIdeal,
    each = vanishingIdeal(Ō_{realizerD m}) for a minimising Kostant partition m (a corner-r orbit closure).

QUESTION 1 (the crux). Is the bridge (TopDimMinPrimes O(Σ̄^r)).ncard = (TopDimMinPrimes O(Σ^r)).ncard
a genuine wall (needing the declined density fact vanishingIdeal(exact) = vanishingIdeal(LE), i.e.
productRankLocusLE ⊆ repClosure(productRankLocus)), OR is there a cheaper route that gets the COUNT
equality without the full ideal equality?

In particular consider: the top-dimensional minimal primes of O(Σ̄^r) are the orbit closures of the
top stratum (rank exactly r corner-r orbits). The lower strata (rank < r) are LOWER dimensional. So
the TOP-dim components of Σ̄^r are exactly the maximal-dim irreducible components, all of which are
closures of rank-EXACTLY-r orbits — they live in the closure of Σ^r. Does this mean the top-dim
minimal primes of vanishingIdeal(exact) and vanishingIdeal(LE) literally COINCIDE (as the lower strata
contribute no top-dim component), so the count is equal even though the full ideals differ? If so, what
is the minimal lemma needed (e.g. "every top-dim minimal prime of vanishingIdeal(LE) contains
vanishingIdeal(exact)" or vice versa)?

QUESTION 2. If it IS a wall, state the single cleanest sufficient lemma to break it, and whether that
lemma is the declined density theorem or something weaker.
</task>

<output_contract>
1. VERDICT: "real wall" or "cheap route exists" — one line.
2. If cheap: the exact minimal lemma(s) and the ⊆ direction argument (which vanishingIdeal contains which,
   restricted to top-dim primes), in enough detail to formalize. Name the key fact about lower strata
   being lower-dimensional.
3. If wall: the single cleanest sufficient lemma, and whether it equals the declined density theorem.
4. Any HAZARD: a case where exact and closed have DIFFERENT top-dim component counts (would kill the
   cheap route) — does productRankLocus (rank exactly r) being possibly REDUCIBLE or EMPTY at the top
   matter? (E.g. is Σ^r itself always nonempty / does its closure capture all top components of Σ̄^r?)
</output_contract>

<grounding_rules>
Mark each cited Mathlib/standard fact [CONFIDENT] or [UNSURE]. Distinguish "clean math" from "Lean lemma
exists". Be explicit about whether your cheap route needs irreducibility of Σ^r (it may not be irreducible).
</grounding_rules>
