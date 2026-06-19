<task>
I am taste-reviewing two topology-free definitions in a Lean 4 / Mathlib formalisation, over an
algebraically closed field `k` with finite coordinate index `σ`. The ambient object is the affine
point space `σ → k` (functions, i.e. `k^σ`). Mathlib at this pin has the affine Nullstellensatz
machinery (`MvPolynomial.vanishingIdeal k V : Ideal (MvPolynomial σ k)`, `zeroLocus`,
`pointToPoint : (σ → k) → PrimeSpectrum (MvPolynomial σ k)` sending a point to the maximal/prime
ideal of polynomials vanishing there) but NO Zariski topology installed on `σ → k` itself — only on
`PrimeSpectrum`.

The two definitions under review:

  (1) `IsZariskiClosed Z := (Z = zeroLocus k (vanishingIdeal k Z))`
      "Z equals the zero locus of its own vanishing ideal."

  (2) `IsZariskiIrreducible Z := IsIrreducible (pointToPoint '' Z)`
      irreducibility (in the PrimeSpectrum topology) of the IMAGE of Z under pointToPoint.

Relevant Mathlib facts I have already confirmed:
 - `IsIrreducible s := s.Nonempty ∧ IsPreirreducible s`  (so empty set is NOT irreducible).
 - `isIrreducible_iff_closure : IsIrreducible (closure s) ↔ IsIrreducible s`.
 - `PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime : IsIrreducible s ↔ (vanishingIdeal s).IsPrime`
   (proved internally via `isIrreducible_iff_closure` + `zeroLocus_vanishingIdeal_eq_closure`).
 - `MvPolynomial.vanishingIdeal_pointToPoint : PrimeSpectrum.vanishingIdeal (pointToPoint '' V) = vanishingIdeal k V`.
 - Strong Nullstellensatz `vanishingIdeal_zeroLocus_eq_radical` (needs `[IsAlgClosed k] [Finite σ]`).
 - The file proves `isZariskiIrreducible_iff_isPrime_vanishingIdeal : IsZariskiIrreducible Z ↔ (vanishingIdeal k Z).IsPrime` (NO IsAlgClosed/Finite needed).

These definitions feed a codimension bridge: for `(vanishingIdeal Z).IsPrime`,
`height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` where
`varietyDim Z := (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal Z)).unbotD 0`.

I need a decorrelated judgement on whether these are the RIGHT topology-free notions, or whether
they smuggle a convenient-but-wrong meaning.
</task>

<questions>
 1. Is `IsZariskiClosed Z := Z = zeroLocus (vanishingIdeal Z)` the correct topology-free characterisation
    of "Z is Zariski-closed in affine space `k^σ`" over an alg-closed field? Specifically: does it
    coincide exactly with "Z is closed in the Zariski topology on `k^σ`" (the topology whose closed sets
    are exactly the zero loci of ideals)? Are there edge cases (empty set, whole space, finite sets) where
    it diverges? Is the alg-closedness even needed for this definition to be the right one, or is it the
    standard closure-operator fixpoint condition for ANY field?

 2. Is `IsZariskiIrreducible Z := IsIrreducible (pointToPoint '' Z)` — irreducibility of the IMAGE (not
    the closure, not Z-as-a-subspace) in PrimeSpectrum — the correct topology-free notion of "Z is an
    irreducible affine variety"? Concern: `pointToPoint '' Z` is a set of closed points, generally NOT
    closed in Spec. Does `IsIrreducible` of this non-closed image agree with "the Zariski closure of Z is
    an irreducible variety"? Does the fact that `IsIrreducible(s) ↔ IsIrreducible(closure s)` rescue this,
    making the definition equal to "closure of the image is irreducible"? Is there any pathology from
    `pointToPoint` possibly not being injective, or from Z being empty?

 3. Taste verdict: are (1) and (2) honest definitions (coincide with the genuine notions), or
    gerrymandered to make the downstream `↔ IsPrime (vanishingIdeal Z)` bridge cheap? Is there a MORE
    canonical topology-free phrasing that would be preferable (e.g. defining the Zariski topology on
    `k^σ` as an induced/pulled-back topology), and is the chosen phrasing a reasonable engineering choice
    given Mathlib has no point-space Zariski topology at this pin?
</questions>

<output_contract>
For each of the 3 questions: a one-paragraph verdict (HONEST / GERRYMANDERED / EDGE-CASE-CONCERN),
then the load-bearing reason. End with a single overall verdict: are these definitions bedrock-honest
for an irreducible-variety codimension bridge, or is there a specific divergence I should flag?
Be concrete with edge cases. Flag clearly what is mathematical fact vs your inference.
</output_contract>

<grounding_rules>
State explicitly when a claim is standard textbook fact (algebraic geometry) vs an inference about
the specific Lean phrasing. Do not invent Mathlib lemma names; reason from the facts I listed.
</grounding_rules>
