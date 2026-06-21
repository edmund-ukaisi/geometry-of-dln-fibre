<task>
Lean 4 + Mathlib (v4.29) formalisation architecture review. I am formalising the irreducible
components of the closed rank-≤r product locus Σ̄^r of a deep-linear-network representation space,
and the count θ of its top-dimensional components.

CONTEXT — landed bricks (all proved, sorry-free):
- `Tuple d` = ∏ Mat (the rep space Rep_d), over a field k. `RepCoord d` is a Finite index type;
  `canonicalCoord d : Tuple d ≃ (RepCoord d → k)` flattens to coordinates.
- `orbitRankLocus M : Set (Tuple d)` = the determinantal orbit closure Ō_M of a tuple M
  (= {A | rankPattern A ≤ rankPattern M pointwise}).
- G2 (set equality, [Field k]): `productRankLocusLE d r = ⋃ (M)(_ : (mult d M).rank ≤ r), orbitRankLocus M`.
  (Σ̄^r = ⋃_{corner M ≤ r} Ō_M.)  Also `orbitRankLocus_eq_of_rankPattern_eq` (equal rank patterns ⟹
  equal locus) — collapses the all-M union to the finite distinct family.
- `MvPolynomial.vanishingIdeal k (canonicalCoord d '' orbitRankLocus M)` IS PRIME [IsAlgClosed k]
  (`isPrime_vanishingIdeal_orbitRankLocus`) and the locus is Zariski-closed (`isZariskiClosed_orbitRankLocus`).
- `codimRepCanonical Z = Ideal.height (vanishingIdeal (canonicalCoord d '' Z))` (geometric codim).
- Per-orbit geometric codim = combinatorial codimForm; `cCodim d r` = min over Kostant partitions of
  the geometric orbit-closure codim (`cCodim_eq_inf_geomCodim`); `numTop d r` = # of minimisers.
- SPIKE (just verified, compiles): for a `Finset (Ideal R)` `s` of primes,
  `(sInf ↑s).minimalPrimes = {p | p ∈ s ∧ ∀ q ∈ s, q ≤ p → p ≤ q}` (the inclusion-minimal members),
  via `IsPrime.inf_le'`.
- Mathlib has: `Ideal.minimalPrimes.equivIrreducibleComponents I : I.minimalPrimes ≃o
  (irreducibleComponents (zeroLocus I))ᵒᵈ`; `Ideal.height = ⨅ minimalPrimes primeHeight` (definitional);
  `Ideal.height_strict_mono_of_is_prime : I prime, FiniteHeight I, I < J ⟹ I.height < J.height`;
  `PrimeSpectrum.vanishingIdeal_iUnion`. The ring `MvPolynomial (RepCoord d) k` is Noetherian
  (FiniteRingKrullDim ⟹ every ideal FiniteHeight).

GOAL: deliver, faithfully and zero-sorry,
  (G3) the irreducible components of Σ̄^r are exactly the maximal Ō_M (orbit-closure order);
  (θ)  the top-dimensional (= min-codim) components number `numTop d r`.

KEY DESIGN QUESTIONS:
1. Where to state "irreducible components of Σ̄^r"? The orbit closures live point-side (Set (Tuple d));
   the union/minimalPrimes algebra lives on PrimeSpectrum (MvPolynomial (RepCoord d) k). The point-space
   topology (MvPolynomial.zeroLocus on σ→k) lacks the union/component API. Recommendation so far: work
   on PrimeSpectrum via the intersection ideal `I_{≤r} := ⨅_{M in finite family} vanishingIdeal(Ō_M)`,
   prove `I_{≤r} = vanishingIdeal(canonicalCoord d '' Σ̄^r)` (the G2 bridge), then components of
   `zeroLocus I_{≤r}` ↔ minimalPrimes I_{≤r} ↔ maximal Ō_M. Is this the right faithfulness anchor, or is
   there a cleaner point-side route I'm missing?
2. The finite distinct family. G2's union is over infinitely many M (all corner-≤r tuples). I need a
   `Finset (Ideal R)` of the distinct `vanishingIdeal(Ō_M)`. Options: (a) index by rank-pattern functions
   (finitely many since each entry ≤ min d_i d_j), pushing through `orbitRankLocus_eq_of_rankPattern_eq`;
   (b) index by Kostant-partition realizers; (c) take the Set.Finite image of vanishingIdeal over the
   (finite) set of rank patterns directly. Which keeps the bridge `⨅ family = vanishingIdeal(Σ̄^r)`
   cheapest? The bridge needs `vanishingIdeal(⋃ Ō_M) = ⨅ vanishingIdeal(Ō_M)`.
3. θ-gate. To get "top-dim component count = numTop", I need: maximal Ō_M of MINIMAL height are exactly
   the height-minimisers among ALL corner-≤r orbits (a non-maximal Ō_S sits inside some maximal Ō_R with
   strictly smaller height, so it never attains the min). Then their count = numTop. Is
   `height_strict_mono_of_is_prime` (on the reversed vanishing-ideal inclusion) enough, plus the fact that
   the min-height members are automatically maximal? Any pitfall in identifying "height of the prime
   vanishingIdeal(Ō_M)" with the per-orbit `codimRepCanonical` = `cCodim`'s summand?

If G3 lands but θ has a genuine gap (e.g. matching the min-height-component COUNT to numTop's COUNT needs
an injection I can't cheaply build), say so explicitly and tell me the precise missing lemma.
</task>

<output_contract>
Three sections, terse:
1. FAITHFULNESS ANCHOR — confirm or correct the PrimeSpectrum-via-intersection-ideal plan for G3; name
   the single cleanest faithful component statement.
2. FINITE FAMILY — pick (a)/(b)/(c) or a better option; give the cheapest route to the bridge ⨅ = vanishingIdeal(Σ̄^r).
3. θ FEASIBILITY — is numTop = #top-dim-components reachable with the listed bricks? If a gap, name the
   exact missing lemma. Rank G3-only vs G3+θ by risk.
</output_contract>

<grounding_rules>
You may reason about Mathlib API by name but flag any lemma you are INFERRING exists vs. ones I listed as
confirmed. Distinguish "this will compile" (inference) from "this is the mathematically right statement"
(judgement). Do not emit large code blocks — names + one-line glosses only.
</grounding_rules>
