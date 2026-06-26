<task>
Lean 4 + Mathlib v4.29 formalisation. I am composing a chain of already-proven `ncard` (set-cardinality)
equalities into a headline theorem, and need to (a) sanity-check the chain composes, (b) get the cleanest
tactic for the two keystone applications that hit a known instance-diamond / synthInstance fuel wall.

CONTEXT — the count chain. `TopDimMinPrimes A := {p ∈ minimalPrimes A | ringKrullDim (A ⧸ p) = ringKrullDim A}`,
a `Set (Ideal A)`. Goal headline: `(TopDimMinPrimes (O(fibre))).ncard = cTheta (dminus d r)`.

All these are LANDED (sorry-free), each an `ncard` equality of `TopDimMinPrimes` of two CommRings:
- E0 `ncard_topDimMinPrimes_sigma_eq_cTheta_dminus`:
    `(TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal d r)).ncard = cTheta (dminus d r)`
    [over `d : Fin (N+1) → ℕ`, needs Monotone d, ∀k r ≤ d k, two Kostant nonempties, IsAlgClosed+CharZero]
- KEYSTONE `topDimMinPrimes_ncard_away_eq (f : A) (S) [IsLocalization.Away f S] (hdim) (havoid) (hper)`:
    `(TopDimMinPrimes S).ncard = (TopDimMinPrimes A).ncard`, ABSTRACT over any CommRing A and f : A.
    hdim : ringKrullDim S = ringKrullDim A
    havoid : ∀ p ∈ TopDimMinPrimes A, f ∉ p
    hper : ∀ p ∈ TopDimMinPrimes A, ringKrullDim (Localization.Away (Ideal.Quotient.mk p f)) = ringKrullDim (A ⧸ p)
- ChartE `ncard_topDimMinPrimes_chartE_eq`:
    `(TopDimMinPrimes (Localization.Away (chartDsig ..))).ncard = (TopDimMinPrimes (Localization.Away (chartGfib ..))).ncard`
- Poly `topDimMinPrimes_mvPolynomial_ncard_eq`:
    `(TopDimMinPrimes (MvPolynomial ι A)).ncard = (TopDimMinPrimes A).ncard` [A Noetherian, ι finite]
- W3 `topDimMinPrimes_quotient_radical_ncard_eq (J)`:
    `(TopDimMinPrimes (R ⧸ J)).ncard = (TopDimMinPrimes (R ⧸ J.radical)).ncard`
- FibreUnit `ncard_topDimMinPrimes_fibre_eq_localization`:
    `(TopDimMinPrimes (R ⧸ fibreGenIdeal d E)).ncard = (TopDimMinPrimes (Localization.Away (mk (fibreGenIdeal d E) (ΔPdeep d r)))).ncard`

INDEXING SUBTLETY. The chart objects (sweepSigmaRing = O(Σ^r) = MvPolynomial (RepCoord d) k ⧸ vanishingIdeal(sweepSigma),
chartDsig = mk(vanishingIdeal(sweepSigma))(ΔPdeep), sweepFibreRing = O(F), chartGfib, ΔPdeep) are stated over
`d : Fin (N+2) → ℕ` (the chart machinery needs ≥1 interior vertex, condition hN : (0 : Fin (N+2)) ≠ Fin.last (N+1)).
E0 (the Σ̄^r endpoint) is over `d : Fin (N+1) → ℕ`. So when I compose, the FINAL theorem is most naturally stated
over `d : Fin (N+2) → ℕ`, and E0 is instantiated at the SAME d : Fin (N+2) → ℕ (its "N" = my "N+1"). i.e. E0 with
`(N := N+1) (d := d)` gives `(TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal d r)).ncard = cTheta (dminus d r)`.

THE W0 GAP (a separate module I will also build). E0 is over `sigmaIdeal d r = vanishingIdeal(canonicalCoord '' productRankLocusLE d r)`
(closed rank ≤ r). The chart source ring is `sweepSigmaRing = MvPolynomial (RepCoord d) k ⧸ vanishingIdeal(canonicalCoord '' productRankLocus d r)`
(exact rank = r). W0 must prove:
    `(TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal d r)).ncard
       = (TopDimMinPrimes (sweepSigmaRing k d r)).ncard`
i.e. closed-locus ideal and exact-locus ideal have the same TopDimMinPrimes count.
Available: `topDimMinPrimes_quotient_ncard_eq_of_minimalPrimes_eq (I J) (hmin : I.minimalPrimes = J.minimalPrimes)
(hdim : ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ J))` — equal minimal primes + equal quotient dim ⟹ equal count.
But here vanishingIdeal(exact) and vanishingIdeal(LE) do NOT have equal minimal primes in general (LE has extra
lower-strata components). They share only their TOP-dimensional minimal primes. The thread-08 Codex-vetted route:
every top component p of Σ̄^r equals vanishingIdeal(Ō_{realizerD m}) for a minimising Kostant partition m (LANDED
unconditional recovery `exists_kostantPartition_partitionIdeal_eq_of` discharged by `cCodim_zero_strict`), and the
realizer's orbit lies in Σ^r (`orbitAsTuples_realizerD_subset_productRankLocus` + `vanishingIdeal_orbitRankLocus_eq_orbitSet`),
so `vanishingIdeal(Σ^r) ≤ p`; lower strata are strictly lower-dim (strict corner-monotonicity), contributing no top
component; coincidence by `q.height = C` + strict prime-height monotonicity.

I have `topDimMinPrimes_quotient_ncard_eq_of_minimalPrimes_eq` which needs FULL minimalPrimes equality — too strong for W0.
W0 needs only a TOP-dim coincidence. There is also the abstract `bijOn_comap_quotTopDimSet` giving
`TopDimMinPrimes (R ⧸ I) ≃ quotTopDimSet I := {q ∈ I.minimalPrimes | ringKrullDim (R ⧸ q) = ringKrullDim (R ⧸ I)}`.

THE KEYSTONE-APPLICATION WALL (W1, W2). To apply `topDimMinPrimes_ncard_away_eq` at W2, I instantiate A := MvPolynomial SchurVar (sweepFibreRing k d r ..)
(a polynomial ring over a quotient ring) and f := chartGfib. The hper input requires elaborating `Ideal.map C q`,
`A ⧸ map C q ≅ MvPolynomial SchurVar (O(F) ⧸ q)`. Elaborating `Ideal.map (C : ...) q` / `A ⧸ map C q` over
`MvPolynomial SchurVar (MvPolynomial (RepCoord) k ⧸ I)` hits a CommRing/HasQuotient instance-diamond
(`AddMonoidAlgebra.semiring` vs `Ring.toSemiring`), exhausting default `synthInstance.maxHeartbeats`.
The thread-08 card calls this Lean-engineering, not math.

<output_contract>
Four sections, terse and concrete.

1. CHAIN COMPOSES? Verify the ncard chain telescopes E0 = ... = FibreUnit endpoint, in order:
   E0 (Σ̄^r) =[W0] sweepSigmaRing =[W1 keystone, f=chartDsig] Away(chartDsig) =[ChartE] Away(chartGfib)
   =[W2 keystone, f=chartGfib, after Poly descent] ... =[Poly] O(F)=sweepFibreRing =[W3, J=fibreGenIdeal via vanishingIdeal=radical] R⧸fibreGenIdeal =[FibreUnit].
   Flag any rung where the TWO ncard endpoints don't literally share a ring (so `.trans`/`rw` won't chain), and
   say what intermediate identity is missing. In particular: at W2, the keystone gives
   `ncard (Away gF) = ncard (MvPolynomial SchurVar O(F))`, but I need this to then chain to `ncard O(F)` via Poly.
   And the chart-e codomain `Away(chartGfib)` — is `chartGfib : MvPolynomial SchurVar O(F)`, so `Away(chartGfib)`
   localizes the POLYNOMIAL ring, and the keystone f=chartGfib instantiates A := MvPolynomial SchurVar O(F). Confirm
   the keystone-W2 A matches the chart-e codomain ring exactly (same instance path), or flag the diamond risk there too.

2. W0 — cheapest Lean route. Given I have `bijOn_comap_quotTopDimSet` (TopDimMinPrimes (R⧸I) ≃ quotTopDimSet I) and
   the recovery + containment + height facts above, what is the cleanest lemma to prove
   `(TopDimMinPrimes (R ⧸ sigmaIdeal)).ncard = (TopDimMinPrimes (R ⧸ vanishingIdeal(sweepSigma))).ncard`?
   Specifically: is it cleaner to (a) prove `quotTopDimSet (vanishingIdeal exact) = quotTopDimSet (sigmaIdeal)`
   as SETS (a Set.ext) and conclude via two `ncard_topDimMinPrimes_quotient_eq`, or (b) build a BijOn directly?
   What is the minimal set of facts to show the two quotTopDimSets are equal? (Note: a top-dim minimal prime q of
   one is a prime of R with height = C; I must show q ∈ minimalPrimes(other) and the dim matches. The hard direction
   and the precise Mathlib lemmas for "minimal prime of I of minimal height ⟹ minimal prime of J when J ≤ I≤ ... ").
   Be concrete about which containment (vanishingIdeal exact ≤ sigmaIdeal? or ≥?) holds and why.
   NOTE productRankLocus ⊆ productRankLocusLE (rank = r ⟹ rank ≤ r), so canonicalCoord''exact ⊆ canonicalCoord''LE,
   so vanishingIdeal(LE) = sigmaIdeal ≤ vanishingIdeal(exact). So sigmaIdeal ≤ vanishingIdeal(exact). Use this direction.

3. KEYSTONE-APPLICATION instance diamond — the disciplined tactic. The keystone is ABSTRACT over (A : Type) [CommRing A] (f : A).
   To apply it at W2 with A := MvPolynomial SchurVar O(F), f := chartGfib, hper must be discharged. Recommend the
   exact letI/haveI/abbrev structure that avoids re-synthesizing the AddMonoidAlgebra-vs-Ring.toSemiring diamond.
   Concretely: (i) should I introduce `abbrev FibrePolyRing := MvPolynomial SchurVar (sweepFibreRing k d r ..)` to
   pin ONE canonical CommRing instance path, then state hper/havoid/hdim against `FibrePolyRing`? (ii) when discharging
   hper per prime p = map C q, the helper `ringKrullDim_localizationAway_eq_of_fg_domain` needs `A ⧸ map C q` as a
   f.g. k-domain — how to get Lean to accept the `A ⧸ map C q` elaboration without the fuel wall (e.g. `set p := Ideal.map C q with hp` then `letI : CommRing (A ⧸ p) := inferInstance`)? (iii) is `set_option synthInstance.maxHeartbeats 400000`
   a legitimate localised fix, or does it just defer the wall? Give the concrete pattern you'd write.

4. RISKS. Anything in the above that is mathematically WRONG (not just hard), or any rung that secretly needs an extra
   hypothesis I haven't listed (e.g. Infinite k, Noetherian, nonemptiness for W0's height argument). Flag DVR-style
   per-prime dimension-drop risks in hper for W1/W2 specifically.
</output_contract>

<grounding_rules>
This is a design/strategy consult. Distinguish (a) what follows rigorously from the stated lemma signatures vs
(b) your inference about Mathlib API that I must verify locally. For any Mathlib lemma name you suggest, mark it
[VERIFY] — I will check it exists at v4.29 before using it. Do not invent lemma names confidently.
</grounding_rules>
</task>
