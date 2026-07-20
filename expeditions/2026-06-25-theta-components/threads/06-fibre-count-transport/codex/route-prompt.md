<task>
Lean 4 + Mathlib v4.29 formalisation. I must transport a *count of top-dimensional
irreducible components* (and a bijection to combinatorial data) from one coordinate ring
to another, through a localized chart isomorphism plus a polynomial extension. I want the
cleanest route and the precise hidden walls BEFORE I build (this is a multi-tide build;
I land incrementally).

CONTEXT (what is already PROVED, sorry-free, in the codebase):

1. Σ̄^r side (over the polynomial ring P_Σ := MvPolynomial (RepCoord d) k, k alg. closed, char 0):
   - sigmaIdeal d r : Ideal P_Σ  = vanishingIdeal of the closed rank-≤r product locus Σ̄^r.
   - topComponents d r h : Set (Ideal P_Σ) :=
       { p | p ∈ (sigmaIdeal d r).minimalPrimes ∧ p.height = (cCodim d r h).toNat }
     i.e. minimal primes whose HEIGHT equals the combinatorial constant cCodim.toNat.
   - numTop_eq_ncard_topComponents : numTop d r h = (topComponents d r h).ncard  [UNCONDITIONAL]
   - bijOn_partitionIdeal_topComponents_of (gated on two corner facts, both now discharged
     upstream so effectively unconditional): Set.BijOn (partitionIdeal d r)
       (minimisingPartitions d r h) (topComponents d r h)  — a bijection minimising Kostant
       partitions ↔ top components.
   - ncard_topComponents_sigma_eq_cTheta_dminus : (topComponents d r h).ncard = cTheta (d−r).

2. Fibre side:
   - O(fibre) generator ring: Q := MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d E,
     E = normalForm = diag(I_r,0).
   - Ideal.height_radical : (radical I).height = I.height  [minimalPrimes of I = of radical I].
   - codimRepCanonical_fibre_eq_height_fibreGenIdeal (alg closed): the fibre codim = height of
     fibreGenIdeal.
   - FibreDetUnit: ΔPdeep d r ("detΔ") ≡ 1 in Q, so detΔ is a UNIT on O(fibre);
     fibreLocalizationAwayDetΔ_algEquiv : Q ≃ₐ[Q] Localization.Away (mk detΔ).

3. The localized chart e (built for the codim result; used there only at ringKrullDim level):
   chartLocalizedAlgEquiv :
     Localization.Away dsig  ≃ₐ[k]  Localization.Away gF
   where:
     - dsig = mk (vanishingIdeal Σ^r) (ΔPdeep d r)  over O(Σ^r) = P/vanishingIdeal(Σ^r-exact-rank),
       (NB Σ^r here is rank-EXACTLY-r over Fin(N+2); topComponents is rank-≤r closed over Fin(N+1));
     - gF = map (algebraMap k O(F)) detSchurS over MvPolynomial (SchurVar) O(F),
       O(F) = P/vanishingIdeal(fibre).  card SchurVar = δ = r(d_N+d_0−r).
   So fibre side of e = (O(F)[X_1..X_δ])[1/detSchurS]  — polynomial extension by δ vars + a localization.

4. Mathlib available (confirmed present, v4.29):
   - RingEquiv.height_comap / height_map ; Ideal.comap_minimalPrimes_eq_of_surjective ;
     IsLocalization.minimalPrimes_comap ; IsLocalization.AtPrime.orderIsoOfPrime ;
     IsLocalization.height_map_of_disjoint ; IsLocalization.height_comap ;
     Ideal.minimalPrimes_eq_comap ; ringKrullDim_eq_of_ringEquiv.
   - NO packaged "minimalPrimes(R[X]) = {p·R[X]}" lemma, and NO "ringKrullDim((R/p)[X]) =
     ringKrullDim(R/p)+1" packaged for MvPolynomial-by-finite-σ at a single prime.

GOAL: numTop(fibre d E_r) = cTheta(d−r) = C(m,|δ|), i.e.
  #{top-dim min primes of O(fibre)} = #{top-dim min primes of Σ̄^r-side} = cTheta(d−r),
  plus the component bijection transported to the fibre.

The proposed route (controller): define TopDimMinPrimes A := {p ∈ minimalPrimes A |
ringKrullDim(A/p) = ringKrullDim A}; prove polynomial-extension equiv
TopDimMinPrimes(R[X_1..X_δ]) ≃ TopDimMinPrimes(R); localization survival at detSchurS / detΔ;
then transport through e via orderIsoOfPrime.
</task>

<output_contract>
1. ROUTE RANK. Is the height-based topComponents notion (p.height = cCodim.toNat) better kept,
   or should I switch the fibre side to the dim-based TopDimMinPrimes(ringKrullDim A/p = ringKrullDim A)?
   For each minimal prime, are "height = cCodim.toNat" and "ringKrullDim(A/p) maximal" the SAME selection
   here (catenary + equidimensional ambient)? If they can diverge, say exactly where. Give the single
   notion that makes the transport cleanest end-to-end and is faithful to "top-dimensional".
2. THE BIJECTION-COUNT SHORTCUT. Since #top-dim-min-primes is preserved by a ring iso and is what I
   ultimately count, can I AVOID re-deriving height/dim of each fibre prime and instead transport the
   *number* directly: O(fibre) ≃ Localization.Away detΔ ≃(orderIso on primes) primes of O(Σ^r)[1/dsig]
   ≃(e) primes of (O(F)[X]_δ)[1/detSchurS], matching top-dim primes set-wise via height-preservation
   lemmas, then ncard? Sketch the minimal chain of set-bijections + which lemma preserves the
   "top-dimensional" predicate at each arrow. Flag any arrow where the predicate is NOT obviously
   preserved (e.g. the +δ polynomial shift changes ringKrullDim of BOTH A and A/p by δ, so "= max" is
   preserved — confirm or refute).
3. THE δ-SHIFT. For the polynomial-extension arrow R ↦ R[X_1..X_δ] (R = O(F), a finite-type k-algebra
   quotient, so Noetherian + the relevant ring is equidimensional/catenary as a domain quotient): state
   the cleanest Mathlib-provable form of "minimalPrimes(R[X_δ]) ↔ minimalPrimes(R) and top-dim ↔ top-dim".
   Is it cheaper via Spec (PrimeSpectrum) maps, via Ideal.map C, or via the dim-equality
   ringKrullDim R[X] = ringKrullDim R + δ (Mathlib: does this exist for MvPolynomial Fin δ R / for R[X]
   iterated?)? Name the exact Mathlib lemmas if they exist.
4. THE TWO LOCALIZATIONS. detΔ is a UNIT on O(fibre) (so that localization is an iso — trivial).
   detSchurS is NOT a unit; I localize O(F)[X_δ] at it. dsig is the detΔ-image on O(Σ^r). For the count
   to be preserved I need: every TOP-dim min prime AVOIDS the localizing element (so it survives), AND no
   NEW top-dim prime appears. Give the cleanest sufficient condition + Mathlib lemma. (The codim
   expedition already proved the *dimension* doesn't drop under these localizations — SourceNoDrop,
   SchurSideNoDrop — can those be reused to show the top-dim min-prime SET is preserved, or do they only
   give the single number?)
5. INCREMENTAL LANDING ORDER. Give the dependency-ordered list of the 3–6 atomic lemmas, each with its
   exact Lean statement shape (hypotheses + conclusion), so each compiles in isolation. Mark which is the
   genuine math wall (if any) vs pure Mathlib wiring. If any step needs a math certificate beyond wiring,
   say which and what the certificate must assert.
6. INDEXING TRAP. The chart e is stated for rank-EXACTLY-r Σ^r over Fin(N+2); topComponents is rank-≤r
   closed Σ̄^r over Fin(N+1). Is this a real obstruction to transporting the COUNT, or does the
   exact-rank ↔ closed top-component identification already live implicitly in the codim assembly
   (RouteCAssembly / SigmaCodim)? Tell me what to check.
</output_contract>

<grounding_rules>
Distinguish (a) Mathlib lemmas you are CONFIDENT exist at v4.29 (name them) from (b) lemmas you BELIEVE
should exist but must be verified by grep, from (c) facts that must be hand-proved. Mark each.
Do not emit long Lean proofs — emit statement shapes + the one load-bearing tactic/lemma per step.
If the height-based and dim-based notions genuinely coincide here, say so plainly and pick the cheaper.
