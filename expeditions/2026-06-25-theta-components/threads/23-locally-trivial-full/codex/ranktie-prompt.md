<task>
Pin the PRECISE formalizable target for the "rank-tie" before I build ~150-300 LoC. Be decisive about
what statement honestly earns the name `locallyTrivial`.

CONTEXT (Lean 4 / Mathlib, all sorry-free, axiom-clean), Lehalleur–Rimányi Lemma 4.6 fibre bundle:
- BASE ring `sweepSigmaRing k d r = O(Σ̄^r) = MvPolynomial(RepCoord d)/vanishingIdeal(sweepSigma)`,
  the coord ring of the CLOSURE Σ̄^r of the rank-=r product locus.
- `chartDsigAt d r s t : sweepSigmaRing` = class of the (s,t) deep r×r minor.
- `rankROpen d r : Set (PrimeSpectrum sweepSigmaRing) := (zeroLocus (range chartDsigAt))ᶜ` — DEFINED as
  the chart-cover-complement (set of PRIMES). `iSup_pivot_basicOpen_eq_rankROpen` proves
  `⨆ basicOpen(chartDsigAt) = rankROpen` (near-definitional).
- `sweepSigma k d r : Set (RepCoord d → k) := canonicalCoord '' productRankLocus d r` — the rank-=r
  K-POINT locus (NOTE: a set of k-points / functions RepCoord→k, NOT primes).
- BANKED forward: `sweepSigma_subset_chartOpen : ∀ x ∈ sweepSigma, ∃ pivot (s,t), IsUnit(eval x
  (ΔPdeepAt d r s t))`. (k-point statement; from `exists_invertible_minor_of_rank` on `mult A` at rank=r.)
- BANKED rank lemmas (RankLocusClosed): `submatrix_det_eq_zero_of_rank_le` (rank ≤ r ⟹ every (r+1)×(r+1)
  minor det = 0) and `exists_submatrix_det_ne_zero_of_le_rank` (r+1 ≤ rank ⟹ some (r+1) minor ≠ 0).
  Also `eval_det_submatrix_multPoly : eval x (det ((of multPoly).submatrix br bc)) = ((mult A).submatrix
  br bc).det` (eval of deep minor = minor of the actual product).

THE TENSION I see. `rankROpen` is a set of PRIMES; `sweepSigma`/`{rank=r}` is a set of K-POINTS. They
are not literally the same type, so a bare `rankROpen = {rank=r}` does NOT type-check. Options for the
"rank-tie":
(A) K-POINT converse: for a k-point x with rank(mult-at-x) ≤ r (i.e. x ∈ Σ̄^r, the ambient closure),
    `(∃ pivot, IsUnit(eval x ΔPdeepAt)) ↔ x ∈ sweepSigma (rank = r)`. Forward (⟸) is banked; converse
    (⟹): some r×r minor ≠ 0 ⟹ rank ≥ r, plus ≤ r ⟹ = r (RankLocusClosed). This is a genuine, provable
    k-point biconditional restricted to the closure.
(B) PRIME-level: map a maximal ideal / closed point of Spec(sweepSigmaRing) to its k-point (Nullstellensatz
    over alg-closed k) and show it lies in rankROpen iff rank=r. Needs the maximal-ideal↔point bridge over
    the quotient ring — heavier.
(C) Something else.
</task>

<output_contract>
Terse, decisive:

1. WHICH STATEMENT IS THE HONEST RANK-TIE? Is (A) — the k-point biconditional restricted to the
   rank-≤r closure — the genuine, provable content that "the r×r minors cut out the rank-<r
   complement"? Or does honestly earning `locallyTrivial` REQUIRE (B), the prime/scheme-level
   statement over Spec(sweepSigmaRing)? Be concrete about which one a careful algebraic geometer would
   accept as "the charts cover exactly the rank-=r open".

2. DOES (A) EARN `locallyTrivial`? If I prove (A) — the k-point biconditional `chart-cover ↔ rank=r` on
   the closure — does that upgrade my atlas from "named pivotLocalProductAtlas (mild overclaim to call
   locallyTrivial)" to honestly `locallyTrivial`? Or does the residual remain (because the COVER in the
   atlas is `iSup basicOpen = rankROpen`, a prime statement, and (A) is a k-point statement — they
   don't compose to a scheme local-triviality)?

3. THE EXACT LEAN SHAPE. Give the precise statement(s) to prove for the honest rank-tie. I expect
   something like: `chartCoverKPoint d r := {x | ∃ st, Injective s ∧ Injective t ∧ IsUnit(eval x
   ΔPdeepAt)}` and the theorem `sweepSigma d r = chartCoverKPoint d r ∩ {x | (mult-at-x).rank ≤ r}` (or
   `∩ Σ̄^r`). State the cleanest honest form and whether it needs alg-closed k.

4. VERDICT ON THE NAME. After (A), what is the maximally-honest headline name? `locallyTrivial`-family
   (e.g. `reducedFibre_locallyTrivialOnRankLocus`) or still `pivotLocalProductAtlas…`? If the prime-vs-
   k-point gap means even (A) doesn't license `locallyTrivial`, say so plainly — I will report that the
   genuine residual is the prime/scheme bridge (B), not buildable as "no new mathematics", and keep the
   honest atlas name.
</output_contract>

<grounding_rules>
You cannot see the files. Flag inference vs derivation. The crux is the PRIME-vs-K-POINT type gap: my
`rankROpen` is primes, my `sweepSigma`/rank facts are k-points. If bridging them to license
`locallyTrivial` genuinely needs the Nullstellensatz maximal-ideal↔point machinery (NOT "no new math"),
say so — I would rather report that honestly than overclaim a `locallyTrivial` name on a k-point tie.
</grounding_rules>
