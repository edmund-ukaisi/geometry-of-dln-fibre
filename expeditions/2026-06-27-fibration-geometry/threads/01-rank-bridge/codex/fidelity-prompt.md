<task>
You are red-teaming the FIDELITY of a Lean 4 / Mathlib theorem against an informal claim. Fidelity = does the formal statement faithfully capture the informal target, with no hidden hypotheses, no vacuity, no overclaim. Do NOT critique proof tactics; assume the proof compiles (it does, build is green, axiom-clean).

INFORMAL TARGET (S1): For Spec(sweepSigmaRing k d r) = the chart-closure ring of the rank-exactly-r product locus, the rank-`= r` open `rankROpen d r` is exactly the locus where the universal product matrix, evaluated over the residue field κ(P) of a prime P, has rank = r. Precisely: `P ∈ rankROpen d r ↔ (universal matrix over κ(P)).rank = r`.

KEY DEFINITIONS (all real, from the repo):
- `multPoly d : Fin (d (last N)) → Fin (d 0) → MvPolynomial (RepCoord d) k` = the (r,c) entry of the generic matrix product A_N ⋯ A_1 (entries are coordinate variables). `Matrix.of (multPoly d)` is the universal product matrix.
- `mult d A` = actual product A_N⋯A_1; `productRankLocus d r = {A | (mult d A).rank = r}` (rank EXACTLY r).
- `sweepSigma k d r := canonicalCoord d '' productRankLocus d r` (image of rank-exactly-r locus in coordinate space).
- `sweepSigmaRing k d r := MvPolynomial (RepCoord d) k ⧸ vanishingIdeal k (sweepSigma k d r)` (vanishingIdeal = Mathlib MvPolynomial.vanishingIdeal: polys vanishing on the set).
- `ΔPdeepAt d r s t := ((Matrix.of (multPoly d)).submatrix s t).det` for selectors s,t : Fin r → ...
- `chartDsigAt d r s t := Ideal.Quotient.mk (vanishingIdeal k (sweepSigma)) (ΔPdeepAt d r s t)` (class of the r×r minor in sweepSigmaRing).
- `rankROpen d r := (zeroLocus (range (fun st ↦ chartDsigAt d r st.1 st.2)))ᶜ` — complement of common vanishing locus of all r×r pivot minors. (def over PrimeSpectrum sweepSigmaRing.)
- `residueMap d r P := (algebraMap (sweepSigmaRing k d r) P.asIdeal.ResidueField).comp (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)))` : MvPolynomial (RepCoord d) k →+* κ(P).
- `universalMatrixResidue d r P := (Matrix.of (multPoly d)).map (residueMap d r P)`.

HEADLINE PROVED:
`P ∈ rankROpen (k:=k) d r ↔ (universalMatrixResidue d r P).rank = r`
Supporting lemmas proved:
- `rank_universalMatrixResidue_le`: rank ≤ r for EVERY prime P. (proof: the (r+1)-minors of multPoly lie in vanishingIdeal(sweepSigma), so vanish in sweepSigmaRing, so vanish in κ(P); then the over-field minor criterion rank ≤ r.)
- `r_le_rank_universalMatrixResidue_of_notMem`: if chartDsigAt s t ∉ P then rank ≥ r.
- `mem_rankROpen_iff_exists_notMem`: P ∈ rankROpen ↔ ∃ (s,t), chartDsigAt s t ∉ P.
- r=0 branch handled: empty 0×0 minor det = 1, chartDsigAt = 1 ∉ P (prime proper), so rankROpen = all primes and rank=0 always.

The (r+1)-minor-vanishing lemma `det_submatrix_multPoly_mem_vanishingIdeal_sweepSigma` is proved on points A with `(mult d A).rank = r` (rank EXACTLY r, via mem_productRankLocus), using rank=r ⟹ rank≤r ⟹ (r+1)-minors vanish.

CARD SCOPING: "Deferred: the bridge is prime-pointwise (iff per P), giving rankROpen = {P | rank over κ(P)=r} as a set of primes; NOT packaged as a scheme/structure-sheaf identity. No scheme-object identity claimed."
</task>

<output_contract>
Five numbered verdicts, each one short paragraph:
1. Does `universalMatrixResidue` faithfully = "universal product matrix evaluated over κ(P)"? Is residueMap the correct composite (note: it factors MvPolynomial → sweepSigmaRing → κ(P), but the SAME κ(P) class is reached as if going MvPolynomial → κ(P) directly — is that the intended object)?
2. Is the headline iff non-vacuous / not vacuously true? Any prime P where both sides are trivially true/false in a way that hides content?
3. Hidden hypotheses: is anything load-bearing beyond [Field k]? Is the r=0 branch honest (not a false claim swept under a unit)?
4. THE SHARP ONE: the (r+1)-minor vanishing is proved over `sweepSigma` = image of rank-EXACTLY-r locus, NOT rank-≤-r locus. Is "rank ≤ r over κ(P) for every prime P" actually TRUE for sweepSigmaRing built from the rank-exactly-r locus? Concretely: is vanishingIdeal(rank-exactly-r locus) ⊇ the (r+1)-minors? (Yes if every point of the exactly-r locus has rank ≤ r — trivially true. But could the CLOSURE / the ring sweepSigmaRing have primes where rank jumps ABOVE r? The minors vanish on the set, hence in the vanishingIdeal, hence in EVERY prime containing it = every prime of the quotient ring. So rank ≤ r everywhere. Confirm or find the hole.)
5. Overclaim check: does the name `mem_rankROpen_iff_rank_universalMatrixResidue_eq` and the card's "set of primes, not scheme identity" scoping honestly match what's proved? Is calling rankROpen "the rank = r locus" justified given rankROpen is DEFINED as a complement-of-zero-locus, with the rank-tie being THIS theorem?
</output_contract>

<grounding_rules>
Flag inference vs fact explicitly. You cannot run the build; assume compilation. Focus on mathematical fidelity of statement-to-claim. If a concern is "I'd need to see definition X to be sure", say so precisely rather than asserting a hole. A specific counterexample (a prime where rank > r, or a vacuity case) beats a vague worry.
</grounding_rules>
