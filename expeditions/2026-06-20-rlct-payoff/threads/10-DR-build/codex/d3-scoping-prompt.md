# D3 honest-scoping decision (RLCT payoff, r=0, Lean 4 / Mathlib v4.29)

## Context
Formalising the geometric codimension identity for the DLN multiplication-fibre at r=0, en route to
the RLCT payoff `rlct = C/2` with a Cited (Aoyagi) interface. I must NOT overclaim (the harness's
`rlct_…` trap: a name asserting more than is proved).

## Landed Core API (over a field k; the geometric ones need [IsAlgClosed k][CharZero k]):
- `fibre d B := {A | mult d A = B}`; `productRankLocusLE d r := {A | rank(mult A) ≤ r}`.
- `codimRepCanonical Z := Ideal.height (vanishingIdeal (canonicalCoord d '' Z))` : ℕ∞  (codim of Zariski closure).
- `sigmaIdeal d r := vanishingIdeal (canonicalCoord d '' productRankLocusLE d r)`.
- `sigmaIdeal_eq_sInf_orbitIdeals : sigmaIdeal d r = sInf (orbitIdeals d r)` where
  `orbitIdeals d r := (M ↦ vanishingIdeal (canonicalCoord d '' orbitRankLocus M)) '' {M | rank(mult M) ≤ r}`.
- `minimalPrimes_sigmaIdeal_eq [IsAlgClosed k] : (sigmaIdeal d r).minimalPrimes = {p | p ∈ orbitIdeals d r ∧ ∀ q ∈ orbitIdeals d r, q ≤ p → p ≤ q}`.
- `orbitIdeals_isPrime`, `orbitIdeals_finite`.
- `codimRepCanonical_orbitRankLocus_eq_height : codimRepCanonical (orbitRankLocus M) = (vanishingIdeal (canonicalCoord d '' orbitRankLocus M)).height` (rfl).
- `cCodim_eq_inf_geomCodim [IsAlgClosed k][CharZero k] (d r) (h : (kostantPartitions d r).Nonempty) :
    cCodim d r h = (kostantPartitions d r).inf' h (fun m ↦ ((codimRepCanonical (orbitRankLocus (intervalDirectSum (listOfPartition m)))).toNat : ℤ))`.
- Mathlib: `Ideal.height I = ⨅ J ∈ I.minimalPrimes, J.primeHeight`; `height_eq_primeHeight` (prime ⟹ height=primeHeight);
  `height_strict_mono_of_is_prime` (I<J prime, finite height ⟹ height I < height J); finite Krull dim instance present.

## The two families differ by index type
- `sigmaIdeal`'s minimal primes range over `orbitIdeals d 0` = orbit ideals of corner-≤0 TUPLES M.
- `cCodim d 0` is an `inf'` over KOSTANT PARTITIONS m (realized as tuples `intervalDirectSum(listOfPartition m)`).
Both are corner-0 orbit closures, but indexed differently. Bridging `height(sigmaIdeal 0) = cCodim d 0`
needs: (a) `height(sInf finite primes) = ⨅ over the family of their heights` (= min codim, since non-minimal
ideals strictly contain minimal ⟹ strictly larger height); (b) the family `{codimRepCanonical(Ō_M) : corner M ≤ 0}`
and `{codimRepCanonical(Ō_{⊕listOfPartition m}) : m ∈ kostantPartitions d 0}` have the SAME minimum
(every corner-0 tuple's orbit = some Kostant partition's orbit, Gabriel; and vice versa).

## Question
1. Is `codimRepCanonical (productRankLocusLE d 0) = cCodim d 0` (cast ℕ∞↔ℤ/ℕ) the right honest D3 target,
   given it requires BOTH bridges (a) and (b)? Or is the honest scope-limited target
   `codimRepCanonical (fibre d 0) = ⨅_{M : corner ≤ 0} codimRepCanonical (orbitRankLocus M)` (bridge (a) only,
   the "codim of union = min codim of components", purely from Mathlib height + minimalPrimes_sigmaIdeal_eq),
   leaving the `= cCodim` (bridge (b), the Kostant-count identification) as a separately-named lemma or
   a roadmap step?
2. For the RLCT payoff R2 `rlct(lossDLN 0) = (cCodim d 0)/2`, which target do I actually need to land to
   make the payoff honest and non-vacuous — the full `= cCodim`, or does the (2,2,2) witness
   `cCodim_d222_zero = 3` + a concrete `codimRepCanonical(fibre d222 0) = 3` suffice to anchor it?
3. Estimate the Lean difficulty (LoC, friction) of bridge (a) `height(sInf finite primes) = ⨅ heights`
   and bridge (b) the Kostant↔corner-tuple min-codim identification. Flag if (b) is a multi-day step
   that should be roadmapped rather than attempted in a ~200-410 LoC module.
4. Name=content check: what is the most precise name for each target so the geometric codim claim is
   not confused with an aggregate-variety claim the Core explicitly says is NOT formalised?
