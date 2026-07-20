# Statement card — thread 09 sub-task W0: the closed/exact indexing bridge

Thread 09 (count composition), expedition `theta-components`. Branch `expedition/theta-components`,
base commit `a6cd85a8` (+ uncommitted: `lean/DLNFibre/Core/TopDimMinPrimesW0.lean`). The theorem
below builds green, sorry-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`). Module NOT
yet wired into `DLNFibre.lean` (single-writer aggregator — controller to add the import at the end).

---

## What this sub-task is

The W0 rung of the fibre-`θ` count transport: show that passing from the **closed** rank-`≤ r`
locus `Σ̄^r` to the **exact** rank-`= r` locus `Σ^r` does not change the top-dimensional
minimal-prime count, on the coordinate-ring side. The chart transport works with the exact-rank
locus `Σ^r` (the `detΔ`-unit chart sees only rank-exactly-`r` tuples), whereas the `(C, θ)` count
is anchored on the closed locus `Σ̄^r` (`sigmaIdeal`, whose minimal primes are the irreducible
components). W0 is the bridge identifying their top-dimensional counts.

---

> **Claim (W0 — closed/exact indexing bridge).** Over an algebraically closed field of
> characteristic zero, for a dimension vector `d : Fin (N+1) → ℕ` and `r` with the corner-`r`
> Kostant set nonempty, the closed rank-`≤ r` locus ideal `sigmaIdeal d r` and the exact rank-`= r`
> locus ideal `vanishingIdeal (canonicalCoord d '' productRankLocus d r)` carry the **same**
> top-dimensional minimal-prime count.
>
> - **Lean:** `DLNFibre.Core.ncard_topDimMinPrimes_sigma_eq_sweepSigma`
>   (`lean/DLNFibre/Core/TopDimMinPrimesW0.lean` @ `a6cd85a8`).
> - **Gloss.** `(TopDimMinPrimes (R ⧸ sigmaIdeal d r)).ncard = (TopDimMinPrimes (R ⧸ vanishingIdeal
>   (canonicalCoord d '' productRankLocus d r))).ncard`, where `R = MvPolynomial (RepCoord d) k`.
>   The number of top-dimensional irreducible components is the same whether read off the closed
>   locus `Σ̄^r` or the exact locus `Σ^r`.
> - **Proved.** Unconditionally given `[IsAlgClosed k] [CharZero k]` and
>   `(kostantPartitions d r).Nonempty`. Mechanism: both counts equal `(quotTopDimSet ·).ncard`
>   (`ncard_topDimMinPrimes_quotient_eq`, thread 08), so it reduces to a `quotTopDimSet` set
>   equality. Both ideals have height `C = (cCodim d r h).toNat` (`height_sigmaIdeal_eq_cCodim`;
>   `Ieq.height = codimRepCanonical (productRankLocus d r) = C` from
>   `codimRepCanonical_productRankLocus_eq_cCodim_enat`), and `Ile ≤ Ieq` (anti-monotone
>   `vanishingIdeal` against `Σ^r ⊆ Σ̄^r`). On a minimal prime, top-dimensional ⟺ `height = C`
>   (`ringKrullDim_quotient_eq_iff_height_eq`). The cheap direction (`Ieq`→`Ile`) is `Ile ≤ Ieq ≤ q`
>   + `Ideal.mem_minimalPrimes_of_height_eq`; the hard direction (`Ile`→`Ieq`) uses the recovery
>   `exists_kostantPartition_partitionIdeal_eq_of` (strict corner-monotonicity discharged by
>   `cCodim_zero_strict`) to write `q` as a corner-`r` realizer's orbit ideal, giving `Ieq ≤ q` via
>   `vanishingIdeal_productRankLocus_le_orbitRankLocus` (the `Fin (N+1)` re-proof of the SourceNoDrop
>   per-component containment), then again `Ideal.mem_minimalPrimes_of_height_eq`.
> - **Assumed.** None beyond the stated hypotheses (`[IsAlgClosed k] [CharZero k]`,
>   `(kostantPartitions d r).Nonempty`).
> - **Cited.** None — every input is a LANDED in-repo lemma or a Mathlib commutative-algebra lemma
>   (`Ideal.mem_minimalPrimes_of_height_eq`, `Ideal.minimalPrimes_isPrime`).
> - **Deferred.** None for W0 itself. (Downstream: the controller instantiates this at `Fin (N+2)`
>   when composing with the chart transport W1/W2 — that composition is a separate sub-task, not
>   carried here.)
> - **Status.** sorry-free + reviewed (fidelity PASS, `reviewer` + decorrelated Codex, `a6cd85a8`).
>   The reviewer noted the proof in fact establishes the stronger `quotTopDimSet` *set* equality
>   (not mere equinumerosity), and that the hard-direction realizer recovery is load-bearing (the
>   cheap "equal height + `Ile ≤ Ieq`" inference is unsound on its own — Codex confirmed with a
>   counterexample).

> **Claim (W0 set-level form — closed `=` exact `quotTopDimSet`).** The closed and exact loci select
> the same top-dimensional minimal primes (the set equality of which the count equality is a
> corollary).
>
> - **Lean:** `DLNFibre.Core.quotTopDimSet_sigma_eq_sweepSigma`
>   (`lean/DLNFibre/Core/TopDimMinPrimesW0.lean` @ `a6cd85a8`).
> - **Gloss.** `quotTopDimSet (sigmaIdeal d r) = quotTopDimSet (vanishingIdeal (canonicalCoord d ''
>   productRankLocus d r))`. The genuine W0 content; `ncard_topDimMinPrimes_sigma_eq_sweepSigma` is
>   the one-line `ncard` corollary (`ncard_topDimMinPrimes_quotient_eq` twice + this set equality).
> - **Proved.** Same hypotheses; same mechanism as the hard/easy directions above.
> - **Status.** sorry-free + reviewed.

> **Claim (closed-locus `quotTopDimSet` `=` `topComponents`).** The dimension-based top-dim minimal
> primes of `sigmaIdeal` are the height-based `Σ̄^r` top components.
>
> - **Lean:** `DLNFibre.Core.quotTopDimSet_sigma_eq_topComponents`
>   (`lean/DLNFibre/Core/TopDimMinPrimesW0.lean` @ `a6cd85a8`).
> - **Gloss.** `quotTopDimSet (sigmaIdeal d r) = topComponents d r h`. On a minimal prime,
>   `ringKrullDim (R ⧸ q) = ringKrullDim (R ⧸ sigmaIdeal) ↔ q.height = C`
>   (`ringKrullDim_quotient_eq_iff_height_eq` + `height_sigmaIdeal_eq_cCodim`); both sides are
>   `{q ∈ sigmaIdeal.minimalPrimes | <top-dim predicate>}`.
> - **Proved.** Same hypotheses. (Names the height↔dim conversion already implicit in
>   `TopComponentsTopDim.ncard_topComponents_eq_ncard_topDimMinPrimes_sigma`'s proof.)
> - **Status.** sorry-free + reviewed.

> **Claim (exact-locus `quotTopDimSet` `=` `topComponents` — the W1-application form).** The
> exact-locus dimension-based top components are the height-based `Σ̄^r` top components.
>
> - **Lean:** `DLNFibre.Core.quotTopDimSet_sweepSigma_eq_topComponents`
>   (`lean/DLNFibre/Core/TopDimMinPrimesW0.lean` @ `a6cd85a8`).
> - **Gloss.** `quotTopDimSet (vanishingIdeal (canonicalCoord d '' productRankLocus d r)) =
>   topComponents d r h`. The form the W1 keystone application consumes. Composes
>   `quotTopDimSet_sigma_eq_sweepSigma` (closed `=` exact) with `quotTopDimSet_sigma_eq_topComponents`
>   (closed `=` `topComponents`).
> - **Proved.** Same hypotheses; pure composition of the two preceding set equalities.
> - **Status.** sorry-free + reviewed.

> **Claim (supporting — per-component containment over `Fin (N+1)`).** `Ieq ⊆` the orbit-rank-locus
> ideal of any corner-`r` Kostant realizer.
>
> - **Lean:** `DLNFibre.Core.vanishingIdeal_productRankLocus_le_orbitRankLocus`
>   (`lean/DLNFibre/Core/TopDimMinPrimesW0.lean` @ `a6cd85a8`).
> - **Gloss.** `vanishingIdeal (canonicalCoord d '' productRankLocus d r) ≤ vanishingIdeal
>   (canonicalCoord d '' orbitRankLocus (realizerD hm))` for `hm : m ∈ kostantPartitions d r`. The
>   realizer's orbit sits in `Σ^r`, so anti-monotone `vanishingIdeal` gives the containment. The
>   `Fin (N+1)` analogue of `Core.SourceNoDrop.vanishingIdeal_sweepSigma_le_orbitRankLocus`
>   (which is stated only over `Fin (N+2)`).
> - **Proved.** Unconditionally given `[Infinite k]` (auto-resolved from `[IsAlgClosed k]
>   [CharZero k]` at the use site).
> - **Status.** sorry-free.

---

## Build / audit

- `scripts/lb DLNFibre.Core.TopDimMinPrimesW0` — green, no warnings on the file.
- `#print axioms` on all four theorems (`quotTopDimSet_sigma_eq_topComponents`,
  `quotTopDimSet_sigma_eq_sweepSigma`, `quotTopDimSet_sweepSigma_eq_topComponents`,
  `ncard_topDimMinPrimes_sigma_eq_sweepSigma`) → `[propext, Classical.choice, Quot.sound]`.
- `scripts/sorries` — 0 sorry / 0 axiom / 0 native_decide / 0 #exit (whole library).

## Note (addendum — extra W1-application lemmas)

The module now exposes the W0 content at the **set level** (`quotTopDimSet_sigma_eq_sweepSigma`) with
the `ncard` headline as its corollary, plus `quotTopDimSet_sigma_eq_topComponents` and
`quotTopDimSet_sweepSigma_eq_topComponents` (the form the W1 keystone application consumes), added at
the formaliser's request. The fidelity review (above) covered the original `ncard` headline + the
supporting containment lemma; the three set-level lemmas are an exposure of the same proved content
(same mechanism, no new hypothesis or citation) and inherit the review, but a controller may re-gate
them if desired.
