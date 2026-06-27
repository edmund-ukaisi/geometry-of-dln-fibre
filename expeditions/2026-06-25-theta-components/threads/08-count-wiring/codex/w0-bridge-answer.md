VERDICT: **cheap route exists**.

Let `I = vanishingIdeal(Σ̄^r)` and `J = vanishingIdeal(Σ^r)`. The free inclusion is

`I ≤ J`

because `Σ^r ⊆ Σ̄^r`.

The non-free but cheap top-dimensional inclusion is:

```lean
∀ p ∈ topComponents d r hr, J ≤ p
```

Geometrically: every top component of `Σ̄^r` is `vanishingIdeal(Ō_realizerD(m))` for a corner-`r` minimising partition `m`; the actual orbit of `realizerD m` lies inside `Σ^r`; therefore every polynomial vanishing on `Σ^r` vanishes on that orbit closure. This uses only density of the exact-rank orbit inside its own top component, not `Σ̄^r ⊆ repClosure(Σ^r)`.

The formal direction is:

```lean
orbitSet (realizerD hm) ⊆ canonicalCoord d '' productRankLocus d r
⇒ J ≤ vanishingIdeal (orbitSet (realizerD hm))
= vanishingIdeal (canonicalCoord d '' orbitRankLocus (realizerD hm))
= partitionIdeal d r m = p
```

using `vanishingIdeal_anti_mono` [CONFIDENT] and `vanishingIdeal_orbitRankLocus_eq_orbitSet` [CONFIDENT, local].

Then the ambient top minimal primes coincide:

```lean
{p ∈ I.minimalPrimes | p.height = I.height}
=
{p ∈ J.minimalPrimes | p.height = J.height}
```

Proof sketch:

- Forward: if `p ∈ Min(I)` is top and `J ≤ p`, then `p ∈ Min(J)`, since any `q` with `J ≤ q ≤ p` also has `I ≤ q ≤ p`.
- Reverse: if `q ∈ Min(J)` is top, choose `p ∈ Min(I)` with `p ≤ q` [clean math CONFIDENT; exact Mathlib lemma name UNSURE]. Since `I.height = J.height = C`, topness gives `q.height = C`, while `p.height ≥ I.height` and `p.height ≤ q.height`; hence equal. If `p < q`, strict height monotonicity for prime ideals contradicts equality, so `p = q`. `Ideal.height_strict_mono_of_is_prime` exists and is already used locally [CONFIDENT].

The key lower-strata fact is: **rank `< r` orbit closures have strictly larger codimension than `C`**, equivalently they cannot be top-dimensional components. In code this is the strict corner-monotonicity/recovery package: `exists_kostantPartition_partitionIdeal_eq_of` via `cCodim_corner_strict_of` / `cCodim_zero_strict` [CONFIDENT local].

This is strictly weaker than the declined density theorem. The declined theorem says all of `Σ̄^r` lies in `repClosure(Σ^r)`, including lower strata. The cheap lemma only says the **top components** do.

Hazard: dimension equality alone is not enough. A closed set with two top components and an exact subset dense in only one has the same dimension but different top-component count. Here that hazard is killed precisely by the recovery statement: every top closed component is a rank-exact orbit closure. Reducibility of `Σ^r` is harmless; the proof is componentwise. Emptiness is not harmless: if `productRankLocus d r` is empty while `productRankLocusLE d r` is not, counts can differ. The usual `hr : (kostantPartitions d r).Nonempty`/realizer hypothesis rules this out.