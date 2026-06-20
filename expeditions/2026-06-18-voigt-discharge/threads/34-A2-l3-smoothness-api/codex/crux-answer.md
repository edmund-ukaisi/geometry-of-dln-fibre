**Verdict**

You do **not** have to prove `IsOpen O_M` to finish L3. The cleanest route is to avoid that target and prove instead:

```lean
Dense {p : PrimeSpectrum A | ∃ x ∈ orbitSet M, p = m_x}
```

where `A = R ⧸ I`, `R = MvPolynomial (RepCoord d) k`, `I = vanishingIdeal k (canonicalCoord '' orbitRankLocus M)`, and `m_x` is the quotient maximal ideal induced by evaluation at the orbit point `x`.

Then the dense open smooth locus intersects this dense set of orbit closed points. The point you get is automatically in the orbit, so translation carries smoothness to `m_M`. This avoids local-closedness/open-orbit machinery.

**Why This Works**

The key ring-side lemma is:

```lean
theorem dense_orbitClosedPoints_of_vanishingIdeal_eq
    (hI : vanishingIdeal k (orbitSet M)
        = vanishingIdeal k (canonicalCoord d '' orbitRankLocus M)) :
  Dense {p : PrimeSpectrum A | ∃ x ∈ orbitSet M, p = pointIdealInQuotient x}
```

Proof idea: `p` ranges over kernels of lifted evaluations `A →ₐ[k] k`. The vanishing ideal of these points in `A` is `⊥`, because a representative polynomial vanishes on all orbit points iff it lies in `vanishingIdeal (orbitSet M) = I`. Hence their closure is `V(⊥)=Spec A`.

Then use:

```lean
Dense.inter_open_nonempty denseOrbitPoints
  f.smoothLocus.2
  f.dense_smoothLocus_of_perfectField.nonempty
```

This gives a smooth point already carrying an orbit witness.

**About The Rank-Stratification Idea**

Mathematically correct, with one caveat: do not claim each single condition

```text
rankPattern A i j ≤ rankPattern M i j - 1
```

is itself an `orbitRankLocus` of a smaller tuple. It is a determinantal closed locus; that is enough. The modified rank pattern may not be realizable as one tuple’s full rank pattern.

Inside `Z_M`, the boundary is

```text
Z_M \ O_M =
⋃_{i≤j, r_ij > 0} {A ∈ Z_M | rankPattern A i j ≤ r_ij - 1}
```

and each term is cut out by all `r_ij × r_ij` minors of the interval product. So the scheme-theoretic rank stratum is open in `Spec A`.

**Important Point-Set Warning**

The point-set `orbitSet M : Set (RepCoord d → k)` should not be transported literally as an open subset of `Spec A`. Its image consists only of closed points, and a set of closed points alone is generally not open in a positive-dimensional scheme.

The honest open is the rank-equality stratum:

```lean
U_M =
⋂_{i≤j} ⋃_{er ec}
  D(quotientMap (minorPoly i j hij er ec))
```

where `er, ec` range over `r_ij × r_ij` minors, with `r_ij = rankPattern M i j hij`. Its closed `k`-points are exactly `O_M`.

Equivalently, after distributing finite intersections over finite unions, `U_M` is a finite union of basic opens `D(f)`. But it is not equal to the closed-point set `O_M`; it is the scheme-open whose closed points are the orbit.

**Difficulty Ranking**

For the actual L3 goal: **CHEAP to MODERATE**, not a Borel/local-closed-orbit crux.

If you use the dense-orbit-closed-points route, the single hardest lemma is:

```lean
PrimeSpectrum.vanishingIdeal orbitClosedPointsInQuotient = ⊥
```

from the already landed vanishing-ideal equality.

If you insist on proving the rank-stratum open, it is **MODERATE**: one needs to package the existing minor machinery into “rank ≥ r is a finite union of basic opens” and prove the closed-point equivalence. No Borel theorem is needed.

**L3 Ladder Sanity Check**

Your 5-7 module count is plausible. No circularity in generic smoothness: `dense_smoothLocus_of_perfectField` only needs reduced + locally finite presentation. The orbit/rank step is only needed to ensure the smooth point lies in the orbit.

I would adjust L3.3 to:

```text
L3.3 dense orbit closed-points in Spec A
```

rather than `IsOpen O_M`. That uses L6 directly and avoids the point-set topology trap.