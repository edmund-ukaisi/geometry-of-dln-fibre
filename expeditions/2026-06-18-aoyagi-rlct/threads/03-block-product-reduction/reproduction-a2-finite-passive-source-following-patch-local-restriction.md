# A2 finite-passive source following-patch local restriction

Date: 2026-07-03

## Source step

Aoyagi's Case 2 calculation on pp. 19--21 reduces the residual product in the
enlarged source chart to a displayed residual block multiplied by the
following factor.  The previous Lean step packaged this as a finite
following-patch source theorem: if the independent following factor at the
base point has unit reindexed determinant, then there is a measurable finite
matrix-entry patch `P` containing that factor such that the product residual is
positive almost everywhere and has finite negative `t`-power integral over the
finite-passive source cylinder

```text
mu_P = (((passiveMeasure.prod weightedBox).prod followingRef)
  .restrict {z | z.2 in P}).
```

The source-chart construction in the next layer returns an open neighborhood
`V` of the base source point.  The following patch `P` is not open and should
not be used as the open set in that source-chart theorem.  The honest local
measure is instead `mu_P.restrict V`, equivalently the original source
restricted to the intersection of the cylinder and the open source-chart
neighborhood.

## Calculation

Let `f z` be the nonnegative integrand

```text
ofReal ((squareSum (productResidual z)) ^ (-t)).
```

From the finite cylinder theorem we have

```text
forall^ae z with respect to mu_P, 0 < squareSum (productResidual z),
integral f d mu_P < infinity.
```

For any set `V`, the restriction measure satisfies

```text
mu_P.restrict V <= mu_P.
```

Therefore

```text
integral f d (mu_P.restrict V)
  <= integral f d mu_P
  < infinity.
```

The a.e. positivity also restricts:

```text
(forall^ae z with respect to mu_P, Pos z)
  implies
(forall^ae z with respect to mu_P.restrict V, Pos z).
```

No measurability or openness of `V` is needed for this measure-theoretic
restriction step.  Openness will enter only when `V` is supplied by the
source-chart/readback theorem.

## Boundary

This proves only local restriction stability of the already-constructed finite
following-patch cylinder theorem.  It does not prove positive patch mass,
openness of the following patch, determinant-Haar/raw-Haar transport,
source-density or original-prior transport, normal crossings, pole order, or
RLCT extraction.  The determinant hypothesis remains a separate hypothesis on
the independent following factor `z0.2`, and finite passive-side mass remains
explicit.
