# Reproduction - A2 source-stratum bounds local-source finite integral

Date: 2026-06-29.

Status: reproduced; Lean target landed.

## Scope

This slice bridges two localities that occur in the p. 13 handoff.
The loss and density estimates are naturally stated on the source-rank
stratum, while the residual positive-set and residual negative-power integral
may come from a retained-passive determinant-chart local source.  The bridge
assumes an explicit open neighborhood on which the source-rank stratum is
contained in that local source.

No source-rank coverage theorem, chart image equality, Jacobian transport,
normal-crossing certificate, pole order, or RLCT statement is produced here.

## Pen-And-Paper Calculation

Write

```text
S = paperEndpointFixedBaseSourceRankStratum,
L = localSource,
V = Ulocal.
```

Assume `V` is open, `x0 in V`, and

```text
V cap S subset V cap L.
```

Also assume residual positivity and residual negative-power integrability on
`L`:

```text
0 < residualSquareSum(x)              for mu|L-a.e. x,
int_L residualSquareSum(x)^(-t) dmu < infinity.
```

Finally assume that the lower loss bound and the density bounds hold eventually
for `x` in `nhdsWithin x0 S` and uniformly for regular coordinates `u` in the
ball `B_R(0)`:

```text
c * (residualSquareSum(x) + regularSquareSum(u)) <= loss(x,u),
0 <= density(x,u),
density(x,u) <= C.
```

The source-filter-to-product-a.e. lemma gives an open neighborhood `Ub` of
`x0` such that these three inequalities hold for

```text
(mu restricted to Ub cap S) prod nu
```

almost everywhere.

Set

```text
U = Ub cap V.
```

Then `U` is open and contains `x0`.  Moreover,

```text
U cap S subset Ub cap S,
```

so product-measure monotonicity restricts the three a.e. bounds from
`Ub cap S` to `U cap S`.

The coverage hypothesis also gives

```text
U cap S subset L.
```

Indeed, if `x in U cap S`, then `x in V cap S`; by coverage, `x in V cap L`,
so `x in L`.  Therefore residual positivity and residual negative-power
integrability restrict from `L` to `U cap S` by monotonicity of restricted
measures.

At this point all hypotheses of the finite-side regular-coordinate integrability
adapter hold for the base measure

```text
mu restricted to U cap S.
```

Applying that adapter gives

```text
int_{(U cap S) x B_R(0)}
  loss(x,u)^(-(t + regularVariableCount/2)) * density(x,u)
  d(mu prod nu)
< infinity.
```

This is the desired local source-stratum finite-integral conclusion.

## Lean Landing

The landed theorem is in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_bounds_locally_subset_localSource
```

It uses:

```text
exists_open_ae_restrict_source_prod_p13RegularCoordinates_loss_density_bounds
residualSourceHypotheses_mono
lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residual_power_lt_top
```

The proof also uses monotonicity of restricted product measures to move the
a.e. loss/density bounds from `Ubounds cap sourceStratum` to the smaller
`(Ubounds cap Ulocal) cap sourceStratum`.

## Boundary Checks

- The theorem consumes, but does not prove, the local coverage inclusion
  `Ulocal cap sourceStratum subset Ulocal cap localSource`.
- The theorem keeps residual positivity and residual negative-power
  integrability as local-source hypotheses.
- The theorem keeps loss and density bounds as source-stratum filter
  hypotheses.
- No selected-entry chart image equality is constructed.
- No source prior, Haar measure, or external Jacobian transport is identified.
- No analytic atlas, normal crossings, pole order, or RLCT extraction is
  proved.

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** Under an explicit local coverage inclusion,
source-stratum loss/density bounds and local-source residual hypotheses imply
the source-stratum restricted p. 13 finite-integral conclusion after shrinking
the open neighborhood.

**Assumed.** Fixed-base regular-coordinate source data, finite-dimensional
endpoints, add-Haar regular-coordinate measure, positivity of `R`, `c`, and
`t`, nonnegativity of `C`, source-stratum measurability, the open local coverage
neighborhood, residual positivity and residual negative-power integrability on
`localSource`, and the three source-stratum filter bounds.

**Cited.** None.

**Deferred.** Construction of source-rank coverage or selected-entry chart
image equality; residual readout along such a chart; source-prior/Jacobian
transport; analytic normal-crossing certificate construction; pole order; and
RLCT extraction.
