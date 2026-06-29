# Reproduction - A2 local-source two-sided loss-density handoff

Date: 2026-06-29.

Status: pen-and-paper checked; Lean formalised as a supplied-bound
filter-to-measure handoff.

## Source Anchor

Aoyagi PDF p. 13 reduces the regular-coordinate layer to the square model

```text
q(x,u) = residualSquareSum(x) + regularSquareSum(u).
```

The previous checkpoint proved a supplied two-sided comparison iff once the
four comparison hypotheses are already available almost everywhere on a product
measure.  The present step is the local-source plumbing needed before that
consumer: it turns source-local, uniform-in-regular-fiber comparison hypotheses
into four a.e. product-measure facts after shrinking the base neighborhood.

This is not a proof of the comparison bounds, the p.13 product chart, or any
loss-density integrability theorem.

## Calculation

Fix a source set `source`, a base point `x0`, and a product regular-coordinate
measure `nu`.  Let

```text
model(x,u) =
  aoyagiCoordinateSquareSum
    (paperEndpointFixedBaseResidualBlockCoordinateMap ... Cedge x)
  + aoyagiCoordinateSquareSum (fun i => u i).
```

Assume that in `nhdsWithin x0 source`, uniformly for all regular coordinates
`u` in the ball `ball(0,R)`, the following four inequalities are supplied:

```text
cL * model(x,u) <= loss(x,u),
loss(x,u) <= CL * model(x,u),
dRho <= density(x,u),
density(x,u) <= DRho.
```

Bundle these four eventual predicates into a single base predicate

```text
P(x) :=
  (forall u in ball(0,R), cL * model(x,u) <= loss(x,u))
  and
  (forall u in ball(0,R), loss(x,u) <= CL * model(x,u))
  and
  (forall u in ball(0,R), dRho <= density(x,u))
  and
  (forall u in ball(0,R), density(x,u) <= DRho).
```

The existing local-measure helper says that if `P` holds eventually in
`nhdsWithin x0 source`, then there is an open set `U` with `x0 in U` such that
`P(z.1)` holds for almost every `z` with respect to

```text
(mu.restrict (U inter source)).prod nu.
```

Projecting the four conjunctions gives the four a.e. product hypotheses needed
by the later two-sided supplied-bound comparison iff, on one common restricted
product measure and one common open set `U`.

## Lean Shape

Lean formalises this in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

with:

```text
exists_open_ae_restrict_localSource_prod_p13RegularCoordinates_two_sided_loss_density_bounds
```

The proof is mechanical:

1. Introduce the regular-coordinate index abbreviation `rho`.
2. Bundle the four source-filter hypotheses using `filter_upwards`.
3. Apply `exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin`.
4. Project the four nested conjunctions over the resulting product-measure
   a.e. statement.

No positivity assumptions on `R`, `cL`, `CL`, `dRho`, or `DRho` appear in this
handoff.  Those belong to the later integrability iff, not to the
filter-to-measure transfer.

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

passed.

## Nonclaims

- No proof of the four supplied comparison bounds.
- No construction or identification of Aoyagi's p.13 product chart.
- No source-prior, Jacobian, density, or product-measure transport theorem.
- No proof of residual positivity, residual boundedness, residual
  measurability, or residual negative-power integrability.
- No integrability iff, normal-crossing theorem, pole-order theorem, or RLCT
  extraction.
