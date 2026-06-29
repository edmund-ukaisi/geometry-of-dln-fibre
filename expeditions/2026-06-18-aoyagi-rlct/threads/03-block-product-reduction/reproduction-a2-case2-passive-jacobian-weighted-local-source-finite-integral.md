# Reproduction - A2 Case 2 Passive Jacobian-Weighted Local-Source Finite Integral

Date: 2026-06-29.

Status: controller pen-and-paper reproduction before Lean banking.  This is a
local-source finite-integral handoff for the same chart-produced
Jacobian-weighted passive product-domain measure as the residual-source theorem.

## Question

The previous theorem constructs an open determinant neighborhood `Udom` of
`z0`.  For

```text
jacobianWeightedMeasure =
  (sourceMeasure.restrict Udom).withDensity
    (fun z => ofReal (J z))

muJ = Measure.map sourceChart jacobianWeightedMeasure
```

it proves the retained-passive residual-source hypotheses:

```text
for muJ.restrict localSource-a.e. E,
  0 < squareSum(residual(E))

residualNegPowerIntegrableOn localSource muJ t.
```

The reusable p.13 local-source finite-integral theorem says that such residual
hypotheses, together with the local regular-suspension loss lower bound and
density upper/lower bounds, imply finiteness of

```text
int^- (E,u),
  ofReal (1_{ball R}(u) *
    loss(E,u)^(-(t + regCount/2)) * density(E,u))
  d ((muJ.restrict (Ufin inter sourceStratum)).prod nu)
```

for some open source neighborhood `Ufin` of the fixed base edge family.

The intended new theorem should prove exactly this conclusion for `muJ`, without
the older raw-order inverse-Jacobian determinant-chart pushforward equality.

## Calculation

The fixed-base edge family is

```text
base p = reverseEdge W2 B2 p
```

viewed as a continuous linear map.  The source-coordinate map for the finite
integral theorem is the identity on edge families:

```text
Cedge E = E.
```

Thus the continuity and base equations required by the local-source theorem are

```text
Continuous Cedge          = continuous_id
Cedge base = base         = rfl.
```

Let `localSource` be the retained-passive p.13 local source for this identity
coordinate map, and let `sourceStratum` be the fixed-base source-rank stratum
from the supplied regular-coordinate source data.  The previous residual-source
theorem gives

```text
hpos_local :
  for muJ.restrict localSource-a.e. E,
    0 < squareSum(residual(E))

hbase_local :
  residualNegPowerIntegrableOn localSource muJ t.
```

The remaining inputs are the already standard local comparison hypotheses:

```text
hloss :
  eventually on nhdsWithin base localSource,
    for u in ball(0,R),
      c * (squareSum(residual(E)) + squareSum(u)) <= loss(E,u)

hdensity_nonneg :
  eventually on nhdsWithin base localSource,
    for u in ball(0,R), 0 <= density(E,u)

hdensity_le :
  eventually on nhdsWithin base localSource,
    for u in ball(0,R), density(E,u) <= C.
```

Under `0 < R`, `0 < c`, `0 <= C`, and `0 < t`, the local-source finite-integral
theorem applies directly and produces an open `Ufin` with `base in Ufin` and the
finite integral over

```text
(muJ.restrict (Ufin inter sourceStratum)).prod nu.
```

There is no determinant-chart Haar equality in this argument.  The only source
domain open set is `Udom`, already constructed inside the residual-source
theorem, and the only source measure in the conclusion is the corresponding
pushforward `muJ`.

## S-finiteness Check

The local-source finite-integral theorem requires `[SFinite muJ]`.  The
passive theorem assumes

```text
passiveMeasure univ < infinity.
```

Inside the proof this gives a local instance

```text
IsFiniteMeasure passiveMeasure.
```

Mathlib then supplies sigma-finiteness and hence s-finiteness for
`passiveMeasure`; finite products, restrictions, `withDensity`, and measurable
maps preserve `SFinite`.  Therefore the concrete `muJ` should satisfy the
needed typeclass without adding a new mathematical hypothesis.

## Lean Target

Package the handoff as a theorem in
`RetainedPassiveCase2LocalJacobianMeasure.lean`, near the residual-source
theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass
```

The proof should:

1. invoke the residual-source packaging theorem to obtain `Udom` and
   residual-source hypotheses for `muJ`;
2. introduce the local finite-measure instance for `passiveMeasure`;
3. apply
   `exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource`
   to `muJ`, with `Cedge := fun E => E`, `hCedge := continuous_id`, and
   `hbase := rfl`;
4. return the open `Ufin` and finite integral conclusion.

## Dependency Boundary

This theorem uses only:

- the banked passive Jacobian-weighted residual-source theorem;
- the generic retained-passive local-source finite-integral theorem;
- finite-measure-to-s-finite measure bookkeeping.

It does not use an exact localized residual marginal, determinant-chart Haar
pushforward, raw/source Haar theorem, original source-prior transport,
source-prior Jacobian formula, source-image equality or local coverage,
normal-crossing construction, pole order, or RLCT extraction.

## Kill Conditions

- `muJ` cannot be made `SFinite` from the finite passive mass and existing
  product/withDensity/map instances.
- The residual-source theorem's `localSource` is not definitionally the
  `localSource` expected by the finite-integral consumer.
- The source-data base edge family is not the same fixed-base edge family used
  in the passive Case 2 chart.
- The local loss or density hypotheses are accidentally stated over a different
  source set than the retained-passive p.13 local source.
