# Review - A2 Retained-Passive Raw-Order Local-Source COV Bridge

Date: 2026-06-27.

Reviewer: xhigh read-only reviewer `Parfit the 4th`.

Verdict: accepted.

## Checked Statement Shape

The measure is oriented as

```text
mu = Measure.map sourceChart (m.restrict T),
```

where `T` is the raw-order source-recursive determinant chart.  The conclusion
is the local-source restriction identity

```text
mu.restrict localSource =
  Measure.map (sourceChart o topologyTupleEdgeRawOrder)
    ((m.restrict S).withDensity (ofReal o J)).
```

Here `S` is the tuple determinant chart and `J` is the forward raw-order
absolute Jacobian determinant.

## Hypotheses

The hypotheses are sufficient and explicit:

- `sourceChart` is a.e.-measurable on `m.restrict T`;
- `Cedge` is continuous, supplying measurability of the retained-passive local
  source through the existing local-source handoff;
- the fixed-base edge matrices of `Cedge (sourceChart y)` agree pointwise with
  `edgeFamilyOfRawOrderTuple y` for every `y in T`;
- the underlying tuple measure is an additive Haar measure, as required by the
  already-proved retained-passive raw-order COV theorem.

The source lemma correctly transports `y in T` across the pointwise realization
identity into membership of `sourceChart y` in the retained-passive p.13 local
source.

## Nonclaims

This slice does not prove determinant-density continuity, inverse-density
measurability, original DLN source-prior transport, selected-entry target-image
equality, source-rank coverage, normal crossings, pole order, or RLCT.

## Bookkeeping

The statement card verification block has been updated after recording this
review and running the Lean checks.
