# Statement card: A2 retained-passive raw-order source-chart product-density pushforward

## Lean target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

## New names

```text
measure_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_sourceEdgeFamilySet_eq_self
measure_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_eq_restrict_sourceEdgeFamilySet
```

## Content

The first theorem states that the pushforward of the raw-order determinant
chart through the public raw-order source chart is already supported on

```text
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U0 hU0.
```

The second theorem specialises the product-determinant raw-order change of
variables to the public source chart, for an additive Haar measure `m`:

```text
map (fun z => sourceChart (topologyTupleEdgeRawOrder z))
  ((m.restrict S).withDensity (fun z => ofReal (Jprod z)))
=
(map sourceChart (m.restrict T)).restrict sourceEdgeFamilySet.
```

Together they expose the retained-passive source-production and measure
pushforward route that was previously hidden behind the local-source identity's
private `sourceChart` let-binding.

## Nonclaims

No original-source prior, full source-rank coverage, selected-entry signed-box
density identification, residual positivity, finite negative-power integral,
normal-crossing theorem, pole-order theorem, or RLCT theorem is claimed.
