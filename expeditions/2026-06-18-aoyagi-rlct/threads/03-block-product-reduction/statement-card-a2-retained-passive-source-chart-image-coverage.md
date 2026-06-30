# Statement Card - A2 Retained-Passive Source-Chart Image Coverage

## Claim

Near the self-base point, retained-passive local-source membership yields an
explicit retained-passive determinant-chart datum whose fixed-base
retained-passive source chart is the given edge-family point.

Public Lean name:

```text
exists_open_paperEndpointFixedBaseRetainedPassiveP13SourceChart_image_coverage_of_selfBase
```

## Inputs Used

- the existing self-base local-source coverage theorem
  `exists_open_paperEndpointFixedBaseRetainedPassiveP13LocalSource_coverage_of_selfBase`;
- the definitional equality between local source and preimage of
  `paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet`;
- the retained-passive source edge-family homeomorphism
  `paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_homeomorph`.

## Output

Lean returns an open neighborhood `Ulocal` of the self-base point such that
`Ulocal` is contained in the retained-passive local source and, for every
`x in Ulocal`, there is determinant-chart coordinate data `data` with

```text
paperEndpointFixedBaseRetainedPassiveP13SourceChart W B U0 hU0 data =
  Cedge x.
```

The theorem also gives the same witness on

```text
Ulocal inter paperEndpointFixedBaseSourceRankStratum ...
```

for downstream source-rank-shaped consumers.

## Proof Shape

Take the open set from the existing local-source coverage theorem. For
`x in Ulocal`, local-source membership says `Cedge x` lies in the retained
passive source edge-family set. Put `Cedge x` into the source-set subtype,
apply the inverse of
`paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_homeomorph`, and use
the homeomorphism right-inverse law.

## Nonclaims

No Case 2 passive-theta coverage, no selected-entry coverage, no source-image
equality with a source-rank stratum, no original/source-prior transport, no
Haar/Jacobian transport, no normal crossings, no pole order, and no RLCT
extraction is proved.
