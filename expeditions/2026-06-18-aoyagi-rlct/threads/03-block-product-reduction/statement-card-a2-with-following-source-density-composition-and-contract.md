# Statement card - A2 with-following source-density composition and contract

## Lean Target

Files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaFormalProductSourceImageContract.lean
```

Names:

```text
aemeasurable_case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity_unweightedSource
case2PassiveThetaWithFollowingFactorReferenceSourceMeasure_withDensity_eq_unweighted_withDensity_selectedEntrySourceDensity_mul
case2PassiveThetaWithFollowingFactorReferenceSourceMeasure_withDensity_restrict_eq_unweighted_withDensity_selectedEntrySourceDensity_mul_restrict
exists_open_subset_a2FormalProductSourceImagePieceContract_case2PassiveThetaWithFollowingFactorEndpointSourceChart_of_rawMap_eq_restrict_rawSource
```

## Claim

The selected-entry density can be multiplied with any further source-side
density over the unweighted enlarged Case 2 source.  Separately, a local
raw-pushforward identity to the raw-order source-recursive Haar restriction
builds the with-following A2 formal-product/source-image contract with
constant density `1` and bound `1`.

## Proved

Lean proves the unrestricted and restricted source-density identities:

```text
referenceSource.withDensity rawDensity =
  unweightedSource.withDensity
    (fun z => selectedEntryDensity z * rawDensity z)
```

and

```text
(referenceSource.withDensity rawDensity)|Omega =
  (unweightedSource.withDensity
    (fun z => selectedEntryDensity z * rawDensity z))|Omega.
```

Lean also proves the contract constructor: after a local shrink, the supplied
raw-pushforward equality implies an `A2Case2FormalProductSourceImagePieceContract`
whose density is `fun _ => 1` and whose bound is `1`.

## Assumed

For density composition: a.e. measurability of the extra source density for
the unweighted source or its restriction.

For the contract constructor: the raw-pushforward identity, chart-piece
measurability, `chartPiece subset sourceChart '' V`, and
`chartPiece subset p13SourceSet`.

## Cited

None.

## Deferred

No raw Haar transport theorem, no determinant-chart Haar transport, no
source-image coverage, no source-prior transport, no density lower-bound
removal, no normal crossings, no pole order, and no RLCT extraction.

## Structure & Ideas Observed

The selected-entry source density is pulled from the center coordinate through
two product factors.  The density multiplication is exactly Mathlib
`withDensity_mul_0`.

The contract constructor combines two local shrinks: local source-chart
readback/injectivity/continuity first, then the raw-pushforward
formal-product/source-reference theorem inside that neighborhood.

## Status

Implemented; focused elaboration passed before full verification.
