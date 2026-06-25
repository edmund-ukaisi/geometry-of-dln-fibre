# Statement Card - A2 measurable local source from source certificate

Date: 2026-06-25.

## Claim

A fixed-base local source certificate yields a concrete measurable local source
by intersecting an open neighborhood of the basepoint with Aoyagi's
source-rank stratum.  At the regular-coordinate source-data level, this local
source has the same `nhdsWithin x0` filter as the full source-rank stratum.

## Lean Names

```text
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_measurable_localSource

PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_measurable_localSource_of_measurable_edgeMatrix

PaperEndpointFixedBaseRegularCoordinateSourceData.exists_measurable_localSource_nhdsWithin_of_measurable_edgeMatrix
```

## Inputs Kept Explicit

- the fixed-base local source certificate, through `sourceData` in the wrapper;
- fixed-base edge-matrix measurability, for deriving source-rank-stratum
  measurability;
- the fixed base chain, complement, rank label, and edge-rank labels.

## Discharged Input

The theorem constructs the measurable local source set and proves basepoint
membership, inclusion in the source-rank stratum, source-rank conclusions on
that local source, and the regular-coordinate `nhdsWithin` equality.

## Nonclaims

No signed-box chart, chart image/source coverage theorem, weighted pushforward,
Jacobian/source-density transport, residual or source-density monomial-unit
identity, normal-crossing theorem, pole-order computation, or RLCT statement is
proved.

## Verification

Focused and full builds passed with the worktree-local Lake cache:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionEntryIdealBoundary
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb
```

`scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
`git diff --check` was clean.
