# Statement card - A2 with-following loss dominates readback product residual

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaProductResidualBridge.lean
```

Name:

```text
exists_pos_const_eventually_readbackProductResidual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase_nhdsWithin_rankCut_of_sourceChart_image_eq
```

The exported constant is under:

```text
DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData
```

## Claim

On a local with-following p.13/readback rank-cut patch, the original fixed-basis
square-Frobenius loss dominates the with-following readback product-residual
square-sum up to a positive scalar.

## Proved

Lean assumes a local set `V` with:

```text
readback(sourceChart z) = z              for z in V
sourceChart '' V = p13SourceSet cap readback^{-1}(V)
V subset determinant sector.
```

For any source-rank stratum and compatible fixed-base source datum, Lean
produces `c > 0` such that eventually on

```text
(p13SourceSet cap readback^{-1}(V)) cap sourceStratum
```

we have:

```text
c * squareSum(readback product residual of E) <= lossDLN(E).
```

The proof restricts the existing fixed-base endpoint `lossDLN` lower bound from
the full source stratum to the rank-cut patch, uses determinant-sector equality
between the fixed p.13 residual block and the with-following product residual,
uses the local left inverse to replace source-chart residuals by readback
residuals, and drops the nonnegative regular square-sum term.

## Assumed

- The local image equality and local left inverse for `sourceChart`/`readback`.
- The determinant-sector support `V subset detSector`.
- A fixed-base `PaperEndpointFixedBaseRegularCoordinateSourceData` at
  `sourceChart z0`.
- The centering equality identifying `sourceChart z0` with the fixed reverse
  edge family.
- Fixed endpoint bases for the original `lossDLN` expression.

## Cited

None.

## Deferred

No source coverage, source-rank atlas coverage, source-prior transport,
determinant/raw Haar transport, residual integrability, normal crossings, pole
order, or RLCT extraction.

## Status

Implemented and proved.  Focused `lake env lean`, focused module build,
`DLNFibre.lean` elaboration, no-sorry audit, whitespace checks, forbidden-marker
scan, and direct axiom probe passed.  The declaration reports only
`[propext, Classical.choice, Quot.sound]`.  Xhigh reviewer `Aquinas the 2nd`
found no theorem-boundary or proof-scope issues and marked the statement card
ready.
