# Statement card - A4 Case 2 constructed Cprime Q/P

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.exists_case2DisplayedQP_mul_arbitraryPivotFirstFollowingFactor_of_flat_weights`
- `DLNFibre.DLN.Aoyagi.CorrectedCase2NewLabelCertificate.exists_case2DisplayedQP_mul_freeFollowingFactor_of_postData`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_constructedCprime_paperQP`

## Statement

Lean now proves the displayed Case 2 `Q/P` product identity with an arbitrary
pivot-first chart-coordinate following factor `Cprime`.

The old pivot-first following factor is constructed as

```text
Csrc = Q*Cprime.
```

The supplied-boundary theorem rewrites the product as

```text
(P * weighted source-substituted block) * Csrc
  = (weighted D''') * Cprime.
```

## Proved

- The flat-weight `Q/P` row-operation identity works for an arbitrary
  pivot-first following factor.
- Supplied Case 2 recurrence post-data rewrites the right-hand row weights to
  the post-state weights.
- A supplied displayed boundary exposes the paper-named `D'''` identity with
  free `Cprime`.

## Assumed

- Displayed Case 2 continuation and supplied displayed-boundary data.
- Supplied recurrence post-data and old Case 2 gap, as carried by the boundary.
- The free chart-coordinate matrix `Cprime`.

## Cited

- None in Lean. This is finite matrix algebra using the existing displayed
  `Q/P` identity and the constructed-`Cprime` inverse identity.

## Deferred

- Construction of a total source-coordinate following function from `Cprime`.
- Source-produced next `C'^(S+1)`.
- Chart-produced recurrence or exponent post-data.
- Successor chart family, chart coverage, coordinate regularity, transition
  invariance, Jacobian arithmetic, normal crossings, RLCT extraction,
  arbitrary-pivot coverage, terminal relabeling, and printed-vector repair.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
