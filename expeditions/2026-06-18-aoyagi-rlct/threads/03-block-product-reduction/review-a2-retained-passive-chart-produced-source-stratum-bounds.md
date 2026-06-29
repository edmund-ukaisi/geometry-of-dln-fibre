# Review - A2 retained-passive chart-produced source-stratum bounds

Reviewer: xhigh read-only checker `Bacon the 2nd`.

Verdict: PASS.

## Findings

None.

The reviewed slice adds chart-produced source-stratum-bound finite-integral
handoffs without broadening the measure claim.  The source measure remains the
selected-entry signed-box pushforward through the supplied chart, and the new
generic theorem derives the retained-passive local-source restriction from
pointwise chart landing in the retained-passive p.13 local source.

The retained-data wrappers correctly keep `sourceStratum` distinct from the
retained-passive local source.  They move the loss and density estimates to
`nhdsWithin base sourceStratum` while preserving the local-source support and
selected-entry residual readout needed by the earlier handoff.

The Case 2 wrappers genuinely route through the existing
`retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData`
bridge.  They do not add source/image equality, original source-prior
transport, Jacobian comparison, normal crossings, pole order, or RLCT.

## Verification

Controller verification before banking:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
```

Both focused builds and the full library build passed.  The only warnings were
replayed from existing dependencies and from the existing import aggregator,
not from the touched files.  The reviewer separately ran `git diff --check`
and a forbidden-marker scan; both were clean.  The controller reran
`lean/scripts/sorries`; it reported no forbidden declarations or exits.

## Boundary

This is a local-measure API hardening slice.  It removes the explicit `hmap`
input for chart-produced selected-entry measures while allowing the final
regular-coordinate estimates to be stated on the source-rank stratum.  It does
not prove selected-entry source-rank coverage, original source-prior transport,
external-prior Jacobian comparison, analytic atlas construction, normal
crossings, pole order, or RLCT extraction.
