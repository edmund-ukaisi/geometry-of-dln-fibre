# Statement Card - A2 Case 2 produced local-source point readout

Date: 2026-06-29.

## Claim

For endpoint-transported explicit Case 2 data, any selected-entry residual
center value with nonzero selected pivot has a produced retained-passive p.13
local-source edge-family point whose fixed-base residual-coordinate readout is
that value.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Declaration:

```text
exists_case2EndpointTransport_sourceEdgeFamilyOfData_mem_localSource_and_residualBlockCoordinateMap_eq_value_of_pivot_ne_zero
```

## Inputs Kept Explicit

- finite two-edge Case 2 endpoint setup;
- `hS`, continuing and successor inequalities `hcont`, `hnext`;
- fixed total-kernel complement;
- endpoint transport equivalences;
- target selected-entry center value;
- nonzero selected pivot value.

## Nonclaims

No source-rank-stratum membership of the produced point, no selected-entry
source-rank coverage, no source/image equality, no source-prior transport, no
Jacobian comparison, no analytic atlas, no normal crossings, no pole order,
and no RLCT statement.

## Verification Plan

Focused Lean build passed:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

`lean/scripts/sorries` reported no forbidden declarations or exits,
`git diff --check` passed, and the touched-Lean-file forbidden-marker scan was
clean.  Independent xhigh review passed in
`review-a2-case2-produced-local-source-point-readout.md`.
