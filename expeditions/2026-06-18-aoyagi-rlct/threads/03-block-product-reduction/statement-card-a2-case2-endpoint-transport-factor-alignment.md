# Statement Card - A2 Case 2 endpoint-transport factor alignment

## Claim

For the endpoint-transported explicit Case 2 selected-entry retained-passive
datum, the two stored residual factors are Aoyagi's displayed post-pivot
residual block and displayed free following factor after submatrixing by the
forward endpoint equivalences.

Concretely, for

```text
data :=
  case2PostPivotSelectedEntryRetainedPassiveData
    (rho := rho) n hS hcont hnext yNext eNext
transported := data.endpointTransport e,
```

the intended Lean facts are:

```text
(transported.C 1).submatrix (e 2) (e 1)
  =
case2DisplayedPostPivotResidualBlock n hS hcont
  (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext)
```

and

```text
(transported.C 0).submatrix (e 1) (e 0)
  =
case2DisplayedPostPivotFreeFollowingFactor n hS hcont
  (case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext).
```

## Source / Proof Basis

Aoyagi PDF pp. 19-22 for the displayed continuing Case 2 post-pivot residual
block and following factor; the Lean endpoint-transport definition for the
finite reindexing step.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
```

Expected declarations:

```text
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_C_one_submatrix_eq_displayedPostPivotResidualBlock
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_C_zero_submatrix_eq_displayedPostPivotFreeFollowingFactor
```

A small datum-level consumer may use these to call the existing all-pivot
selected-entry residual-product theorem for this explicit transported datum
without supplying `hD` and `hF`.

## Nonclaims

This does not prove product nonzeroness, fixed-pivot nonzeroness, arbitrary
`ofTopologyTuple` factor alignment, fixed-base source-readback provenance,
source-prior transport, Jacobian comparison, normal crossings, pole order, or
RLCT.

## Verification Plan

Run the focused Lean build for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge`, then
`scripts/sorries`, `git diff --check`, touched-file marker search, direct axiom
probe for the new declarations, and xhigh read-only review.
