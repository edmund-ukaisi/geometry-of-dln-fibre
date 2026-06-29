# Review - A2 Case 2 produced source-rank point readout

Date: 2026-06-29.

Reviewer: xhigh read-only `Dewey the 2nd`.

Status: pass after correction.

## Scope

Reviewed the Lean theorem

```text
exists_case2EndpointTransport_sourceEdgeFamilyOfData_mem_sourceRankStratum_and_localSource_and_residualBlockCoordinateMap_eq_value_of_pivot_ne_zero
```

in `RetainedPassiveCase2LocalJacobianMeasure.lean`, plus the reproduction and
statement-card notes for this slice.

## Correction Checked

The first review found that a uniform hypothesis

```text
forall yNext,
  r + rank(case2SuccessorSelectedEntryMatrix ... yNext ...) = rEdge 1
```

was too strong for this point-production theorem and likely vacuous for the
intended punctured selected-entry chart.  The theorem was corrected to require
the edge-1 rank equation only at

```text
SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext value.
```

The follow-up review confirmed that the produced witness is this same
preimage coordinate and that the pointwise rank equation is passed to
`case2EndpointTransport_sourceEdgeFamilyOfData_mem_sourceRankStratum`.

## Checks

The reviewer found no hidden source-rank coverage, source/image equality,
source-prior transport, Jacobian compatibility, normal-crossing, pole-order,
or RLCT claim.

The reviewer reported that these read-only checks passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
scripts/sorries
git diff --check
```

and that a direct axiom probe for the theorem reported only
`[propext, Classical.choice, Quot.sound]`.

## Result

Pass.  The theorem and notes now match: this is a point-production/source-rank
support package with a pointwise successor-rank hypothesis at the produced
fixed-pivot inverse coordinate.
