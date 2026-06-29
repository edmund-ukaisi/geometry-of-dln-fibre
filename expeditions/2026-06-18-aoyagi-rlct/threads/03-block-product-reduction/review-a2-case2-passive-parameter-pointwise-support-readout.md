# Review - A2 Case 2 Passive-Parameter Pointwise Support Readout

Date: 2026-06-29.

Reviewer: Kuhn the 3rd, xhigh, read-only.

Verdict: PASS.

## Scope Checked

Lean theorems:

```text
case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_mem_sourceRankStratum
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_mem_sourceRankStratum_and_localSource_and_residualBlockCoordinateMap_eq_chartMap
```

Artifacts reviewed:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
reproduction-a2-case2-passive-parameter-pointwise-support-readout.md
statement-card-a2-case2-passive-parameter-pointwise-support-readout.md
theorem-ledger.md
```

## Findings

No issues found.

The Lean statements are pointwise only.  The source-rank theorem proves
membership of the constructed passive-sector source point in the named
source-rank stratum under the supplied pointwise rank equation.  The residual
readout theorem proves the fixed-base residual coordinate map is the
selected-entry center-coordinate chart map.  The combined theorem packages
source-rank membership, retained-passive p.13 local-source membership, and
the residual readout.

The assumptions are explicit.  The determinant-unit hypotheses are exactly:

```text
hCtop : forall theta, IsUnit ((Ctop theta).det)
hA1passive : forall theta p, IsUnit ((A1passive theta p).det)
```

The rank hypotheses are `hprod`, `hr0`, and pointwise `hr1`.  There are no
unit or rank hypotheses on `F2`, `A3passive`, or `F3`.

The source-rank proof is routed through determinant-chart membership for
`Ctop` and `A1passive`, selected-entry `C` rank facts, endpoint-transport
rank preservation for `C`, and the retained-passive source-rank membership
constructor from `C` ranks.

The residual-coordinate readout depends on passive fields only through the
constructed source point and determinant/readback bridge.  The matrix readout
comes from the stored selected-entry `C` factors.

The docs and ledger keep the nonclaim boundary explicit: no source-rank
coverage, source-image equality, arbitrary-source local coverage, measure
pushforward, source-prior or Jacobian transport, normal crossings, pole order,
or RLCT.

## Gates

Controller gates:

```text
git diff --check
scripts/sorries
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
lake env lean /tmp/aoyagi_case2_passive_support_readout_axioms.lean
```

Results: whitespace clean; `0 sorry, 0 #exit, 0 native_decide, 0 axiom`;
focused build passed; direct axiom probe reports only
`[propext, Classical.choice, Quot.sound]`.

## Decision

Accept and bank.  Next boundary remains source-measure construction for the
passive sector: chart-produced measure support, concrete passive-coordinate
continuity/product-measure data, image or local coverage, and any
Jacobian/source-prior transport theorem.
