# Review - A2 Case 2 coordinate residual readout

Date: 2026-06-29.

Reviewer: xhigh `Descartes the 2nd`.

Status: PASS.

## Findings

No findings.

## Checks

The reviewer checked:

```text
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_sourceReadback_residualFactorProduct_eq_matrix
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData
```

The generic theorem was confirmed to use only:

- the fixed-base residual readout as `value` of the source-readback
  residual-factor product;
- the supplied source-readback residual-factor matrix identity;
- `AoyagiResidualBlockCoordinateIndex.value_matrix`.

The Case 2 theorem was confirmed to keep the endpoint data explicit:

- `eNext`;
- `e`;
- `hcont`;
- `hnext`;
- `U₀`;
- `hU₀`.

No source-image, measure, Jacobian, normal-crossing, pole-order, or RLCT
assumption is hidden in either theorem.

## Verification

The reviewer ran:

```text
cd /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
git diff --check
```

The build passed with only replayed existing linter warnings from
`ProductReductionStepRegularDensity.lean`, and `git diff --check` passed.

Direct axiom checks for both new theorem names reported only:

```text
[propext, Classical.choice, Quot.sound]
```
