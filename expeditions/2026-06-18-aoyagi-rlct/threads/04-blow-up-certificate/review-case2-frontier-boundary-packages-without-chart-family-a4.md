# Review - A4 Case 2 frontier packages without chart family

Review mode: xhigh mathematical boundary scout, xhigh Lean API scout, and
controller integration.

## Verdict

Accepted at the finite API-hardening scope.

## Checks

- The continuing fields are now available without `ChartRegular`,
  `TransitionRegular`, or a caller-supplied
  `Case2ResidualBlockChartFamilyBoundary`.
- The package constructor
  `sourceChartMap_frontierBoundaryPackages_withoutChartFamily` exposes the
  same fielded implication structure as the older package.
- The consumer
  `SourceProductionObligation.of_formulaSuccessor_transportTerminalRows`
  now uses the chart-family-free package constructor.
- The stopped branches remain branch implications.  They do not become chart
  production, terminal source production, or a semantic disjoint case split.

## Fidelity Audit

The mathematical scout rechecked the Case 2 frontier algebra:

- continuing means `J+2 <= prefixMinNat n (S+1)`;
- actual-width stopped means `n(S+1)=J+1`;
- row-exhausted stopped means `prefixMinNat n S=J+1`;
- the stopped alternatives can overlap.

The review specifically flags that row-exhausted terminal rows are transported
prefix rows.  They must not be read as original rows unless actual-width
exhaustion is also supplied.

## Residual Risk

The stopped terminal helper proofs still pass through compatibility APIs whose
old statements mention an abstract chart-family boundary.  The new package
does not expose that boundary to callers, but a deeper cleanup would refactor
the stopped helpers themselves to direct chart-free statements.  This is an
API-hardening slice, not source/chart production.

## Verification

Controller gates passed:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```

The no-sorry audit reported zero `sorry`, `#exit`, `native_decide`, and
`axiom` hits.
