# Statement Card - A4 Case 2 Source-Production Obligation Removes Vacuous Next Boundary

## Lean Names

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.of_formulaSuccessor_transportTerminalRows`

## Claim

`SourceProductionObligation` no longer contains the vacuous continuing
next-chart-family existential.  The canonical formula-level constructor now
requires no next-boundary argument.

## Inputs

The new constructor uses the displayed supplied Case 2 boundary, residual
coordinates, source following factor `C`, source suffix factors `Ctail`, and
the suffix layer bound `S+1 <= L`.

## Output

An obligation with canonical choices

```text
Csucc = case2DisplayedSourceSuccessorFollowingFactor ...
Cterm = case2DisplayedSourceTerminalTransportedRows ...
```

and the remaining branchwise finite payloads.  The old supplied/true-predicate
constructor names were removed rather than retained as ignored-argument
wrappers.

## Nonclaims

No affine atlas, chart coverage, meaningful transition regularity, successor
source object, suffix production, coordinate post-data derivation, normal
crossings, pole order, termination, or RLCT is proved.

## Review

Passed after removing the old ignored-argument wrapper names:
`review-case2-source-production-obligation-remove-vacuous-next-boundary-a4.md`.
