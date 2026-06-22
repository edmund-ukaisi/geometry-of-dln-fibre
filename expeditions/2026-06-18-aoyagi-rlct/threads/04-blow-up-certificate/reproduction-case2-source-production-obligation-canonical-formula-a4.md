# Reproduction - Case 2 source-production obligation canonical formula

Date: 2026-06-22.

Status: supplied-boundary constructor.  This is not chart/source production.

2026-06-22 update: the current Lean API now has the no-extra-boundary
constructor
`SourceProductionObligation.of_formulaSuccessor_transportTerminalRows`.
The supplied-next-chart-family theorem described below has been removed from
the current Lean API.  See
`reproduction-case2-source-production-obligation-remove-vacuous-next-boundary-a4.md`.

## Source Anchor

Aoyagi PDF pp. 21-22, Case 2.  The displayed chart operation gives the
formula-level successor following factor

```text
C'_J^(S+1) = Q^-1 C_J^(S+1).
```

The previously introduced Lean interface `SourceProductionObligation` records
the branchwise data a full successor-production theorem would have to provide.
This slice constructs an inhabitant of that interface only after keeping the
remaining continuing next chart-family boundary explicit.

## Supplied Input

The constructor assumes the existing displayed supplied boundary `data`, a
source following factor `C`, source suffix factors `Ctail`, and the following
supplied continuing branch field:

```text
∀ hnext : J+2 <= prefixMinNat n (S+1),
  ∃ ChartRegularNext TransitionRegularNext,
    Case2ResidualBlockChartFamilyBoundary n S (J+1)
      ChartRegularNext TransitionRegularNext.
```

This is the remaining source-production input for the continuing branch.  The
theorem does not build it from Aoyagi's chart coordinates.

## Canonical Choices

The theorem chooses

```text
Csucc = case2DisplayedSourceSuccessorFollowingFactor n hS hcont residual C
```

and

```text
Cterm = case2DisplayedSourceTerminalTransportedRows n hS hcont residual C.
```

With these choices:

- `Csucc_eq_formula` is reflexive.
- The continuing frontier is the existing frontier package rewritten through
  the successor-following tail projection.
- The actual-width frontier is the existing actual-width stopped boundary with
  the real source suffix product.
- The row-exhausted frontier is the existing source-suffix transported-prefix
  boundary.

For the actual-width terminal-row field, the chosen `Cterm` is transported
rows.  Under

```text
n(S+1) = J+1,
```

the formula-level successor factor collapses to the old source factor `C`.
Since transported rows are already original rows of the formula-level
successor factor, this gives

```text
Cterm = originalRows(C).
```

For the row-exhausted terminal-row field, the chosen `Cterm` is exactly the
transported-row matrix, so the equality is reflexive.

## Historical Lean Target

This slice originally added:

```text
SourceProductionObligation.of_formulaSuccessor_transportTerminalRows_suppliedNextChartFamily
```

That name has since been removed.  The current replacement in the
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation`
namespace is:

```text
SourceProductionObligation.of_formulaSuccessor_transportTerminalRows
```

## Nonclaims

This theorem does not construct the continuing next chart-family boundary,
does not prove chart coverage or transition regularity, does not source-produce
the successor object from coordinates, does not produce the suffix, does not
derive corrected post-data from coordinates, and does not prove Jacobian
arithmetic, normal crossings, pole order, termination, RLCT, or repair of the
printed Case 2 vector mismatch.

It also does not make the stopped branches exclusive.  It chooses a terminal
matrix compatible with both actual-width and row-exhausted branch fields under
their explicit hypotheses.
