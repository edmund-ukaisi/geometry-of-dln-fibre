# Reproduction - Case 2 continuing successor-following handoff

Date: 2026-06-22.

Status: finite notation handoff for the Case 2 source-production frontier.

## Source anchor

Aoyagi PDF pp. 19-22, Case 2.  After the selected pivot blow-up at
`(J+1,J+1)`, the paper forms

```text
C'_J^(S+1) = Q^-1 C_J^(S+1).
```

The continuing branch then increases `J` to `J+1`.  The residual lower-row
product in the continuing branch uses the following factor restricted to rows
strictly after the new pivot row.

## Finite calculation

Lean already names the formula-level source successor following function as

```text
case2DisplayedSourceSuccessorFollowingFactor n hS hcont residual C.
```

It differs from the old source following function `C` only at row `J+1`; this
row is the transformed top row of `Q^-1 C`.  In the continuing same-stage
residual block for `(S,J+1)`, the following factor is restricted to rows

```text
j >= J+2.
```

Therefore each restricted row `j` satisfies `j != J+1`, and the already-proved
row formula gives

```text
case2DisplayedSourceSuccessorFollowingFactor(...)(j,-) = C(j,-).
```

So the following-factor restriction is unchanged:

```text
case2SourceFollowingFactor (S,J+1) (case2DisplayedSourceSuccessorFollowingFactor ...)
  =
case2SourceFollowingFactor (S,J+1) C.
```

The existing theorem
`case2SourceFollowingFactor_successorFollowingFactor_succ` proves this.

## Lean target

Add a generic handoff theorem converting

```text
ContinuingWeightedSourceFollowingFrontierPayload ... C
```

to

```text
ContinuingWeightedSuccFollowingFrontierPayload ... C.
```

This should be a rewrite-only theorem using the equality above.  It should not
require chart-family data, exponent data, or source-production data beyond the
payload already supplied.

Optionally, add a projection from
`SourceChartFrontierBoundaryPackages.continuingWeighted` to the successor
payload under the same `hnext` hypothesis, so the `SourceProductionObligation`
continuing payload can reuse the existing frontier package.

## Nonclaims

This handoff does not produce `Csucc`, construct a successor chart family,
prove chart coverage, prove source production of `C'^(S+1)`, produce the
suffix, derive corrected post-data from coordinates, prove Jacobian
arithmetic, prove normal crossings, prove pole order, prove termination, or
prove RLCT extraction.

## Kill conditions

- Do not use this handoff to claim the full successor object is produced.
- Do not include the pivot row or old top rows in the rewritten lower-row
  payload.
- Do not drop the standing displayed-pivot hypotheses.
- Do not infer a source suffix or transition theorem from the lower-row
  following-factor restriction.
