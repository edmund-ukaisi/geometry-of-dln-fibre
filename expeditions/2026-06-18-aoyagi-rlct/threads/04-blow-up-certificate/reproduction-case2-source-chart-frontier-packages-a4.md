# Pen-and-paper reproduction - A4 Case 2 source-chart frontier packages

Status: reproduced and formalised a fielded implication package for the
displayed Case 2 source-chart frontier.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  After the displayed pivot `(J+1,J+1)`, the
proof has three finite-frontier situations:

- continuation at the same stage, with the lower-right block reindexed to
  `(S,J+1)`;
- actual next-width exhaustion `n(S+1)=J+1`, where the transported top row has
  no correction sum and actual-width relabeling to `(S+1,0)` is available;
- current-prefix row exhaustion `prefixMinNat n S=J+1`, where the terminal
  prefix rows are transported rows, not necessarily original rows.

The stopped alternatives may overlap.  This checkpoint packages consequences
as implications from explicit branch hypotheses; it does not choose a unique
branch.

## Reproduction

The previous frontier branch checkpoint proves the finite arithmetic:

```text
J+2 <= prefixMinNat n (S+1)
or n(S+1)=J+1
or prefixMinNat n S=J+1.
```

For downstream proof assembly, using a selected disjunction witness is too
coarse: if both stopped equalities hold, choosing the row-exhausted constructor
would hide the stronger actual-width conclusion.  The correct package is
therefore a set of implications.

Under the common displayed source-chart hypotheses, Lean already has three
branch-specific packages:

1. If

   ```text
   J+2 <= prefixMinNat n (S+1),
   ```

   then the next residual center is nonempty and the lower rows of
   `D''' * C'` reindex to the next same-stage source-following product at
   `(S,J+1)`, with corrected supplied exponent/level/gap post-data.

2. If

   ```text
   n(S+1)=J+1,
   ```

   then the actual-width stopped branch has original source rows, relabelled
   `(S+1,0)` level/exponent certificates, and finite residual-center
   principalization.  The following factor is still an arbitrary supplied
   matrix.

3. If

   ```text
   prefixMinNat n S=J+1,
   ```

   and additionally `S+1=L`, then the row-exhausted stopped branch has a
   terminal-last transported-prefix-row boundary and finite residual-center
   principalization.  No original-row equality or `(S+1,0)` relabeling is
   attached to this row-exhausted conclusion.

The Lean package names these three propositions and bundles the implication
fields:

```text
ContinuingSourceChartFrontierPayload
ContinuingWeightedSourceFollowingFrontierPayload
ActualWidthSourceChartFrontierPayload
RowExhaustedTerminalLastSourceChartFrontierPayload
SourceChartFrontierBoundaryPackages
sourceChartMap_frontierBoundaryPackages
```

## Proved

- The field `frontierBranch` records the finite branch witness from displayed
  pivot validity.
- The field `continuing` exposes the existing next same-stage source-following
  product package under the explicit next-continuation hypothesis.
- The field `continuingWeighted` exposes the paper-`C'` weighted lower-row
  source-following payload, next residual-center nonemptiness, and finite
  center principalization under the same explicit next-continuation
  hypothesis.
- The field `actualWidthStopped` exposes the existing actual-width original-row
  supplied-following package under the explicit actual-width hypothesis.
- The field `rowExhaustedStopped` exposes the existing terminal-last
  transported-prefix package under explicit row-exhaustion and terminal-last
  hypotheses.
- The later field `rowExhaustedSourceSuffix` exposes the source-suffix
  transported-prefix package under explicit row-exhaustion, keeping
  `sourceSuffixProduct` and not requiring terminal-last.

## Assumed

- The common supplied displayed source-chart boundary data: pre exponent
  certificates, level invariants, least-value gap, and residual-block
  chart-family boundary.
- Branch hypotheses are supplied independently to each implication.
- The row-exhausted terminal-last field still requires the terminal-last
  hypothesis `S+1=L`.  The source-suffix field instead requires finite and
  decidable suffix index data and keeps the suffix product explicit.

## Not Claimed

- No disjointness or exclusivity of the stopped alternatives.
- No chart coverage or affine-atlas construction.
- No source-produced recurrence/exponent post-data or source-produced
  `C'^(S+1)`.
- No successor chart-family construction.
- No transition invariant or termination theorem.
- No terminal source truth.
- No `(S+1,0)` relabeling or original-row claim in the row-exhausted wide-next
  branch.
- No Jacobian, normal-crossing, pole-order, or RLCT statement.
- No repair of Aoyagi's printed Case 2 vector mismatch.
