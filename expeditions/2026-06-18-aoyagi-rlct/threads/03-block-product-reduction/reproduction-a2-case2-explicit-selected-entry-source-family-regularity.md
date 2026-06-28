# Reproduction - A2 Case 2 explicit selected-entry source-family regularity

Date: 2026-06-28.

Status: reproduced; Lean target selected.

## Target

The previous explicit source-family rung constructs, for every successor
selected-entry coordinate vector `yNext`, a retained-passive source edge family

```text
E(yNext) = case2PostPivotSelectedEntrySourceEdgeFamily ... yNext eNext.
```

The target of this rung is only finite-coordinate regularity:

```text
yNext |-> E(yNext) is continuous,
yNext |-> E(yNext) is measurable.
```

This is not a source-prior pushforward, not a Jacobian statement, not coverage
of arbitrary retained-passive points, and not a normal-crossing or RLCT claim.

## Successor Matrix

The successor selected-entry matrix is

```text
T(yNext) =
  case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext.
```

Entrywise, `T(yNext) i j` is a selected-entry center-coordinate chart map
evaluated at the residual coordinate corresponding to `(i,j)` under the
residual-coordinate equivalence.  The selected-entry chart map is continuous,
and evaluation at a fixed finite coordinate is continuous.  Therefore every
entry of `T` is continuous, hence `T` is a continuous finite matrix-valued
function.

Lean endpoint:

```text
continuous_case2SuccessorSelectedEntryMatrix
```

## Retained-Passive Datum

The retained-passive datum is

```text
data(yNext) =
  case2PostPivotSelectedEntryRetainedPassiveData ... yNext eNext.
```

Its product-topology tuple is

```text
(A1passive, F2, A3passive, C, Ctop, F3)
= (1, 0, 0, C(yNext), 1, 0).
```

Only the `C` field varies with `yNext`.  The two `C` edges are:

```text
C 0 = case2DisplayedPostPivotFreeFollowingFactor
        (case2SuccessorSelectedEntrySourceCprime ... yNext eNext),
C 1 = case2DisplayedPostPivotResidualBlock
        (case2SuccessorSelectedEntrySourceResidual ... yNext eNext).
```

The first edge is constant because the chosen `Cprime` tail is the reindexed
identity and does not read the matrix argument.  The second edge is the
right-reindexed successor selected-entry matrix: the residual data is the
zero-extension of `T(yNext).submatrix id eNext.symm`, and restricting the
zero-extension to the displayed post-pivot residual block recovers that
matrix.  Since `T` is continuous, this submatrix is continuous.

Thus the `C` field is continuous as a finite product over the two edges.  The
other tuple fields are constant, so the entire product tuple is continuous.
The retained-passive coordinate type carries the induced product topology via
`ofTopologyTuple`, hence `data` is continuous.

Lean endpoints:

```text
continuous_case2PostPivotSelectedEntryRetainedPassiveData
continuous_case2PostPivotSelectedEntryRetainedPassiveData_detChart_subtype
```

## Source Edge Family

The explicit source edge family is the retained-passive `edgeMatrix` of
`data(yNext)`.  The datum lies in the determinant-chart subtype for every
`yNext`, and the retained-passive topology layer already proves that
`edgeMatrix` is continuous on that subtype.  Composing these maps gives
continuity of the explicit source family.

Measurability follows directly from continuity.

Lean endpoints:

```text
continuous_case2PostPivotSelectedEntrySourceEdgeFamily
measurable_case2PostPivotSelectedEntrySourceEdgeFamily
```

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** Continuity of the successor selected-entry
matrix, continuity of the explicit retained-passive datum and determinant-chart
subtype map, and continuity/measurability of the explicit Case 2
selected-entry-to-source edge family.

**Assumed.** Branch hypotheses `hS`, `hcont`, `hnext`, the endpoint equivalence
`eNext`, and the finite typeclass data needed by the source edge family.

**Cited.** None.  The proof uses finite product topology, matrix submatrix
continuity, the selected-entry chart-map continuity already formalised in the
expedition, and the retained-passive `edgeMatrix` continuity theorem.

**Deferred.** Source-prior pushforward, Jacobian density comparison, arbitrary
retained-passive coverage, source-rank coverage, normal crossings, pole order,
and RLCT.

