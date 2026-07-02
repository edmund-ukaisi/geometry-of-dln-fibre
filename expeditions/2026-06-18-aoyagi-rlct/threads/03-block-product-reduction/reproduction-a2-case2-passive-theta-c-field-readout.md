# Reproduction - A2 Case 2 passive-theta active C-field readout

Date: 2026-07-02.

Status: finite readout theorem for the active retained-passive `C` factors.

## Source Boundary

Aoyagi's Case 2 reduction first clears a pivot and then continues with the
post-pivot residual block and following factor.  In the Lean two-edge
post-pivot model the active retained-passive field is

```text
C : ∀ p : Fin 2, Matrix (κ p.succ) (κ p.castSucc) ℝ.
```

The previous coordinate inventory showed that `Case2PassiveTheta.Center`
matches the scalar coordinate index of the tail factor `C(1)`, while the head
factor `C(0)` is a separate block.  The actual selected-entry construction
does not leave `C(0)` arbitrary: it builds both factors from the successor
selected-entry matrix.

## Readout

For a passive-theta point `theta`, endpoint equivalences `e`, and successor
column equivalence `eNext`, the endpoint-transported retained data satisfies:

```text
C(1), reindexed back by e
  = case2DisplayedPostPivotResidualBlock
      (case2SuccessorSelectedEntrySourceResidual theta.yNext eNext),
```

and

```text
C(0), reindexed back by e
  = case2DisplayedPostPivotFreeFollowingFactor
      (case2SuccessorSelectedEntrySourceCprime theta.yNext eNext).
```

Thus the current passive-theta source lands in the graph of the selected-entry
construction inside the full active `C` coordinate tuple.  It is not an
ambient full-coordinate chart.

## Lean Slice

The formalised readout is in

```text
DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaCFieldReadout
```

and proves:

```text
endpointRetainedData_C_one_submatrix_eq_displayedPostPivotResidualBlock
endpointRetainedData_C_zero_submatrix_eq_displayedPostPivotFreeFollowingFactor
```

Both theorems are in the `Case2PassiveTheta` namespace.  They are wrappers
around the existing selected-entry retained-data C-factor readouts, specialized
to the actual passive-theta retained-data constructor.

## Consequence

The next source-image theorem can now state the image obstruction more
concretely:

- the tail `C(1)` block is selected-entry center data;
- the head `C(0)` block is forced by
  `case2SuccessorSelectedEntrySourceCprime theta.yNext eNext`;
- therefore an ambient formal-product measure theorem needs either an
  enlarged coordinate domain with a free head block, or a section-image
  measure supported on this graph.

## Nonclaims

No source-image coverage, determinant-chart Haar transport, raw-Haar
pushforward, original-prior transport, Jacobian density identity, density
bound, normal-crossing theorem, pole order, or RLCT extraction is proved here.
