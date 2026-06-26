# Review - A2 retained-passive selected-entry source-readback residual-factor handoff

Reviewer: Newton the 3rd, xhigh

## Verdict

No blockers.

## Checks

The two Lean theorems match the proved content.  The algebraic readout theorem
derives the selected-entry residual square-sum from the supplied
source-readback residual-factor matrix identity.

The proof uses `sourceChart y` only on the fixed-base edge-family side and
`SelectedEntrySignedBox.CenterCoord.chartMap pivot y` only on the selected-
entry right-hand side.  The residual-coordinate reindexing is sound: the
supplied `residualCoordEquiv` is a full equivalence from the endpoint residual
coordinate index to `center`, and `aoyagiCoordinateSquareSum_comp_equiv` is
used in the correct orientation.

The new local-measure theorem does not take the raw `hresidual_eq` hypothesis.
It derives that equality from `residualCoordEquiv` and `hfactor`, then calls
the existing retained-passive selected-entry local-measure theorem.  Source
chart measurability, weighted pushforward, local loss lower bound, and density
bounds remain explicit hypotheses.  No source chart construction, source image
theorem, Jacobian formula, or pushforward proof is hidden.

The reproduction and statement card match the Lean slice and keep the
nonclaims explicit.
