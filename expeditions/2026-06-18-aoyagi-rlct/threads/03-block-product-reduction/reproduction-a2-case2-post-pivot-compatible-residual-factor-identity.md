# Reproduction - A2 Case 2 post-pivot compatible residual-factor identity

Date: 2026-06-26.

Status: killed as an Aoyagi-supplied source claim. The displayed Case 2
post-pivot product is source-backed, but the stronger selected-entry readout
identity is not.

## Target Under Audit

The proposed source-moving target was the identity

```text
residualFactorProduct Cfac last 0
  = matrix (c -> SelectedEntrySignedBox.CenterCoord.chartMap pivot y
      (residualCoordEquiv c))
```

for Aoyagi's Case 2 post-pivot two-edge product. In the concrete displayed
chain this would say that the post-pivot lower product

```text
D_(J+1) * C'_+
```

is itself the matrix of successor selected-entry center coordinates after the
pivot.

## Source Boundary

Aoyagi PDF pp. 19-21, Case 2, support the following finite operations:

- select the top-left residual-block entry `d_(J+1,J+1) = u_(S,J+1)`;
- write the remaining entries of the current residual block in the selected
  chart;
- define the regular column operation `Q`;
- transform the following factor by `C'_J^(S+1) = Q^-1 C_J^(S+1)`;
- define the regular row operation `P`;
- obtain the cleared block `D'''_J = blockdiag(1, D_(J+1))`;
- state that, when the branch continues, this gives the inductive statement
  with `J` increased by one.

The source does not display an equation identifying
`D_(J+1) * C'_+` with the successor selected-entry chart-map matrix. The next
selected-entry chart, if applied, is on the next residual block `D_(J+1)`;
the lower product still includes the following factor `C'_+`.

## Entrywise Calculation

Write the normalized current pivot block as

```text
A = [1  y]
    [x  Z],
```

where

```text
x_i   = d'_(i,J+1),
y_k   = d'_(J+1,k),
Z_ik  = d'_(i,k)
```

for post-pivot row and column indices `i,k > J+1`.

Aoyagi's column operation has the form

```text
Q      = [1 -y],       Q^-1 = [1 y],
         [0  I]                [0 I]
```

so

```text
A Q = [1      0]
      [x  Z - x y].
```

For the following factor,

```text
C' = Q^-1 C,
```

so entrywise

```text
C'_(J+1,a) = C_(J+1,a) + sum_k y_k C_(k,a),
C'_(k,a)   = C_(k,a)                         for k > J+1.
```

The row operation `P` clears the lower first column after the diagonal weights,
leaving

```text
D''' = [1      0]
       [0  Z - x y].
```

Therefore the lower post-pivot product entries are

```text
(D''' C')_(i,a)
  = sum_k (Z_ik - x_i y_k) C_(k,a)
```

for post-pivot rows `i > J+1`.

This is the source-backed product `D_(J+1) * C'_+`. To identify it with a
successor selected-entry center matrix one would need extra data:

```text
sum_k (Z_ik - x_i y_k) C_(k,a)
  = CenterCoord.chartMap pivotNext yNext (i,a)
```

after a column endpoint equivalence. The selected-entry chart-map RHS has the
shape "pivot coordinate" at the pivot and "pivot coordinate times residual
coordinate" off the pivot. Aoyagi does not derive that shape for the product
entries above.

## Proved / Assumed / Cited / Deferred

**Proved.** The finite `Q/P` block algebra, the `C' = Q^-1 C` lower-tail
identity, and the concrete two-edge product
`D_(J+1) * C'_+`. Lean already records this through
`residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_freeTwoEdgeFactorProduct`
and
`residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_paperCprime_eq_sourceResidualBlock_successorFollowingFactor`.

**Assumed.** Any identity making the post-pivot product entries equal successor
selected-entry chart-map coordinates; any `yNext`; any column endpoint
equivalence from the free target type to `Case2ResidualColIndex n S (J+1)`;
and any local source/image equality producing those coordinates.

**Cited.** Aoyagi pp. 19-21 only for the displayed Case 2 finite algebra and
the induction-step wording.

**Deferred.** Source production of successor chart coordinates, selected-entry
product readout, fixed-base endpoint equivalences in a global p.13 source, and
source-measure/normal-crossing/RLCT consequences.

## Decision

Do not promote the unqualified identity to Lean as an Aoyagi theorem. The
already-landed conditional Lean bridges are the right boundary:

```text
residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_entrywise
```

and the corresponding paper-`C'` source-product identity. A future theorem may
consume a supplied entrywise successor readout, but proving that readout is a
separate source-production problem.

