# Reproduction - A2 retained-passive endpoint transport

Date: 2026-06-28.

Status: reproduced; Lean targets selected and proved.

## Target

The previous Case 2 selected-entry retained-passive datum lives over the
explicit endpoint family

```text
case2PostPivotTwoEdgeDomain n S J τ : Fin 3 -> Type.
```

Fixed-base p.13 consumers use a different endpoint family.  This rung proves
the finite algebra needed to move the stored `C` residual-factor product along
endpoint equivalences.

## Product calculation

Let

```text
C p : Matrix (κ p.succ) (κ p.castSucc) K
e j : κ j ≃ κ' j.
```

Define the transported factors

```text
C' p = (C p).submatrix (e p.succ).symm (e p.castSucc).symm.
```

The endpoint product is defined by decreasing induction.  At the base endpoint
`i = j`, both products are identity matrices, and

```text
(1 : Matrix (κ j) (κ j) K).submatrix (e j).symm (e j).symm = 1.
```

For the induction step from `p.succ` to `p.castSucc`, assume

```text
residualFactorProduct C' j p.succ
  = (residualFactorProduct C j p.succ).submatrix (e j).symm (e p.succ).symm.
```

Then

```text
residualFactorProduct C' j p.castSucc
  = residualFactorProduct C' j p.succ * C' p
  = (residualFactorProduct C j p.succ).submatrix (e j).symm (e p.succ).symm
      * (C p).submatrix (e p.succ).symm (e p.castSucc).symm
  = (residualFactorProduct C j p.succ * C p).submatrix
      (e j).symm (e p.castSucc).symm
  = (residualFactorProduct C j p.castSucc).submatrix
      (e j).symm (e p.castSucc).symm.
```

The third equality is `Matrix.submatrix_mul_equiv`; the first and last are the
recursive product step.

Lean endpoint:

```text
ChartLocalSuffixState.residualFactorProduct_endpointTransport
```

## Retained-passive data calculation

For retained-passive nonredundant coordinate data, endpoint transport keeps the
square retained fields unchanged and reindexes the endpoint-dependent fields:

```text
F2 p          -> submatrix id (e p.castSucc).symm
A3passive p  -> submatrix (e p.castSucc.succ).symm id
C p          -> submatrix (e p.succ).symm (e p.castSucc).symm
F3            -> submatrix (e last).symm id.
```

Since `detChart` reads only `Ctop` and the passive `A1passive` blocks, endpoint
transport preserves determinant-chart membership.  The stored `C` product
transport is the product calculation applied to `data.C`.

Lean endpoints:

```text
RetainedPassiveNonredundantCoordinateData.endpointTransport
RetainedPassiveNonredundantCoordinateData.endpointTransport_detChart
RetainedPassiveNonredundantCoordinateData.residualFactorProduct_C_endpointTransport
```

## Case 2 specialization

For the explicit selected-entry Case 2 datum, endpoint transport preserves the
determinant-chart proof.  Its transported stored `C` residual-factor product is
the same selected-entry center-coordinate matrix, with residual coordinates
read through the transported endpoint equivalence:

```text
case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
  n S (J+1) (e last).symm ((e 0).symm.trans eNext).
```

Lean endpoints:

```text
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
```

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** Endpoint transport of explicit residual-factor
products; endpoint transport of retained-passive nonredundant coordinate data;
determinant-chart preservation for that transport; and the transported stored
`C` selected-entry matrix readout for the explicit Case 2 datum.

**Assumed.** Endpoint equivalences `e j : κ j ≃ κ' j`, and the same finite Case
2 branch data as the prior selected-entry datum theorem.

**Cited.** None.

**Deferred.** Transport of `edgeMatrix`, `sourceRecursiveDetChart`,
`sourceReadback`, and full suffix-recursion states; fixed-base source-chart
realization; local-source membership; source-prior pushforward; Jacobian density
comparison; normal crossings; pole order; and RLCT.
