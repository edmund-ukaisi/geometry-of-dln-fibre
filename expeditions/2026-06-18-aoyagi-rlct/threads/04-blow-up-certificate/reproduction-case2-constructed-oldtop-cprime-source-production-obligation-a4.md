# Reproduction - Case 2 constructed old-top `Cprime` source-production obligation

Date: 2026-06-24.

Status: controller reproduction before Lean formalisation.

## Source Anchor

Aoyagi PDF pp. 21-22 gives the Case 2 coordinate change around the selected
pivot and writes the transported following block as `C'_J^(S+1) = Q^-1
C_J^(S+1)`.  In the continuing branch this is the formula-level replacement
used for the next selected row.  In the stopped branches the terminal row data
keeps old rows and the surviving transported pivot row.

This slice is not a new geometric chart-production theorem.  It packages an
already-constructed finite following factor into the existing
`SourceProductionObligation` interface.

## Data

Assume the displayed Case 2 supplied chart-family boundary

```text
data :
  Case2DisplayedSuppliedChartFamilyBoundary R L n S J
    t t' numerator numerator' leastValue leastValue'
    pre post u ChartRegular TransitionRegular.
```

It supplies

```text
data.stage_pos    : 1 <= S,
data.continuation : J+1 <= prefixMinNat n (S+1).
```

Fix a source suffix setup

```text
kappa : Fin (L+1) -> Type,
[forall i, Fintype (kappa i)],
[forall i, DecidableEq (kappa i)],
hSuffix : S+1 <= L,
Ctail : forall p : Fin L, Matrix (kappa p.castSucc) (kappa p.succ) R.
```

Let

```text
tau =
  kappa (sourceLayerIndex L (S+2)
    (Nat.succ_le_succ (Nat.zero_le (S+1)))
    (Nat.succ_le_succ hSuffix)).
```

Fix arbitrary old-top rows and arbitrary free transported chart-coordinate
following data

```text
Cold :
  Matrix (case2SourceOldTopRowIndex J) tau R,

Cprime :
  Matrix
    (Unit + pivotComplement
      (case2DisplayedPivotCol n data.stage_pos data.continuation))
    tau R.
```

Define the source-side following factor

```text
C =
  case2DisplayedConstructedSourceFollowingFactorWithOldTopFromCprime
    n data.stage_pos data.continuation residual Cold Cprime.
```

By construction,

```text
case2DisplayedSourceOldTopBlock C = Cold
```

and the displayed source following block is the reconstructed old residual
block

```text
case2DisplayedSourceFollowingFactor n data.stage_pos data.continuation C
  =
case2DisplayedPaperConstructedFollowingFactor
  n data.stage_pos data.continuation residual Cprime.
```

Aoyagi's displayed inverse operation also recovers the free transported
coordinate:

```text
case2DisplayedPaperCprime n data.stage_pos data.continuation residual C
  =
Cprime.
```

## Terminal Matrix

The canonical formula-level `SourceProductionObligation` constructor chooses
terminal rows to be the transported source-terminal matrix

```text
case2DisplayedSourceTerminalTransportedRows
  n data.stage_pos data.continuation residual C.
```

For the constructed old-top/free-`Cprime` factor, previous row bookkeeping
proves that reindexing this transported terminal matrix by old rows plus the
pivot row gives

```text
verticalBlock Cold
  (case2DisplayedFreeCprimeTop n data.stage_pos data.continuation Cprime).
```

Equivalently, as a matrix indexed by the source terminal rows, the transported
terminal matrix is

```text
(verticalBlock Cold
  (case2DisplayedFreeCprimeTop n data.stage_pos data.continuation Cprime))
  .submatrix (case2SourceTerminalRowEquiv J).symm id.
```

This is the same terminal matrix stored by

```text
SuppliedTerminalCprimeBridge.of_constructedWithOldTopFromCprime
  n data.stage_pos data.continuation residual Cold Cprime.
```

The last row is `top(Cprime)`, not the original source row unless a separate
actual-width hypothesis is present.

## Obligation Package

The existing canonical constructor

```text
SourceProductionObligation.of_formulaSuccessor_transportTerminalRows
```

chooses

```text
Csucc =
  case2DisplayedSourceSuccessorFollowingFactor
    n data.stage_pos data.continuation residual C
```

and

```text
Cterm =
  case2DisplayedSourceTerminalTransportedRows
    n data.stage_pos data.continuation residual C.
```

It fills the obligation fields as follows:

- `Csucc_eq_formula` is reflexive.
- The continuing frontier is the existing formula-level continuing payload.
- The actual-width branch uses the existing actual-width source-suffix payload
  and the actual-width collapse of transported terminal rows to original rows.
- The row-exhausted branch uses the existing row-exhausted transported-prefix
  source-suffix payload and keeps the transported terminal rows.

Transporting this constructor along the terminal-row equality above gives the
constructed old-top/free-`Cprime` specialization:

```text
SourceProductionObligation data residual kappa hSuffix C Ctail
  (case2DisplayedSourceSuccessorFollowingFactor
    n data.stage_pos data.continuation residual C)
  ((verticalBlock Cold
    (case2DisplayedFreeCprimeTop n data.stage_pos data.continuation Cprime))
    .submatrix (case2SourceTerminalRowEquiv J).symm id).
```

The intended Lean additions are:

```text
case2DisplayedSourceTerminalTransportedRows_constructedWithOldTopFromCprime_eq_terminalStack
```

where the right-hand side is the source-row reindexing

```text
(verticalBlock Cold
  (case2DisplayedFreeCprimeTop n hS hcont Cprime))
  .submatrix (case2SourceTerminalRowEquiv J).symm id,
```

not the raw stacked matrix.  The second addition is:

```text
Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.
  of_constructedWithOldTopFromCprime_terminalStack
```

The first theorem is finite row-equivalence bookkeeping.  The second is an
interface specialization.

## Boundary Cases

- This result does not assume stopped next-continuation, actual-width
  exhaustion, or row-exhaustion.
- In row-exhausted but wide-next situations, the terminal pivot row remains the
  transported top row `top(Cprime)`.
- The supplied suffix remains the raw `sourceSuffixProduct kappa Ctail S
  hSuffix` inside the obligation fields.
- The successor following factor is the formula-level
  `case2DisplayedSourceSuccessorFollowingFactor ... C`; this theorem does not
  source-produce it.

## Kill Conditions

- Replacing `top(Cprime)` by the full `Cprime` block in the terminal matrix is
  wrong.
- Replacing `top(Cprime)` by original source rows is wrong without the separate
  actual-width hypothesis.
- Naming the result as chart production, suffix production, or RLCT progress
  would overstate it.

## Nonclaims

This is finite packaging only.  It does not construct `Csucc`, source-produce
`C'^(S+1)`, construct suffixes, construct successor charts, prove chart
coverage, prove transition regularity, prove analytic Jacobian data, prove
normal crossings, prove pole order, prove termination, or compute RLCT.
