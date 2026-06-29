# Reproduction - Case 2 finite raw-pivot continuing successor boundary

Date: 2026-06-29.

## Source calculation

Aoyagi's Case 2 continuation step, pp. 19-22, uses the selected-entry blow-up
at the residual-block pivot and then says to continue the procedure when the
next residual-block coordinate is still available.  In the expedition's
prefix-minimum notation, the continuing branch is

```text
J + 2 <= prefixMinNat n (S + 1).
```

At the successor state `(S,J+1)`, the next finite residual-block center is the
same selected-entry kind of finite center, now indexed with `J+1`.  The
source-backed finite formula is still the elementary selected-entry chart

```text
x_p = u,
x_q = u * y_q  for q != p.
```

The finite affine overlaps are still

```text
u_target = u_source * normalized_source(target_pivot),
y_target(q) = normalized_source(q) / normalized_source(target_pivot).
```

The stronger successor boundary is therefore not new analytic data.  It is
the already-proved finite raw-pivot chart-family theorem applied to the
successor state.

## Lean implementation

File:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean
```

New theorem:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
  .finiteRawPivotContinuingSuccessorBoundary
```

The theorem proves

```text
Case2ResidualBlockChartFamilyBoundary n S (J + 1)
  (Case2FiniteRawPivotChartRegular n S (J + 1))
  (Case2FiniteRawPivotTransitionRegular (K := K) n hS hnext)
```

from

```text
hS    : 1 <= S
hnext : J + 2 <= prefixMinNat n (S + 1).
```

The proof applies `finiteRawPivotChartFamilyBoundary` at `J := J + 1`; the
successor continuation inequality is exactly the continuation bound required
for that state.

## Status labels

Proved:

- finite chart regularity at the successor residual-block center, where
  regularity means raw-pivot selected-entry formula plus finite center-ideal
  principalization;
- finite transition regularity at the successor residual-block center, where
  regularity means the finite selected-entry affine overlap pair.

Cited:

- Aoyagi's displayed Case 2 selected-entry finite calculation, only as the
  source anchor for the selected-entry formula and continuing branch.

Deferred:

- analytic domains and coverage;
- analytic transition regularity;
- source-produced successor matrices and suffixes;
- analytic Jacobian or volume-form compatibility;
- branch termination;
- global normal crossings, pole order, and RLCT extraction.

## Kill conditions

Reject any use of this theorem as an analytic next-chart constructor.  It does
not provide open domains, source-neighborhood coverage, overlap regular maps,
source-produced `Csucc` or suffix factors, branch termination, or analytic
measure compatibility.  It only replaces the old successor `True`-predicate
boundary by the nontrivial finite selected-entry predicates already proved for
the current state.
