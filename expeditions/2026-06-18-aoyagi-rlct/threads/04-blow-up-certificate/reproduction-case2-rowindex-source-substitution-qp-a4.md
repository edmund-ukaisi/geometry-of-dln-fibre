# Reproduction - A4 Case 2 row-index source-substitution Q/P bridge

Date: 2026-06-24.

Status: checked finite displayed-pivot matrix reproduction.

## Source Anchor

Aoyagi PDF pp. 20-21 performs the displayed Case 2 selected-entry
substitution, forms the transported following factor `C' = Q^{-1} C`, and
uses the `P` row operation whose quotient entries are built from row weights.

This note isolates the finite displayed-pivot algebra when those row weights
are represented by a monomial recurrence indexed by residual source row.

## Reproduction

Let the displayed normalized residual block in pivot-first coordinates be

```text
A = [ 1  y
      x  D ].
```

Let the old residual row weights be

```text
weight_i = monomialRec step rowLevel_i,
```

where `rowLevel_i` is the source residual-row label.  The displayed pivot row
has level `J+1`, and every residual row satisfies

```text
J+1 <= rowLevel_i.
```

Thus the quotient witnesses required for `P` exist by recurrence divisibility:

```text
u * monomialRec step (J+1) divides
u * monomialRec step rowLevel_i.
```

The source-substituted residual block is

```text
diagonal(weight) * case2DisplayedSubstitutionMatrix(u, residual).
```

The selected variable factors into row weights after pivot-first reindexing:

```text
(diagonal weight * substitution).pivotFirst
  =
weightedPivotDiagonal
  (u * monomialRec step (J+1))
  (i |-> u * monomialRec step rowLevel_i)
* pivotFirstMatrix(A).
```

Substituting this identity into the already-proved row-index `Q/P` theorem
gives the source-substitution form:

```text
(P * (diagonal weight * substitution).pivotFirst) * C
  =
(weightedPivotDiagonal * cleared(A)) * (Q^{-1} C).
```

The vertical-block lift reattaches unchanged top rows by `fromBlocks`, so the
same residual-tail identity holds under an arbitrary unchanged top block.

## Lean Targets

Lean proves:

```text
exists_case2DisplayedQP_mul_sourceSubstitution_of_rowIndex_monomialRec
exists_case2DisplayedQP_verticalBlock_sourceSubstitution_of_rowIndex_monomialRec
```

in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

## Boundary

- This is displayed top-left pivot finite matrix algebra only.
- The recurrence weights are assumed in row-index monomial form.
- The theorem supplies quotient witnesses for the `P` operation by row-level
  divisibility.
- It does not prove the recurrence state produces these weights, and it does
  not generalize to arbitrary pivots.
- It does not prove source production of `C'^(S+1)`, terminal products,
  transition invariance, chart coverage, Jacobian arithmetic, normal
  crossings, pole order, or RLCT.

## Kill Conditions

- Do not use this theorem for a non-displayed selected row: the divisibility
  argument uses `J+1 <= rowLevel_i` relative to the displayed pivot level.
- Do not rename it as a flat-row or gap theorem; no flatness is needed or
  proved here.
- Do not use it to infer row-exhaustion or actual-width exhaustion.
