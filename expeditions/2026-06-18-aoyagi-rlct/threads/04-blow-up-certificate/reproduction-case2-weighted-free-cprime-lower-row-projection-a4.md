# Pen-and-paper reproduction - A4 Case 2 weighted free Cprime lower-row projection

Status: reproduced as finite displayed-pivot block algebra.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  After the row operation `P`, the displayed
weighted product identity has right side

```text
diag(b') D''' C'.
```

Here `D'''` is displayed as a block diagonal matrix

```text
D''' = [1 0; 0 D_{J+1}].
```

The continuing branch later renames primed data and increases `J` by one.
This reproduction isolates only the lower-row projection of the displayed
weighted right side.

## Reproduction

Work in the displayed pivot-first finite coordinates.  Let

```text
D''' = blockdiag(1, E),
Cprime = [Ctop; Ctail],
W = blockdiag(b0, diagonal b).
```

The unweighted lower-row calculation already reproduced is

```text
(D''' Cprime)_lower = E Ctail.
```

Multiplying by the row-weight diagonal gives

```text
(W D''' Cprime)_lower = diagonal(b) (E Ctail).
```

After reindexing the lower old residual rows by the equivalence with the next
same-stage row domain `(S,J+1)`, this becomes

```text
((W D''' Cprime)_lower,reindexed)
  =
diagonal(successor lower-row weights)
  *
(case2DisplayedPostPivotResidualBlock * reindexed Cprime tail).
```

The successor lower-row weight at a next row `i : Case2ResidualRowIndex n S
(J+1)` is the old lower-row weight function evaluated on the corresponding
old pivot-complement row:

```text
post.weight (case2ResidualRowLevel n S J
  ((case2DisplayedPivotRowComplementEquivResidualRowSucc n hS hcont).symm i).1).
```

This is deliberately not the full successor diagonal including the pivot row
`J+1`; it is only the lower-row diagonal after the pivot row has been deleted.

## Boundary Checks

- The theorem projects the weighted right side of Aoyagi's displayed `Q/P`
  equality.  It does not project the old source-side product unless a
  separate equality is applied.
- The result is row-weighted.  Dropping the diagonal weights would be wrong.
- The theorem is about the lower rows only; it does not identify the pivot row
  or a full successor product.
- No next residual-center nonemptiness is asserted.  That still requires the
  separate branch hypothesis `J+2 <= prefixMinNat n (S+1)`.

## Formalisation Target

Lean should add:

```text
weightedPivotDiagonal_mul_lowerRows
weightedPivotDiagonal_mul_lowerRows_reindex
case2DisplayedWeightedPaperDppp_mul_freeCprime_postPivot_eq_nextSameStageProduct
Case2DisplayedSuppliedChartFamilyBoundary.postPivotWeightedFreeCprimeNextSameStageProduct
```

The first two are generic block-diagonal row-weight lemmas.  The third
specializes them to the displayed Case 2 `D'''` block and the already-proved
free-`Cprime` lower-row product.  The namespace wrapper rewrites the lower-row
diagonal with the supplied successor state's row weights.

## Kill Conditions

- Do not claim full successor chart production or actual `C'^(S+1)`.
- Do not claim chart coverage, arbitrary-pivot coverage, transition
  invariance, Jacobian arithmetic, normal crossings, pole order, or RLCT.
- Do not infer recurrence/exponent post-data from this weighted projection.
- Do not state an unweighted lower-row result for the weighted product.
- Do not include terminal `(S+1,0)` relabeling or stopped branches.
- Do not use the Lehalleur-Rimanyi/quiver paper or quiver Lean as evidence.
