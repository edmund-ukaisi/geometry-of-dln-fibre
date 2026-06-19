# A4 Case 2 Arbitrary Selected-Entry Recurrence Handoff

Status: reproduced conditional recurrence-state handoff for arbitrary selected
Case 2 residual pivots.

## Source Data

The previous arbitrary selected-entry checkpoint proved finite algebra for any
selected residual-block pivot. This note adds the recurrence-state hypotheses
already used in the displayed top-left chart:

- an old introduced-label recurrence state `pre`;
- the old Case 2 gap, which makes old residual row weights flat;
- optionally a supplied successor recurrence state `post` satisfying the Case
  2 post-data package.

The row domain is still `J+1..mu_S`, and the column domain is still
`J+1..n_(S+1)`.

## Reproduction

Let `rowPivot : I` and `colPivot : K` be any supplied residual-block pivot. If
`pre.case2Gap` holds, then all old residual row weights are equal:

```text
pre.weight(rowLevel i) = pre.weight(J+1)
```

for every row `i : I`. Hence they are equal to the selected pivot-row weight:

```text
pre.case2ResidualRowWeight i = pre.case2ResidualRowWeight rowPivot.
```

Therefore the arbitrary selected finite-algebra wrapper applies with

```text
weight_i = pre.case2ResidualRowWeight i.
```

If a supplied successor recurrence state `post` preserves old labels and adds
`(S,J+1)` at level `J` with variable `u`, then the already-proved recurrence
update gives, for every residual row level,

```text
post.weight(rowLevel i) = u * pre.weight(rowLevel i).
```

Thus the right-side pivot-first diagonal

```text
diag(u * pre.case2ResidualRowWeight rowPivot,
     u * pre.case2ResidualRowWeight i)
```

can be rewritten as

```text
diag(post.weight(rowLevel rowPivot),
     post.weight(rowLevel i)).
```

This is the arbitrary selected-pivot analogue of the displayed successor-weight
handoff. It is still conditional on supplied recurrence data and a supplied
pivot.

## Scope

This checkpoint proves:

- arbitrary selected-pivot `Q/P` from a packaged old recurrence state and old
  Case 2 gap;
- arbitrary selected-pivot source-substitution transport rewritten through
  supplied successor recurrence weights;
- supplied-post-data wrappers for the same rewrite.

It does not prove:

- that a blow-up chart produces `post`;
- arbitrary-pivot chart coverage;
- affine blow-up atlas construction;
- chart regularity or Jacobian facts;
- exponent updates or transition invariants;
- source comparability;
- normal crossings or RLCT extraction.
