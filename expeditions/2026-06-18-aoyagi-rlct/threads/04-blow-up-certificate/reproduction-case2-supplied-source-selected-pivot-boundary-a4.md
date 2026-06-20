# A4 Case 2 Supplied Source-Selected Pivot Boundary

Status: reproduced a supplied boundary package for a Case 2 source-selected
pivot.

## Source Situation

Aoyagi's Case 2 blow-up center is the residual block with rows

```text
J+1 <= i <= M(S)
```

and columns

```text
J+1 <= j <= M^(S+1).
```

The paper displays the top-left chart `d_(J+1,J+1)=u_(S,J+1)` and then works
through the local `Q/P` calculation in that displayed source order. The finite
selected-entry algebra already formalized in Lean applies to any supplied
center entry after reindexing the chosen row and column first, but Aoyagi does
not write a source-ordered non-top-left transition formula.

Therefore the source-faithful target is not coverage and not a non-displayed
source-order theorem. The correct checkpoint is a supplied boundary: assume a
source pair

```text
p in case2ResidualBlockPivotEntries n S J
```

and package the finite facts already proved for that supplied pair.

## Boundary / Reproduction

The boundary carries the continuation data

```text
1 <= S,  S <= L,  J+1 <= prefixMinNat n (S+1),
```

so the corrected Case 2 new-label certificate follows from the existing prefix
bound theorem. It also carries the pre-state exponent certificates, the bridge
`leastValue = level` on introduced labels, and the integer Case 2 least-value
gap. These reproduce the recurrence-level gap needed by the source-selected
matrix identity:

```text
pre.case2Gap.
```

The supplied recurrence post-data says old introduced recurrence data are
preserved and the new label `(S,J+1)` is assigned level `J` and variable `u`.
The supplied corrected exponent post-data says old exponent/least-value data
are preserved and the corrected new label gets the prefix-minimum Case 2
vector, numerator, and least value `J`.

From these fields the boundary projects:

- the corrected new-label certificate;
- the pre-state Case 2 recurrence gap;
- the successor exponent-domain certificate;
- the successor level/least-value invariant;
- the successor least-value gap and recurrence-level gap;
- supplied chart regularity for the selected pivot;
- supplied transition regularity from the selected pivot to any supplied
  residual-block pivot;
- finite selected-entry principalization of the residual-block center to
  `(u)`;
- the source-selected arbitrary-pivot `Q/P` identity, with successor weights
  supplied by the recurrence post-data.

The `Q/P` identity uses the existing source-coordinate wrappers: a source
residual function is restricted to the residual-block row/column subtypes, and
a source following factor is reindexed into the selected pivot-first column
order.

## Scope / Caveats

- The pivot pair is supplied; membership in the finite center is not coverage.
- Residual rows use the prefix-minimum bound `J+1..M(S)`, while residual
  columns use the actual width `J+1..M^(S+1)`.
- Aoyagi displays only the top-left Case 2 pivot in source order.
- Non-top-left pivot algebra is finite selected-entry algebra after reindexing,
  not a source-displayed non-top-left chart calculation.
- `ChartRegular` and `TransitionRegular` remain supplied predicates.
- Recurrence post-data and corrected exponent post-data remain supplied.
- The selected variable is counted once through successor weights
  `u * pre.weight`.
- The printed Case 2 vector mismatch remains unresolved by this boundary.
- This proves no affine blow-up atlas, chart coverage, chart-produced
  post-data, Jacobian, normal crossing, RLCT extraction, termination, or full
  transition invariant.
