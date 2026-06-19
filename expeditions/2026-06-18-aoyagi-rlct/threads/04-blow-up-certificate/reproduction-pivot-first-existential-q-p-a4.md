# A4 Pivot-First Existential `Q/P` Wrappers

Status: checked finite algebra reproduction. This is not a chart construction
or a source reproduction of non-displayed arbitrary pivot charts.

## Scope

The previous two checkpoints proved:

- a pivot-first algebra bridge for a matrix pivot already normalised to `1`;
- generic quotient witnesses for row weights satisfying divisibility,
  equality, recurrence-tail, equality-or-later, or common-pivot-multiple
  hypotheses.

This note reproduces the small bridge between them. The output is existential:
instead of requiring a previously named `q`, it assumes row-weight divisibility
or recurrence data and chooses the `q` needed by the normalised `P` row
operation.

It does not construct selected-entry charts, prove pivot normalisation, prove
coordinate or weight transport, prove chart coverage, update exponent vectors,
or prove a Case 1/Case 2 transition invariant.

## Algebra Reproduction

Let `A` be a finite matrix over a commutative ring, and choose a row pivot
`r0` and column pivot `c0`. Assume the selected entry has already been
normalised:

```text
A r0 c0 = 1.
```

Putting the pivot first gives the block

```text
[ 1  y
  x  D ].
```

The already-proved pivot-first theorem says that, for row weights `b0` and
`b_i`, if witnesses `q_i` satisfy

```text
b_i = q_i * b0,
```

then the local `Q`-then-`P` identity clears the pivot column below the pivot.
With a following factor `C`, the product-preservation form is:

```text
(P(q,x) * diag(b0,b) * A_pivot_first) * C
  =
(diag(b0,b) * [1 0; 0 D - x*y]) * (Q(y)^(-1) * C).
```

If instead we only know divisibility

```text
b0 divides b_i     for every lower row i,
```

then choosing one quotient for each row gives `q_i` with `b_i=q_i*b0`.
Substitution into the pivot-first theorem gives the existential statement.

## Recurrence Reproduction

For monomial recurrence weights

```text
b_m = monomialRec step m,
```

the previous recurrence calculation gives divisibility whenever the target
level is later than the pivot level. In arbitrary pivot-first coordinates a
lower row may correspond to an earlier row index than the selected pivot row,
so the safe hypothesis is:

```text
b_(level i) = b_a       or       a <= level i.
```

In the equality branch the quotient is `1`; in the later branch it is the
tail product from level `a` to `level i`. This supplies the existential `q`
for pivot-first `Q/P`.

If every row weight is multiplied by the same selected chart variable `u`,
the same witness still works by commutativity:

```text
u * b_i = q_i * (u * b_a).
```

## Aoyagi Reading

For Aoyagi Case 2, the displayed source assumption

```text
b_(J+1)=...=b_(M(S))
```

means all residual row weights are flat. After the displayed substitution
`b'_i = u*b_i`, they remain flat. Thus the quotient witnesses in the
displayed pivot chart are trivial.

For Case 1 matrix pivots in the row strip `J+1..J+J1`, rows in the strip have
the same weight as the selected pivot row, while later residual rows are
handled by recurrence tails. This is the equality-or-later hypothesis. It does
not cover the Case 1 old-exceptional-variable branch, because that selected
generator is not a matrix row pivot.

The Lean checkpoint keeps these Aoyagi readings as hypotheses. It does not
claim that arbitrary selected-entry charts are source-reproduced or covered.

## Case 1 Membership Reproduction

The finite `Case1FirstJumpHypotheses` package already contains `1 <= J1` and
the strict row boundary `J+J1 < mu_S`. Therefore:

- under the source column bound `J+1 <= n_(S+1)`, the displayed pivot
  `(J+1,J+1)` is a Case 1 center generator;
- the same displayed pivot is also a residual-block candidate pivot;
- every Case 1 strip entry is a residual-block entry by row-strip containment.

These are finite membership corollaries only. They do not prove row-weight
recurrence equalities or any chart transition.

## Kill Conditions

- If the selected pivot entry is not already normalised to `1`, the
  pivot-first `Q/P` theorem cannot be applied.
- If weights and the following factor have not been transported to pivot-first
  coordinates, the existential `q` is for the wrong coordinates.
- If a row is neither equal in weight to the pivot row nor later in the
  monomial recurrence, the equality-or-later recurrence wrapper does not
  supply the quotient.
- Case 1(1) remains outside this matrix-pivot bridge.
