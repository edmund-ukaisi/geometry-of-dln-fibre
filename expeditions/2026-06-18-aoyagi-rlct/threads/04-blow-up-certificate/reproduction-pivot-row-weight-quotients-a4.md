# A4 Pivot-Row Weight Quotient Witnesses

Status: checked generic quotient-witness reproduction; xhigh findings
incorporated. This is not a source reproduction of arbitrary pivot charts.

## Scope

This note isolates the quotient witnesses needed by the `P` row operation after
the generic pivot-first `Q/P` algebra bridge. The target is finite monomial
algebra: if a selected pivot row has weight `b0`, produce witnesses `q_i` such
that each lower-row weight satisfies

```text
b_i = q_i * b0.
```

It does not construct selected-entry charts, prove coordinate transport, prove
chart coverage, update exponents, or prove a Case 1/2 transition invariant.

The source text for the recurrence and Case 1 equality setup is Aoyagi PDF
p. 15; the displayed Case 1(2) and Case 2 top-left `Q/P` pivot calculations
are on PDF pp. 16-21.

## Source Data

Aoyagi defines the diagonal monomials by the recurrence

```text
b_0 = 1,
b_i = (prod_{tilde_t_(s,k)=i-1} u_(s,k)) * b_(i-1).
```

In the displayed top-left pivot branches, the `P` matrix contains entries

```text
-(b'_i / b'_(J+1)) * d''_(i,J+1),
```

so the regularity obligation is that `b'_(J+1)` divides every relevant `b'_i`.
For the displayed pivot this is a tail-product quotient from the recurrence.

Case 1 assumes

```text
b_(J+1) = ... = b_(J+J1),
b_(J+J1+1) != b_(J+J1),
```

equivalently there are no labels with `tilde_t = J+1,...,J+J1-1`. The equality
part makes quotient witnesses trivial inside the row strip. For later rows,
the recurrence gives the tail-product quotient.

Case 2 assumes

```text
b_(J+1) = ... = b_(M(S)),
```

equivalently there are no labels with `tilde_t = J+1,...,M(S)-1`. Therefore, in
the displayed residual row range, every row weight is equal to the pivot row
weight and the quotient witness can be `1`.

## Generic Reproduction

Let `weight : rho -> alpha` be row weights in a commutative monoid, and let
`pivot : rho` be the selected pivot row. The `P` theorem requires an explicit
function

```text
q : {i : rho // i != pivot} -> alpha
```

with

```text
weight i = q_i * weight pivot
```

for every non-pivot row `i`.

It is enough to prove divisibility for every non-pivot row:

```text
weight pivot divides weight i.
```

Choosing one quotient for each divisibility proof gives the required `q_i`.
This is the purely algebraic bridge from a divisibility proof to the exact
hypothesis shape used by `weightedPivotBlockRowOp`.

## Monomial Recurrence Reproduction

Let

```text
b_i = monomialRec step i.
```

The existing tail-product calculation proves:

```text
if a <= b, then b_a divides b_b.
```

For an arbitrary pivot-first row order, rows before the selected pivot do not
satisfy `pivot <= row`. They need a separate equality proof. Thus the safe
generic condition for every non-pivot row is:

```text
b_i = b_pivot    or    pivot_index <= i_index.
```

If `b_i = b_pivot`, take quotient `1`. If `pivot_index <= i_index`, use the
monomial tail-product quotient. Therefore the recurrence supplies quotient
witnesses under this equality-or-later-row condition.

If the chart multiplies all relevant row weights by a common selected variable
`u`, the same witnesses still work:

```text
b_i = q_i * b_pivot
=> u * b_i = q_i * (u * b_pivot),
```

using commutativity. This is the algebraic shape of Aoyagi's displayed
`b'_i = u * b_i` lines, independent of the separate ambiguity about the
standalone printed factor `u` before `diag(b')`.

## Aoyagi-Specific Reading

Aoyagi displays only the top-left pivot chart. The following arbitrary-pivot
reading is a conditional formalisation scaffold: it applies only after a
separate selected-entry chart, normalization, coordinate transport, and
pivot-first weight transport have been proved.

For Case 2 arbitrary matrix pivots, source equality of the residual row weights
is strong enough: every row in `J+1..M(S)` has the same weight as the selected
pivot row. The generic constant/equality witness theorem can be applied after
separate chart, normalization, and coordinate-transport proofs.

For Case 1(2) arbitrary strip-entry pivots, rows in the selected strip
`J+1..J+J1` have the same weight as the selected pivot row. Rows after the
strip are later recurrence rows, so the monomial tail-product gives
divisibility. This requires the selected pivot row to lie in the strip and the
row-strip-to-residual-block bound already isolated elsewhere:

```text
J+J1 <= mu_S.
```

It does not cover the Case 1(1) old-exceptional-variable chart, since that
selected generator is not a matrix row pivot.

## Lean Target

The current safe Lean checkpoint is generic quotient-witness infrastructure,
with `iota` later instantiated as a pivot-complement row type when needed:

```text
exists_right_quotients_of_forall_dvd
exists_right_quotients_of_forall_eq
exists_right_quotients_of_forall_eq_or_dvd
exists_right_quotients_monomialRec_of_le
exists_right_quotients_monomialRec_of_eq_or_le
exists_right_quotients_pivotMul_monomialRec_of_le
exists_right_quotients_pivotMul_monomialRec_of_eq_or_le
exists_right_quotients_const
exists_weightedPivotBlockRowOp_mul_diagonal_mul_of_forall_dvd
```

The theorems should not mention Aoyagi chart coverage or transitions. They
should produce exactly the witness shape needed by the pivot-first `Q/P`
corollaries.

## Kill Conditions

- If the selected pivot row is not a matrix row, as in Case 1(1), these
  witnesses are the wrong target.
- If a non-pivot row is neither equal in weight to the pivot row nor later in
  the monomial recurrence order, recurrence divisibility does not supply the
  witness.
- If the following factor and diagonal weights have not been transported to
  pivot-first coordinates, the witnesses do not instantiate the pivot-first
  `Q/P` theorem.
- If the selected pivot entry has not been normalized to `1`, the surrounding
  pivot-first block theorem is not applicable.
- These witnesses do not prove selected-entry chart construction, regularity
  of all coordinate changes, Jacobian behavior, exponent updates, termination,
  normal crossings, or RLCT extraction.
