# A4 Case 2 Gap Row Weights

Status: checked finite recurrence reproduction for the displayed Case 2
residual row weights.

## Scope

Aoyagi's Case 2 calculation assumes there is no later jump before the end of
the current residual row range. In the repaired notation used by this
expedition, the displayed residual rows are

```text
I = {i | J+1 <= i <= mu_S},
mu_S = prefixMinNat n S.
```

This note proves only the elementary recurrence consequence: if the recurrence
factors from `J+1` through `mu_S-1` are all `1`, then all displayed residual
row weights are equal to the pivot row weight. It then records how that
flatness feeds the already-proved displayed source-substitution `Q/P` theorem.

It does not prove that Aoyagi's transition invariant produces the gap, does
not construct arbitrary pivot charts, and does not repair the printed Case 2
vector mismatch.

## Reproduction

Write the row-weight recurrence as

```text
b_0 = 1,
b_(r+1) = step_r * b_r.
```

For `a <= b`, induction gives

```text
b_b = (step_(b-1) * ... * step_a) * b_a.
```

If every factor `step_k` with `a <= k < b` is `1`, then the tail product is
`1`, hence

```text
b_b = b_a.
```

In displayed Case 2, take `a = J+1`. A residual source row `i` satisfies

```text
J+1 <= i <= mu_S.
```

The Case 2 gap hypothesis is

```text
step_k = 1,       J+1 <= k < mu_S.
```

For any residual row `i`, the interval `J+1 <= k < i` is contained in
`J+1 <= k < mu_S`, so

```text
b_i = b_(J+1).
```

Thus the displayed old row weights are flat across the residual rows. After
the selected-entry source substitution, the selected variable is counted once:

```text
newWeight_i = u * b_i.
```

The flatness gives

```text
newWeight_i = u * b_(J+1)
```

for every displayed residual row. This is the hypothesis required by the
already-proved source-substitution `Q/P` wrapper.

## Lean Shape

Generic recurrence facts:

```text
monomialTail_eq_one_of_forall_eq_one
monomialRec_eq_of_step_eq_one_on_Ico
```

Displayed Case 2 row-weight bridge:

```text
case2ResidualRow_monomialRec_eq_pivot_of_gap
exists_case2DisplayedQP_mul_sourceSubstitution_of_gap_monomialRec
```

## Normalisation and Boundary Checks

- The gap is stated as an explicit hypothesis on recurrence factors:
  `step k = 1` for `J+1 <= k < prefixMinNat n S`.
- The row range is `J+1..prefixMinNat n S`; columns and actual width
  bookkeeping use the source residual column range
  `J+1..n_(S+1)`.
- The displayed pivot validity hypothesis remains
  `J+1 <= prefixMinNat n (S+1)`.
- The selected variable is counted once in `u * b_i`.
- Rectangular residual blocks and continuation versus advance are not settled
  by this recurrence calculation.

## Kill Conditions

- If the source gap is not established for the actual recursive state, this is
  only a conditional row-weight bridge.
- If row weights are indexed by something other than the displayed source row,
  this theorem is not the intended source recurrence bridge.
- If an additional outside `u` is also multiplied into the displayed diagonal
  after defining `newWeight_i = u*b_i`, the normalization is wrong.
- This theorem does not prove arbitrary pivot coverage, polynomial chart
  regularity/Jacobian facts, exponent updates, transition invariants,
  termination, normal crossings, or RLCT extraction.
