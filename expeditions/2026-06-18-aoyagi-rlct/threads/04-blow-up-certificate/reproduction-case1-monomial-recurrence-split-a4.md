# A4 Case 1(2) Monomial Recurrence Split

Status: reproduced the elementary off-by-one recurrence split behind the
Case 1(2) factored-base boundary.

## Recurrence Convention

Lean uses

```text
monomialRec step 0 = 1,
monomialRec step (r+1) = step r * monomialRec step r.
```

Thus a label whose recurrence factor is at level `r` first affects row weight
`b_(r+1)`.

## Pen-And-Paper Split

Let `h = J + J1`, with `1 <= J1`, so `J < h`.

Use a factored-base recurrence `baseStep`, where the old selected variable has
already been replaced by its residual coordinate.  Then:

```text
sourceStep = baseStep with an extra factor u at level h,
postStep   = baseStep with an extra factor u at level J.
```

For a single extra factor at level `r`, rows `i <= r` are unchanged, while
rows `r+1 <= i` are multiplied by `u`.

Therefore, on the Case 1(2) strip `J+1 <= i <= h`:

```text
sourceWeight_i = baseWeight_i,
postWeight_i   = u * baseWeight_i.
```

Below the strip, `h+1 <= i`, both source and post weights are

```text
u * baseWeight_i.
```

This is the precise off-by-one reason that strip rows receive the selected
factor from divided source entries, while lower residual rows receive it from
the factored old row weights.

## Lean Boundary

Lean now names the single-factor step operation:

```text
mulStepAt step u r
```

and proves:

```text
monomialRec_mulStepAt_eq_of_le
monomialRec_mulStepAt_eq_mul_of_ge
monomialRec_mulStepAt_case1_strip_split
monomialRec_mulStepAt_case1_lower_eq
```

These are pure monomial-recurrence lemmas over a commutative monoid.  They do
not mention Aoyagi labels, chart coordinates, source validity, or post-data
production.

## Caveats

- This is not a Case 1 transition theorem.
- It does not construct the factored-base recurrence state.
- It does not prove that the PDF's chart produces the post recurrence state.
- It does not prove hidden old-label validity, chart coverage, regularity,
  Jacobian accounting, normal crossings, or RLCT extraction.
