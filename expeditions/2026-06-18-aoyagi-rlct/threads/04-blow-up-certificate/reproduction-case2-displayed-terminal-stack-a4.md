# A4 Case 2 Displayed Terminal Stack

Status: reproduced the finite entry-ideal statement obtained by stacking
unchanged old top rows over the stopped displayed Case 2 terminal block.
This is not the construction of Aoyagi's next-stage `C'^(S+1)`.

## Source Anchor

Aoyagi's Case 2 terminal paragraph on PDF pp. 21-22 rewrites the product
after the displayed `Q/P` calculation into a form with the next stage `S+1`.
The previous checkpoint proved the local pivot-first absorption

```text
< entries(D''' * C') > = < entries(C0) >
```

where `C0` is the top row of the transported following factor
`C' = Q^-1 C`.

This checkpoint adds the unchanged old top rows, denoted here by `Cold`.

## Pen-And-Paper Reproduction

For any two matrices `A` and `B` with the same column type, stacking them
generates the sum of the two entry ideals:

```text
< entries([A;B]) > = < entries(A) > + < entries(B) >.
```

Therefore, if `<entries(B)> = <entries(B')>`, then

```text
< entries([A;B]) > = < entries([A;B']) >.
```

Apply this with

```text
A  = Cold,
B  = D''' * C',
B' = C0.
```

Under displayed pivot validity and failed next continuation, the previous
checkpoint gives `<entries(B)> = <entries(B')>`.  Hence

```text
< entries([Cold; D''' * C']) >
  = < entries([Cold; C0]) >.
```

## Boundaries

- `Cold` is an arbitrary supplied top block with the same column type; Lean
  does not assert it is the source's actual old top rows.
- `C0` is the top pivot row of `Q^-1 C` in pivot-first coordinates.
- The result is matrix-entry ideal equality only, not matrix equality.
- This is not the diagonal-weighted full terminal product ideal from Aoyagi's
  terminal paragraph; diagonal monomial factors and the remaining following
  product are not included in this theorem.
- This does not identify `[Cold; C0]` with Aoyagi's full `C'^(S+1)`, choose
  the row-vs-column terminal presentation, construct chart-produced post-data,
  prove chart coverage or regularity, compute Jacobians, prove normal
  crossings, extract RLCT, prove termination or transition invariance, or
  repair the printed Case 2 vector mismatch.
