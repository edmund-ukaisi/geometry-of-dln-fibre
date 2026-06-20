# A4 Case 2 Terminal-Last Row-Exhausted Boundary

Status: reproduced the terminal-last source-suffix removal for the
row-exhausted transported-prefix branch.

## Source Anchor

Aoyagi's stopped Case 2 terminal expression on PDF pp. 21-22 keeps the source
suffix

```text
prod_{s=S+2}^L C^(s).
```

The row-exhausted branch is the current-prefix exhaustion branch

```text
prefixMinNat n S = J+1.
```

It stops the next continuation, but it does not force actual next-width
exhaustion `n(S+1)=J+1`.

## Pen-And-Paper Reproduction

The existing row-exhausted source-chart source-suffix theorem gives

```text
ideal(M(q) * suffix) = ideal(Ttransported * suffix),
```

where:

- `M(q)` is the source old-top/transformed residual product;
- `Ttransported` is the terminal-prefix weight times the transported terminal
  prefix rows;
- `suffix = prod_{s=S+2}^L C^(s)`.

Under the terminal-last condition

```text
S+1=L,
```

the suffix is the empty product.  Because Lean represents the source-suffix
endpoint by a transported final layer, suffix removal is performed at the
matrix-entry-ideal level by

```text
matrixEntryIdeal_mul_sourceSuffixProduct_terminalLast.
```

Thus the terminal-last row-exhausted statement is

```text
ideal(M(q)) = ideal(Ttransported).
```

The last row of the transported-row factor inside `Ttransported` remains the
top row of `Q^-1 C`:

```text
C(J+1,-) + sum_{r=J+2}^{n(S+1)} d'_(J+1,r) C(r,-).
```

This correction sum is not removed in wide-next cases.

## Boundaries

- This consumes the real source suffix and the terminal-last hypothesis
  `S+1=L`.
- It applies only to the row-exhausted transported-prefix branch.
- It keeps `prefixMinNat n S=J+1` and does not assume `n(S+1)=J+1`.
- It does not identify the transported pivot row with the original source row.
- It does not relabel recurrence or exponent data to `(S+1,0)`.
- It does not prove chart coverage, source production of `C'^(S+1)`,
  chart-produced following products, Jacobian arithmetic, normal
  crossings/RLCT extraction, termination, transition invariance, or repair of
  the printed Case 2 vector mismatch.
