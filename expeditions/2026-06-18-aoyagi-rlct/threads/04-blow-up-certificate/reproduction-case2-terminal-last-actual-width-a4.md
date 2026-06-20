# A4 Case 2 Terminal-Last Actual-Width Boundary

Status: reproduced the source-suffix terminal-last actual-width boundary.

## Source Anchor

Aoyagi's stopped Case 2 terminal expression on PDF pp. 21-22 has a remaining
source suffix

```text
prod_{s=S+2}^L C^(s).
```

When `S+1=L`, this suffix is empty.  The previous source-suffix checkpoint
proved the raw empty-chain identity with the required endpoint transport.

## Pen-And-Paper Reproduction

The source-suffix actual-width theorem gives

```text
ideal(M(q) * suffix) = ideal(T * suffix),
```

where:

- `M(q)` is the source old-top/transformed residual product;
- `T` is the terminal weight times original source rows `1..J+1`;
- `suffix = prod_{s=S+2}^L C^(s)`.

Under the terminal-last condition `S+1=L`, the suffix is the empty product.
Thus

```text
ideal(M(q)) = ideal(T).
```

Lean cannot treat the suffix endpoint equality as definitional: the suffix has
target `Fin.last L`, while `M(q)` has columns at
`sourceLayerIndex L (S+2)`.  The helper

```text
matrixEntryIdeal_mul_sourceSuffixProduct_terminalLast
```

uses the transported identity from
`sourceSuffixProduct_terminalLast_eq_cast_one` to remove the suffix at the
level of matrix-entry ideals.

The actual-width original-row branch still requires

```text
n(S+1)=J+1.
```

## Boundaries

- This theorem consumes the real source suffix and the terminal-last condition.
- It applies only to the actual-width original-row branch.
- The row-exhausted wide-next transported-row branch remains separate.
- It does not prove chart coverage, source production of `C'^(S+1)`,
  chart-produced following products, Jacobian arithmetic, normal
  crossings/RLCT extraction, termination, transition invariance, or repair of
  the printed Case 2 vector mismatch.
