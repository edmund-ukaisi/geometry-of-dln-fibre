# A4 Source Suffix Terminal-Last Identity

Status: reproduced the empty raw source suffix at the terminal layer.

## Source Anchor

Aoyagi's stopped terminal expression on PDF pp. 21-22 contains the remaining
right product

```text
prod_{s=S+2}^L C^(s).
```

When the stopped stage is terminal-last, `S+1=L`, this is the empty product
`prod_{s=L+1}^L C^(s)`.

## Pen-And-Paper Reproduction

The Lean source suffix is

```text
sourceSuffixProduct(S) = paperMatrixChain(source layer S+2, final source layer L+1).
```

If `S+1=L`, then the lower endpoint is source layer `S+2=L+1`, which is also
the final source layer.  The raw paper-order chain has equal endpoints, so by
the empty-chain identity

```text
paperMatrixChain(i,i) = 1,
```

we get

```text
sourceSuffixProduct(S) = 1.
```

In Lean the endpoints are propositionally, not definitionally, equal under
`hLast : S+1=L`.  The theorem therefore keeps the general `hLast` form and
writes the right-hand side as the identity matrix transported along

```text
sourceLayerIndex L (S+2) = Fin.last L.
```

## Lean Shape

The helper

```text
sourceLayerIndex_terminalLast
```

proves the endpoint equality.  The main theorem

```text
sourceSuffixProduct_terminalLast_eq_cast_one
```

then rewrites `sourceSuffixProduct` to the raw empty chain
`paperMatrixChain(i,i)` and applies the raw identity theorem
`paperMatrixChain_self`.

## Boundaries

- This is raw matrix-chain algebra only.
- It supplies the raw suffix identity needed by any terminal-last wrapper whose
  following factor is exactly this source suffix.
- It does not justify setting an arbitrary following matrix to `1` when
  `S+1 < L`.
- It does not prove chart coverage, chart production of `C'^(S+1)`, Jacobian
  arithmetic, normal crossings/RLCT extraction, termination, transition
  invariance, or repair of the printed Case 2 vector mismatch.
