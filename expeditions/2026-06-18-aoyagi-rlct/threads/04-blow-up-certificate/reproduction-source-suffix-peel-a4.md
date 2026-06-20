# A4 Source Suffix One-Edge Peel

Status: reproduced the nonempty one-edge peel for Aoyagi's raw source suffix
product.

## Source Anchor

Aoyagi's stopped Case 2 terminal display on PDF pp. 21-22 contains the right
product

```text
prod_{s=S+2}^L C^(s).
```

The previous source-suffix utility checkpoint named this as
`sourceSuffixProduct(S) = chain(S+2,L+1)` in raw paper order.

## Pen-And-Paper Reproduction

Assume the suffix has a first edge:

```text
S+2 <= L.
```

Then the first edge in the source suffix is the source edge `S+2`, whose lower
and upper source layers are

```text
S+2
S+3.
```

Using the raw paper-order chain split at the intermediate source layer `S+3`,
we get

```text
chain(S+2,L+1)
  = chain(S+2,S+3) * chain(S+3,L+1).
```

The one-edge chain is the corresponding edge matrix:

```text
chain(S+2,S+3) = C^(S+2).
```

Therefore

```text
prod_{s=S+2}^L C^(s)
  = C^(S+2) * prod_{s=S+3}^L C^(s).
```

The Lean statement uses `sourceSuffixFirstEdge` for the first factor.  This is
not new mathematics; it is the source edge `C^(S+2)` reindexed so that its
codomain is written with the same source-layer endpoint as the tail suffix.
When `S+2=L`, the tail suffix `prod_{s=S+3}^L C^(s)` is the empty product.

## Lean Shape

The Lean artifacts are:

```text
paperMatrixChain_succ_left
sourceSuffixFirstEdge
sourceSuffixProduct_peel
```

The raw theorem is

```text
paperMatrixChain(p,p+1,...,j)
  = C(p) * paperMatrixChain(p+1,j).
```

The source wrapper is

```text
sourceSuffixProduct(S)
  = sourceSuffixFirstEdge(S) * sourceSuffixProduct(S+1)
```

under `S+2 <= L`.

## Boundaries

- This is raw matrix-chain algebra only.
- `sourceSuffixFirstEdge` is a dependent-endpoint wrapper for `C^(S+2)`, not a
  chart-produced matrix.
- The empty-suffix identity is still not proved.
- No source-produced `C'^(S+1)`, chart production, chart coverage, Jacobian
  arithmetic, normal crossings, RLCT extraction, termination, transition
  invariance, or printed-vector repair is proved.
