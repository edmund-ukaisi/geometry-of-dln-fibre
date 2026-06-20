# A4 Source Suffix Utilities

Status: reproduced proof-irrelevance, definitional expansion, and split-at
utilities for Aoyagi's raw source suffix product.

## Source Anchor

The stopped Case 2 terminal display on Aoyagi PDF pp. 21-22 contains the
remaining right product

```text
prod_{s=S+2}^L C^(s).
```

Lean names this as `sourceSuffixProduct`, backed by the raw paper-order chain
`paperMatrixChain`.

## Pen-And-Paper Reproduction

The source suffix is a raw chain from source layer `S+2` to the final source
layer `L+1`:

```text
sourceSuffixProduct(S) = chain(S+2, L+1).
```

The proof of the bound `S+1 <= L` only certifies that this endpoint is valid.
It does not change the product, so the suffix is proof-irrelevant in that
bound.

If `T` is a one-based source layer with

```text
S+2 <= T <= L+1,
```

then the raw chain split gives

```text
sourceSuffixProduct(S)
  = chain(S+2,T) * chain(T,L+1).
```

This is the useful cast-light form.  The more paper-like one-edge peel

```text
prod_{s=S+2}^L C^(s)
  = C^(S+2) * prod_{s=S+3}^L C^(s)
```

requires additional dependent endpoint alignment between `sourceLayerIndex`
and `sourceEdgeIndex`; it is not claimed in this checkpoint.

## Lean Shape

The proved theorems are:

```text
sourceSuffixProduct_proof_irrel
sourceSuffixProduct_eq_paperMatrixChain
sourceSuffixProduct_split_at
```

`sourceSuffixProduct_split_at` states the split with named source
layer

```text
let i := sourceLayerIndex L (S+2) ...
let m := sourceLayerIndex L T ...
sourceSuffixProduct κ C S hS
  = paperMatrixChain κ C i m ... * paperMatrixChain κ C m (Fin.last L) ...
```

## Boundaries

- These are raw matrix-chain utilities only.
- No one-edge source-suffix peel theorem is proved.
- No empty-suffix identity theorem is proved.
- Endpoint splits `T=S+2` and `T=L+1` are allowed by the split theorem, but
  explicit identity simplifications for those endpoints are not proved.
- No source-produced `C'^(S+1)`, chart production, chart coverage, Jacobian
  arithmetic, normal crossings, RLCT extraction, termination, transition
  invariance, or printed-vector repair is proved.
