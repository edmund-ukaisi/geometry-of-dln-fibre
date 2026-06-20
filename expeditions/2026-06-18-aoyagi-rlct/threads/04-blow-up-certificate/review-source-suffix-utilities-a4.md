# Review - A4 source suffix utilities

Reviewed objects:

- `DLNFibre.DLN.Aoyagi.sourceSuffixProduct_proof_irrel`
- `DLNFibre.DLN.Aoyagi.sourceSuffixProduct_eq_paperMatrixChain`
- `DLNFibre.DLN.Aoyagi.sourceSuffixProduct_split_at`

Verdict: no blocking source/math or Lean API issue found.

The suffix orientation is correct for Aoyagi paper order.  The raw chain step
right-multiplies by the new edge, so the suffix is ordered as
`C^(S+2) ... C^L`, and the split theorem has orientation

```text
chain(S+2,T) * chain(T,L+1).
```

## Caveats

- `sourceSuffixProduct` is proof-irrelevant in `hS`; that bound certifies
  endpoints only.
- `sourceSuffixProduct_split_at` allows endpoint splits `T=S+2` and
  `T=L+1`.  The endpoint identity simplifications are not proved here.
- One-edge peel and empty-suffix identity theorems require additional
  dependent endpoint/cast wrappers and are not proved by this checkpoint.
- These are raw matrix-chain utilities only; no chart production or analytic
  result is proved.
