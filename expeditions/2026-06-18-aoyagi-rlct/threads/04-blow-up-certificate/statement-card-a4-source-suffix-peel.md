# Statement card - A4 source suffix one-edge peel

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/MatrixChain.lean`

Names:

- `DLNFibre.DLN.Aoyagi.paperMatrixChain_succ_left`
- `DLNFibre.DLN.Aoyagi.sourceSuffixFirstEdge`
- `DLNFibre.DLN.Aoyagi.sourceSuffixProduct_peel`

## Statement

Lean now proves the one-edge peel for a nonempty Aoyagi source suffix:

```text
sourceSuffixProduct(S)
  = sourceSuffixFirstEdge(S) * sourceSuffixProduct(S+1)
```

under `S+2 <= L`.

## Proved

- A raw paper-order chain from `p` to `j` peels its first edge:
  `chain(p,p+1,...,j) = C(p) * chain(p+1,...,j)`.
- The source edge `S+2` is exposed as `sourceSuffixFirstEdge`, with endpoints
  written as source layers `S+2` and `S+3`.
- The source suffix `prod_{s=S+2}^L C^(s)` rewrites as the first source edge
  times `prod_{s=S+3}^L C^(s)`.
  When `S+2=L`, this tail is the empty product.

## Not Proved

- No empty-suffix identity theorem.
- `sourceSuffixFirstEdge` is only a reindexed supplied edge matrix; it is not a
  chart-produced terminal matrix.
- No chart production, chart coverage, Jacobian, normal-crossing/RLCT,
  termination, transition invariance, printed-vector repair, or
  source-produced `C'^(S+1)` theorem.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/MatrixChain.lean`
