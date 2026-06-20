# Statement card - A4 source suffix raw chain split

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/MatrixChain.lean`

Name:

- `DLNFibre.DLN.Aoyagi.paperMatrixChain_trans`

## Statement

For the raw paper-order matrix chain, if `i <= m <= j`, then the product from
`i` to `j` splits as the product from `i` to `m` followed by the product from
`m` to `j`:

```text
paperMatrixChain κ C i j (him.trans hmj)
  =
paperMatrixChain κ C i m him * paperMatrixChain κ C m j hmj.
```

## Proved

- The split orientation matches Aoyagi paper order: upper endpoint extension
  is right multiplication by the new edge.
- The proof uses `paperMatrixChain_self`, `paperMatrixChain_succ_right`, and
  matrix multiplication associativity.

## Not Proved

- No cast-heavy source-suffix empty or peel theorem yet.
- No chart production, coverage, Jacobian, normal-crossing/RLCT, termination,
  or transition-invariance result.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/MatrixChain.lean`
