# Statement card - A4 source suffix terminal-last identity

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/MatrixChain.lean`

Name:

- `DLNFibre.DLN.Aoyagi.sourceLayerIndex_terminalLast`
- `DLNFibre.DLN.Aoyagi.sourceSuffixProduct_terminalLast_eq_cast_one`

## Statement

Lean exposes that Aoyagi's raw source suffix is the identity at the
terminal-last endpoint.  The theorem assumes `hLast : S+1=L`, so the suffix

```text
prod_{s=S+2}^L C^(s)
```

is empty.  Because the lower source-suffix endpoint and the final endpoint are
only propositionally equal, the identity matrix appears transported along the
endpoint equality.

## Proved

- The lower source-suffix endpoint `S+2` is the final source layer when
  `S+1=L`.
- The corresponding raw paper-order matrix chain is the identity after the
  endpoint transport.

## Assumed

- A semiring of coefficients.
- Finite index/typeclass data for the source-layer family and supplied edge
  matrices.

## Cited

- None.  This is finite matrix-chain bookkeeping.

## Deferred

- Terminal-last blow-up wrappers using `F := 1`.
- Chart coverage, chart production of `C'^(S+1)`, Jacobian arithmetic, normal
  crossings/RLCT extraction, termination, transition invariance, and printed
  vector repair.

## Review

- Review artifact:
  `review-source-suffix-terminal-last-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/MatrixChain.lean`
