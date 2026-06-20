# Statement card - A4 source suffix utilities

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/MatrixChain.lean`

Names:

- `DLNFibre.DLN.Aoyagi.sourceSuffixProduct_proof_irrel`
- `DLNFibre.DLN.Aoyagi.sourceSuffixProduct_eq_paperMatrixChain`
- `DLNFibre.DLN.Aoyagi.sourceSuffixProduct_split_at`

## Statement

Lean now exposes proof irrelevance, definitional expansion, and split-at-layer
utilities for Aoyagi's raw source suffix product
`prod_{s=S+2}^L C^(s)`.

## Proved

- `sourceSuffixProduct` is independent of the proof of `S+1 <= L`.
- `sourceSuffixProduct` is the raw paper-order chain from source layer `S+2`
  to the final source layer.
- If `S+2 <= T <= L+1`, the suffix splits at the source layer `T` as
  `chain(S+2,T) * chain(T,L+1)`.

## Not Proved

- No one-edge source-suffix peel theorem.
- No empty-suffix identity theorem.
- Endpoint split identity simplifications are not proved.
- No chart production, chart coverage, Jacobian, normal-crossing/RLCT,
  termination, transition invariance, or source-produced `C'^(S+1)` theorem.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/MatrixChain.lean`
