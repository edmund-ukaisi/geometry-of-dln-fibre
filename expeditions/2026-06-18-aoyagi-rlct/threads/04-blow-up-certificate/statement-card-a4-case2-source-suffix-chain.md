# Statement card - A4 Case 2 source suffix chain

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/MatrixChain.lean`
- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.paperMatrixChainStep`
- `DLNFibre.DLN.Aoyagi.paperMatrixChain`
- `DLNFibre.DLN.Aoyagi.paperMatrixChain_self`
- `DLNFibre.DLN.Aoyagi.paperMatrixChain_proof_irrel`
- `DLNFibre.DLN.Aoyagi.paperMatrixChain_succ_right`
- `DLNFibre.DLN.Aoyagi.paperMatrixChain_edge`
- `DLNFibre.DLN.Aoyagi.sourceLayerIndex`
- `DLNFibre.DLN.Aoyagi.sourceEdgeIndex`
- `DLNFibre.DLN.Aoyagi.sourceEdgeIndex_castSucc`
- `DLNFibre.DLN.Aoyagi.sourceEdgeIndex_succ`
- `DLNFibre.DLN.Aoyagi.sourceSuffixProduct`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceDisplayedOldTopSourceSuffixProduct_entryIdeal_eq_of_not_next_cont`

## Statement

Lean names the raw paper-order matrix-chain product

```text
C(i) C(i+1) ... C(j-1)
```

with right-multiplication recursion, and the Aoyagi source suffix

```text
prod_{s=S+2}^L C^(s)
```

as the product from layer `S+2` to layer `L+1`.

## Proved

- The raw paper-order matrix chain has identity empty product, proof
  irrelevance in the endpoint-order proof, right-extension recursion, and
  one-edge specialization.
- One-based source layer and source edge indices are related to zero-based
  `Fin` vertices and edges.
- The remaining Case 2 terminal suffix is named as `sourceSuffixProduct`.
- The existing source old-top/supplied-suffix terminal theorem is instantiated
  with `F = sourceSuffixProduct`.

## Assumed

- A finite family of composable paper-order matrices.
- For the Aoyagi suffix wrapper, the guard `S+1 <= L`.
- The stopped displayed Case 2 supplied chart-family boundary and failed next
  continuation, inherited from the previous terminal theorem.

## Not Proved

- No construction of Aoyagi's full source-produced `C'^(S+1)`.
- No chart production or chart coverage.
- No coordinate regularity, Jacobian arithmetic, normal crossings, RLCT
  extraction, termination, transition invariant, automatic Case 2 gap/tail
  transport, or printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-source-suffix-chain-a4.md`.
- Review artifact:
  `review-case2-source-suffix-chain-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/MatrixChain.lean`
- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- From `lean/`: `lake build DLNFibre`
- From `lean/`: `./scripts/sorries`
