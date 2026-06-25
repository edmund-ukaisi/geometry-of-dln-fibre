# Reproduction - A2 chain-map loss bridge

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean implementation; independent
statement review pending.

## Source Anchor

This is finite linear algebra connecting the repository's square-Frobenius
DLN loss to the chain-map matrix produced by the Aoyagi reversed-edge bridge.
It is not a new theorem from Aoyagi.

## Derivation

Fix bases

```text
b_j : Basis (Fin (d_j)) ℝ V_j
```

and edge maps

```text
A_p : V_p -> V_{p+1}.
```

The previous bridge defines the core tuple

```text
M_p = [A_p]_{b_p,b_{p+1}}
```

and proves

```text
mult d M = [chainMap(0,last)]_{b_0,b_last}.
```

The repository's DLN loss is definitionally

```text
lossDLN d B M = trace((mult d M - B)^T * (mult d M - B)).
```

Substituting the product bridge gives

```text
lossDLN d B M
  = trace(( [chainMap(0,last)]_{b_0,b_last} - B )^T
      * ( [chainMap(0,last)]_{b_0,b_last} - B )).
```

If the target matrix is itself the matrix of a fixed target chain `A0`, then

```text
B = [chainMap_A0(0,last)]_{b_0,b_last},
```

so the loss is the Frobenius trace of the difference of the two endpoint
chain-map matrices.

For Aoyagi's paper-order base chain `Bpaper`, instantiate

```text
V = reverseVertex W,
A0 = reverseEdge W Bpaper.
```

This gives an exact `lossDLN` rewrite for the tuple of reversed-edge matrices
in chosen endpoint bases.

## Lean Shape

Lean implements this in

```text
lean/DLNFibre/DLN/Aoyagi/ChainMapLossBridge.lean
```

with names

```text
chainMapMatrixFrobeniusLossAgainst
chainMapMatrixFrobeniusLoss
lossDLN_chainMapMatrixTuple_eq_trace
lossDLN_chainMapMatrixTuple_eq_chainMapFrobenius
lossDLN_reverseVertex_chainMapMatrixTuple_eq_baseFrobenius
```

The first two names are finite Frobenius-trace abbreviations.  The three
theorems rewrite `lossDLN` for an arbitrary target matrix, for a target
chain-map matrix, and for the Aoyagi reverse-vertex base-chain target.

## Boundary

This is an equality rewrite of `lossDLN` only.  It does not compare original
endpoint bases with fixed adapted endpoint bases, prove a positive
basis-change lower bound for this loss, identify a statistical/KL/covariance
loss, construct a product chart, transport density/Jacobian factors, produce
normal crossings, compute pole order, or extract an RLCT.
