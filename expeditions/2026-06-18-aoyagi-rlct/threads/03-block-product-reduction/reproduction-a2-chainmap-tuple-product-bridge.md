# Reproduction - A2 chain-map tuple product bridge

Date: 2026-06-25.

Status: pen-and-paper reproduction, Lean implementation, and xhigh scout
review.

## Source Anchor

This is finite linear algebra needed to connect Aoyagi's reversed-edge endpoint
chain with the repository's core DLN tuple product.  It is not a separate
source theorem from Aoyagi.

## Derivation

Let `V_0, ..., V_N` be finite-dimensional vector spaces, let

```text
A_p : V_p -> V_{p+1}
```

be the edge maps in the source-to-target indexing used by the repo's
`chainMap`, and choose bases

```text
b_j : Basis (Fin (d_j)) K V_j.
```

Define the matrix tuple

```text
M_p = [A_p]_{b_p,b_{p+1}}.
```

The core product `mult d M` is defined by prefix products:

```text
P_0 = I,
P_{p+1} = M_p * P_p.
```

The chain map satisfies the parallel recursion:

```text
chainMap(0,0) = id,
chainMap(0,p+1) = A_p ∘ chainMap(0,p).
```

Taking matrices in the chosen bases turns composition into multiplication in
the same order:

```text
[A_p ∘ chainMap(0,p)]_{b_0,b_{p+1}}
  = [A_p]_{b_p,b_{p+1}} * [chainMap(0,p)]_{b_0,b_p}.
```

The same argument from any lower endpoint gives

```text
submult d M i j = [chainMap(i,j)]_{b_i,b_j}.
```

In particular, induction on `p` from the initial endpoint gives

```text
multPrefix d M j = [chainMap(0,j)]_{b_0,b_j},
```

and at `j = Fin.last N`,

```text
mult d M = [chainMap(0,Fin.last N)]_{b_0,b_last}.
```

For Aoyagi's paper-order chain, the repo uses `reverseVertex W` and reversed
edges

```text
E_p : reverseVertex W p.castSucc -> reverseVertex W p.succ.
```

Instantiating the general theorem with `V = reverseVertex W` gives the needed
bridge between the core tuple product and the endpoint chain-map matrix.

## Lean Shape

Lean implements this in

```text
lean/DLNFibre/DLN/Aoyagi/ChainMapTupleBridge.lean
```

with names

```text
chainMapMatrixTuple
submult_chainMapMatrixTuple
multPrefix_chainMapMatrixTuple
mult_chainMapMatrixTuple
mult_toMatrix_chainMap
mult_toMatrix_chainMap_reverseVertex
```

The theorem `mult_toMatrix_chainMap` is the inline form:

```text
mult d (fun p => LinearMap.toMatrix (b p.castSucc) (b p.succ) (A p))
  =
LinearMap.toMatrix (b 0) (b (Fin.last N))
  (chainMap V A 0 (Fin.last N) (Fin.zero_le _)).
```

The theorem `mult_toMatrix_chainMap_reverseVertex` is the direct specialization
with `V = reverseVertex W`.

## Boundary

This proves the product-coordinate identity only.  It does not unfold
`lossDLN`, choose the target matrix `B`, compare original endpoint coordinates
with fixed adapted endpoint coordinates, prove any covariance or statistical
loss comparison, construct a product chart, transport density/Jacobian factors,
produce normal crossings, compute pole order, or extract an RLCT.
