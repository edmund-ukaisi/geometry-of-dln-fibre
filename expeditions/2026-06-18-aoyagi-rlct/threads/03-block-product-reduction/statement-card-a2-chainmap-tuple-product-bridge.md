# Statement Card - A2 chain-map tuple product bridge

## Statement

For a finite chain of linear maps

```text
A_p : V_p -> V_{p+1}
```

and fixed bases `b_j : Basis (Fin (d_j)) K V_j`, form the core DLN tuple

```text
M_p = [A_p]_{b_p,b_{p+1}}.
```

Then the repository's core multiplication map agrees with the matrix of the
total chain composite:

```text
mult d M = [chainMap(0,last)]_{b_0,b_last}.
```

More generally, the interval product agrees with the matrix of the interval
chain composite:

```text
submult d M i j = [chainMap(i,j)]_{b_i,b_j}.
```

Equivalently, in inline Lean form,

```text
mult d (fun p => LinearMap.toMatrix (b p.castSucc) (b p.succ) (A p))
  =
LinearMap.toMatrix (b 0) (b (Fin.last N))
  (chainMap V A 0 (Fin.last N) (Fin.zero_le _)).
```

## Lean Names

```text
chainMapMatrixTuple
submult_chainMapMatrixTuple
multPrefix_chainMapMatrixTuple
mult_chainMapMatrixTuple
mult_toMatrix_chainMap
mult_toMatrix_chainMap_reverseVertex
```

## Dependencies

- `DLNFibre.Core.submult`;
- `DLNFibre.Core.Setup.multPrefix` and `DLNFibre.Core.Setup.mult`;
- `chainMap_self` and `chainMap_succ`;
- `LinearMap.toMatrix_comp`;
- fixed finite bases indexed by `Fin (d j)`.

## Role In A2

This is the missing product-coordinate bridge before connecting Aoyagi
endpoint chain-map matrices to the `Tuple d` consumed by `lossDLN`.

## Nonclaims

No `lossDLN` theorem, no target-matrix choice, no adapted-to-original
basis-norm comparison, no statistical/KL/covariance comparison, no product
chart, no density/Jacobian transport, no normal crossings, no pole order, and
no RLCT extraction is proved.
