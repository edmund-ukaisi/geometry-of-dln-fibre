# Reproduction - A2 multi-edge residual-product preservation

Date: 2026-06-25.

Status: pen-and-paper reproduction for the finite multi-edge p.13
product-coordinate residual-product slice.

## Source Boundary

Aoyagi p.13 separates the product-difference display into regular variables
`Ctop - I`, `F2`, `F3`, and a residual product.  This note treats only the
finite matrix recursion for at least two edges.  It does not construct a
source chart, prove continuity in a source variable, transport measures,
produce normal crossings, prove pole order, or extract RLCT.

## Calculation

Let the chain have `N + 2` edges and endpoint `j = Fin.last (N + 2)`.  Suppose
`Ebase` is a base fixed-coordinate edge family.  For every edge `p`, define the
residual factor

```text
C(p) = residualBlock(Ebase, j, p).
```

Build a new raw product-coordinate family `E` by the p.13 block patterns:

```text
E(last) = [ I   0
            -F3 C(last) ],

E(p)    = [ I 0
            0 C(p) ]        for 0 < p.val < N+1,

E(0)    = [ Ctop  -Ctop F2
            0      C(0) ].
```

The right endpoint starts the suffix tail with `B=0`, `Ctop=I`, and
`lowerLeft(L)=F3`.  Every middle edge has transformed block `[I,0;0,C(p)]`
because the current suffix tail has `B=0`; hence it preserves `B=0`,
`Ctop=I`, and `lowerLeft(L)=F3`.

At the left endpoint, the same tail invariant gives transformed edge
`[Ctop,-Ctop F2;0,C(0)]`.  Its Schur residual is `C(0)` because the lower-left
block is zero.  For middle edges the Schur residual is `C(p)` for the same
reason, and for the right endpoint it is `C(last)` because the upper-right
block is zero.

Thus every transformed Schur residual block visited by the new suffix
recursion agrees with the corresponding base transformed Schur residual block:

```text
residualBlock(E,j,p) = C(p) = residualBlock(Ebase,j,p).
```

The residual product is the ordered product of exactly these visited Schur
residual blocks, so residual-product congruence gives

```text
residualProduct(E,j,0) = residualProduct(Ebase,j,0).
```

## Lean Target

The generic congruence theorem is:

```text
ChartLocalSuffixState.residualProduct_eq_of_residualBlock_eq
```

The p.13 tail and residual preservation facts are:

```text
ChartLocalSuffixState.suffixState_tail_fields_of_productCoordinateEdges_from
ChartLocalSuffixState.residualBlock_productCoordinateEdges_succSucc
ChartLocalSuffixState.residualProduct_productCoordinateEdges_succSucc_eq_base
```

The proof is finite matrix algebra over a commutative ring.  The multi-edge
case does not need `IsUnit Ctop.det` for the residual-product equality because
the left endpoint lower-left block is zero; determinant-chart hypotheses are
still needed by downstream coordinate-readout theorems that also read the
regular fields.

## Boundary

This slice handles only edge count at least two.  The one-edge case is the
separate endpoint-collapse constructor.  No arbitrary final residual matrix is
realised in the multi-edge case; residuals must be supplied as edgewise factors
through the intermediate residual dimensions.
