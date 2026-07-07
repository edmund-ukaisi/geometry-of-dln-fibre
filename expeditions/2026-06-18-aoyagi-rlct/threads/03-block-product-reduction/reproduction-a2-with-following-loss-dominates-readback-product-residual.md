# A2 with-following loss dominates readback product residual

## Object-level calculation

Work in the fixed-base p.13 source coordinates for the with-following Case 2
chart.  Let

```text
sourceChart : Theta -> EdgeFamily
readback    : EdgeFamily -> Theta
p13SourceSet = fixed-base p.13 source set
sourceStratum = fixed source-rank stratum
rankCutSource = (p13SourceSet cap readback^{-1} V) cap sourceStratum.
```

Assume the local chart has the same-shrink image identity

```text
sourceChart '' V = p13SourceSet cap readback^{-1} V,
```

and the left inverse

```text
readback (sourceChart z) = z   for z in V.
```

Assume also `V` lies in the determinant sector.  If
`E in rankCutSource`, then the image identity gives `E = sourceChart z` for
some `z in V`.  On such a point the already-formalised determinant-sector
residual readout gives

```text
squareSum(fixed p.13 residual block of E)
  = squareSum(with-following product residual of z),
```

and the left-inverse readback readout gives

```text
squareSum(readback product residual of E)
  = squareSum(with-following product residual of z).
```

Therefore on `rankCutSource`,

```text
squareSum(fixed p.13 residual block of E)
  = squareSum(readback product residual of E).
```

The fixed-base endpoint loss comparison, applied with `Cedge E = E`, gives a
constant `c > 0` such that eventually on `sourceStratum`,

```text
(c / 2) * (squareSum(regular coordinates of E)
  + squareSum(fixed p.13 residual block of E))
    <= lossDLN(E).
```

Restricting the eventual statement from `sourceStratum` to `rankCutSource` is
valid because `rankCutSource subset sourceStratum`.  Since the regular
coordinate square-sum is nonnegative and `c / 2 >= 0`, the preceding residual
equality gives the weaker but direct comparison

```text
(c / 2) * squareSum(readback product residual of E)
  <= lossDLN(E)
```

eventually on `rankCutSource`.

## Boundary

This is only a local analytic-algebraic comparison between the original
fixed-basis square-Frobenius loss and the with-following readback product
residual.  It does not prove source coverage, source-rank coverage,
source-prior transport, determinant/raw Haar transport, residual integrability,
normal crossings, pole order, or RLCT extraction.

## Kill conditions

- The statement must be restricted to the source-rank stratum used by the
  fixed-base endpoint loss comparison.
- The determinant-sector hypothesis is required for the fixed p.13 residual
  block to agree with the with-following product residual.
- The left-inverse and image identity are local hypotheses; a single chart is
  not a global coverage theorem.
- The theorem compares functions, not measures.  It must not be advertised as
  prior transport or integrability.
