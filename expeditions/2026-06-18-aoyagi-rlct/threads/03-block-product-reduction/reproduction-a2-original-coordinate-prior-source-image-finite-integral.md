# A2 reproduction: pushed original coordinate prior into the source-image finite-integral socket

## Status

Controller reproduction before Lean.  This is a project-internal measure
composition step, not a new theorem quoted from Aoyagi.

## Source boundary

Aoyagi supplies the original matrix-coordinate prior setting and the p.13
product reduction target.  The present calculation uses already-formalised
project infrastructure:

- finite-dimensional transport from flattened coordinates to fixed-basis
  edge-family coordinates;
- the conditional source-image domination bridge for the pushed coordinate
  prior;
- the existing source-image finite-integral socket for the p.13 readback loss.

The source-image density, determinant/raw Haar domination, local prior-density
upper bound, local source-density lower bound, source-rank/coverage,
product-zero density data, normal crossings, pole order, and RLCT extraction
remain external hypotheses or downstream targets.

## Objects

Fix the Case 2 passive-theta chart data and write

```text
Theta       = Case2PassiveTheta ...
EdgeFamily  = forall p : Fin 2, reverseVertex W2 p.castSucc ->L[real] reverseVertex W2 p.succ
sourceChart : Theta -> EdgeFamily
readback    : EdgeFamily -> Theta
thetaMu     = coordinateSourceMeasure
```

Let `d = paperEndpointFixedBaseDim W2 B2 U0` and let `b` be the fixed endpoint
finite basis.  For a flattened coordinate density `coordDensity`, define

```text
toEdge x = tupleToEdgeFamily b ((canonicalCoord d).symm x)
edgeDensity E = coordDensity (canonicalCoord d (edgeFamilyMatrixTuple b E)).
```

For a returned chart shrink `V`, the coordinate-side source-image bridge gives

```text
muV :=
  Measure.map toEdge
    ((originalCoordinatePrior d coordDensity).restrict
      (toEdge^{-1}(sourceChart '' V)))

muV <= Cprior * (Measure.map sourceChart (thetaMu.restrict V)).restrict (sourceChart '' V).
```

Here `Cprior` is the determinant/Haar/source/prior scalar assembled by the
previous source-image bridge.  Its finiteness is part of the returned package.

## Target calculation

The source-image finite-integral socket returns a loss shrink `W` and a local
source neighborhood `U`.  It accepts any external edge-family measure `mu`,
provided that on a measurable chart piece `chartPiece`:

```text
AEMeasurable readback (mu.restrict chartPiece)
Measure.map readback (mu.restrict chartPiece) <= C * thetaMu.restrict W
C < infinity.
```

We instantiate `mu = muV`.  Since the coordinate-prior domination is on the
image of `V`, while the finite-integral socket is local on `W`, choose only
chart pieces satisfying

```text
chartPiece subset sourceLocal
chartPiece subset sourceChart '' (V inter W).
```

Then every `E in chartPiece` has `E = sourceChart z` for some
`z in V inter W`, so the returned left-inverse identity gives

```text
readback E = z in W,
sourceChart (readback E) = E.
```

For the domination, first restrict the source-image bridge inequality:

```text
muV.restrict chartPiece <= Cprior *
  (Measure.map sourceChart (thetaMu.restrict V)).restrict (sourceChart '' V).
```

The chart-produced source-image reference pulls back through `readback` to
`thetaMu.restrict V`.  Since `chartPiece` is supported on
`sourceChart '' (V inter W)`, the readback pushforward of
`muV.restrict chartPiece` is supported on `V inter W`.  The local measure
handoff sharpens the previous domination to

```text
Measure.map readback (muV.restrict chartPiece)
  <= Cprior * thetaMu.restrict (V inter W)
  <= Cprior * thetaMu.restrict W.
```

Thus the external-measure finite-integral socket applies with
`C = Cprior`.

## Resulting finite integral

For the existing p.13 regular-coordinate loss integrand

```text
F(E,u) =
  ofReal ((ball 0 R).indicator
    (fun u => loss(E,u) ^ (-(t + regularVariableCount / 2))) u),
```

the conclusion is

```text
lintegral F d((muV.restrict chartPiece).prod nu) < infinity.
```

This is deliberately a finite integral for the pushed coordinate-prior image
measure after an additional edge-family restriction to `chartPiece`.  It does
not claim the stronger coordinate-domain identity

```text
muV.restrict chartPiece =
  Measure.map toEdge
    ((originalCoordinatePrior d coordDensity).restrict
      (toEdge^{-1}(chartPiece))).
```

That identity is a later transport-cleanup target if it becomes useful.

## Kill conditions

- The coordinate-prior bridge must return domination for the same `sourceChart`
  and `coordinateSourceMeasure` used by the finite-integral socket.
- `chartPiece` must be supported in `sourceChart '' (V inter W)`, not merely in
  `sourceChart '' V`; otherwise the readback need not land in the finite
  socket's shrink `W`.
- The readback left-inverse and injectivity hypotheses must be the ones
  returned for `V`; no global inverse is assumed.
- The finite scalar used in the finite-integral socket is exactly the
  coordinate-prior bridge scalar `Cprior`.
- The theorem must not infer source-image density construction,
  determinant/raw Haar transport, source coverage, normal crossings, pole
  order, or RLCT.
