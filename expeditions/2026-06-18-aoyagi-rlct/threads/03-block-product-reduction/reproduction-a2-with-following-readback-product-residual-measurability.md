# A2 with-following readback product-residual measurability

## Claim

For the enlarged Case 2 passive-theta source chart, the theta-side/source-coordinate
integrand

```text
z ↦ ofReal((Σ(readbackProductResidual(sourceChart z))^2)^(-t))
```

is a.e.-measurable on the local source measure used by the scalar-domination
original-prior handoff.  This is enough to remove the direct/active/source-cylinder
wrappers' explicit `Measurable (fun z => residualIntegrand (sourceChart z))`
hypothesis, without asserting global measurability of an arbitrary readback
pullback.

## Pen-and-paper check

The source chart sends a theta point `z` to the fixed-base p.13 edge family
realised from the retained-passive endpoint data attached to `z`.

```text
z
  ↦ retainedData(z)
  ↦ retainedData(z).edgeMatrix
  ↦ sourceChart(z).
```

The first map is continuous by the with-following endpoint-retained-data
construction.  The fixed-base edge-matrix readout is a finite-coordinate
function of the retained-passive data; its formulas use only finite matrix
addition, multiplication, and inverse.  Matrix inverse is globally
Borel-measurable on finite real matrices because it is the adjugate times the
inverse determinant.  Realising fixed-base matrices as continuous linear maps
is continuous.  This explains why the source-chart side is a finite-coordinate
measurability problem, but the Lean implementation uses a narrower package:
it proves continuity of the theta-side product-residual readout and then uses
the local left-inverse equality below.

The readback product residual, as a global edge-family expression, first
applies the endpoint source-chart readback to an edge family, then reads the
retained-passive residual product coordinates.

```text
E
  ↦ sourceReadback(edgeMatrix(E))
  ↦ endpoint-transported retained data
  ↦ C-field residualFactorProduct
  ↦ finite coordinate family.
```

Again the operations are finite-coordinate ones: edge-family to matrix
coordinates is continuous, `sourceReadback` is built from the same finite
matrix operations and inverses, endpoint transport is coordinate reindexing,
and the residual-factor product is a finite product of matrix blocks.  The
landed Lean proof does not need this as a standalone global measurability
theorem; it needs only the theta-side product-residual readout and the local
a.e. congruence.

Finally, `aoyagiCoordinateSquareSum` is a finite sum of coordinate squares,
`x ↦ x ^ (-t)` is Borel-measurable on `ℝ`, and `ENNReal.ofReal` is
measurable.  The composed theta-side/source-coordinate integrand is
measurable.  On the local set `Vsource` returned by the unit source-image-density
theorem, the local left-inverse identity `readback(sourceChart z) = z`
identifies this theta-side integrand with the readback residual pullback a.e.
Thus the product-transfer step needs only source-side a.e.-measurability.  This
is only a finite-coordinate measurability and local-left-inverse statement; it
does not assert source-image coverage, any measure transport identity, global
readback-pullback measurability, normal crossings, pole order, or RLCT
extraction.

## Lean target

Prove a reusable source-side measurability theorem near the with-following
residual readout definitions:

```text
measurable_case2PassiveThetaWithFollowingFactorProductResidualIntegrand
```

and use it, together with
`lintegral_prod_lt_top_of_aemeasurable_readback_map_le_smul_of_aemeasurable_source`,
to remove the explicit measurability hypothesis from the direct scalar-domination
original-prior finite-integral wrapper and its active/source-cylinder consumers.
