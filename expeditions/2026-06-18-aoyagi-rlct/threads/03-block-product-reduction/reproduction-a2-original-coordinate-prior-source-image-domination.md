# A2 original coordinate prior source-image domination

Status: pen-and-paper reproduction checked; Lean target implemented and
locally verified.

## Question

The current source-image domination theorem controls the edge-family prior on
the returned chart image:

```text
(originalEdgeFamilyPrior b edgeDensity).restrict (sourceChart '' V)
  <= Cprior *
     (Measure.map sourceChart (coordinateSourceMeasure.restrict V)).restrict
       (sourceChart '' V).
```

The finite-dimensional coordinate-prior transport theorem identifies this
edge-family prior with the pushforward of the original flattened-coordinate
prior when the coordinate-side set is the preimage of the same edge-family
chart image.  This bridge exposes that coordinate-side formulation without
changing any determinant, density, or source-image hypotheses.

## Object-level calculation

Fix

```text
d = paperEndpointFixedBaseDim W2 B2 U0,
b = paperEndpointFixedBaseFinBasis W2 B2 U0 hU0,
Fcoord(x) = tupleToEdgeFamily(b)((canonicalCoord d)^(-1)(x)).
```

For a coordinate density `coordDensity`, define the induced edge-family density

```text
edgeDensity(E) =
  coordDensity(canonicalCoord d (edgeFamilyMatrixTuple b E)).
```

Let

```text
I = sourceChart '' V.
```

The preimage-form transport theorem gives, once `I` is measurable and the
tuple-side density is a.e.-measurable on

```text
(originalTupleVolume d).restrict ((tupleToEdgeFamily b)^(-1)(I)),
```

the equality

```text
Measure.map Fcoord
  ((originalCoordinatePrior d coordDensity).restrict (Fcoord^(-1)(I)))
  =
(originalEdgeFamilyPrior b edgeDensity).restrict I.
```

The existing source-image domination theorem gives the same returned open set
`V` and, for the same `I`, determinant-side reverse domination, source-density
lower bounds, and prior-density upper bounds imply

```text
(originalEdgeFamilyPrior b edgeDensity).restrict I
  <= Cprior *
     (Measure.map sourceChart (coordinateSourceMeasure.restrict V)).restrict I.
```

Substituting the transport equality into this domination gives

```text
Measure.map Fcoord
  ((originalCoordinatePrior d coordDensity).restrict (Fcoord^(-1)(I)))
  <= Cprior *
     (Measure.map sourceChart (coordinateSourceMeasure.restrict V)).restrict I.
```

No new analytic fact is used: the open chart package, determinant-side
reverse domination, finite scalar, source-density lower bound, and prior
upper bound are exactly the old hypotheses, with `density` replaced by the
induced `edgeDensity`.

## Source fidelity

Aoyagi uses an original matrix-parameter prior `phi(w) dw` and states the
DLN loss in original matrix coordinates.  The relevant source support is:

```text
pp. 3, 7-8: prior density on the original parameter space;
p. 8: RLCT target for the squared product difference;
pp. 10-13: elementary Schur/block product reduction in matrix coordinates;
p. 13: reduction to the product of residual matrices plus the RLCT shift.
```

The present bridge is Lean-local finite-dimensional bookkeeping that makes
the original coordinate prior visible at the source-image domination interface.
Aoyagi does not state this source-chart pushforward theorem, does not
construct the `sourceImageDensity` used here, and does not prove the
determinant/raw-Haar domination hypothesis in this form.

## Lean target

The theorem lives in:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalCoordinatePriorSourceImageBridge.lean
```

It consumes:

```text
map_canonicalCoord_symm_tupleToEdgeFamily_originalCoordinatePrior_restrict_preimage_eq_originalEdgeFamilyPrior_restrict

exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_eventually_sourceImageDensity_comp_sourceChart_lower_priorDensity_comp_sourceChart_upper
```

## Boundary

This proves only a coordinate-side restatement of an existing conditional
source-image domination theorem.  It does not construct a source-image
density, identify a chart-produced prior with Aoyagi's prior, compute a
retained-passive Jacobian, normalize Haar scalars, prove determinant/raw Haar
transport, prove source-rank or atlas coverage, construct normal crossings,
compute pole order, or extract RLCT.
