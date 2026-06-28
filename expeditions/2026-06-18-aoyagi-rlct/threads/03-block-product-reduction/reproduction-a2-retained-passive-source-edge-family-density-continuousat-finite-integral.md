# Reproduction - A2 retained-passive source-edge-family density continuous-at finite integral

## Shape

The generic retained-passive source-edge-family chart-produced handoff takes
the density bounds as explicit local hypotheses:

```text
forall eventually x in nhdsWithin base localSource,
  forall u in ball 0 Rreg, 0 <= density (x,u)

forall eventually x in nhdsWithin base localSource,
  forall u in ball 0 Rreg, density (x,u) <= Creg.
```

It also takes `Rreg`, `Creg`, and `0 <= Creg`.  The target is the
radius-shrinking version for the same concrete source chart:

```text
sourceChart y =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U0 hU0
    (retainedData y).
```

Replace the supplied density-bound fields by:

```text
0 < Rmax
ContinuousAt density (base,0)
0 < density (base,0).
```

The conclusion returns `R`, `C`, and `U`, with

```text
0 < R, R <= Rmax, 0 <= C, IsOpen U, base in U,
```

and the same finite-integral conclusion over `ball 0 R`.

All source-edge-family data hypotheses from the previous generic theorem
remain explicit: `retainedData`, `hdet`, `hretainedData`, `hdataFactor`,
`residualCoordEquiv`, ambient `EdgeFamily` measurable/open-measurable/Borel
structure, determinant-subtype measurable/open-measurable structure, source
data, positive residual radii, the selected-entry critical inequality, Haar
measure on the regular variables, and the local loss lower bound on the larger
ball `ball 0 Rmax`.

## Calculation

Let

```text
EdgeFamily :=
  forall p : Fin (M + 1),
    reverseVertex W p.castSucc ->L[R] reverseVertex W p.succ

base p := LinearMap.toContinuousLinearMap (reverseEdge W B p)

localSource :=
  paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U0 hU0
    (fun E : EdgeFamily => E)
```

Apply the relative density-bounds lemma

```text
exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
```

with `alpha := EdgeFamily`, `E := EuclideanSpace R rhoReg`,
`x0 := base`, `s := localSource`, and the supplied `Rmax`.  It produces

```text
R, C,
0 < R, R <= Rmax, 0 <= C,
eventual nonnegativity of density on ball 0 R,
eventual upper bound density <= C on ball 0 R.
```

The local loss lower bound is assumed on `ball 0 Rmax`.  Since `R <= Rmax`,

```text
ball 0 R subset ball 0 Rmax,
```

so the same loss lower bound restricts to the smaller radius `R`.

Now invoke the generic source-edge-family chart-produced theorem

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceEdgeFamilyOfData_chartProducedMeasure
```

with

```text
Rreg := R
Creg := C.
```

It supplies an open source neighborhood `U` and the finite integral over
`ball 0 R`.  Package `R`, `C`, and `U` with the radius and bound facts from
the density-bounds lemma.

## Boundary

This removes the supplied local density nonnegativity/boundedness fields from
the generic retained-passive source-edge-family chart-produced handoff.  It
does not construct the density from an original prior, identify an external
source measure, compare Jacobians for such a prior, construct endpoint
equivalences, prove endpoint provenance, prove source-rank coverage, prove
normal crossings, compute pole order, or extract RLCT.

## Proved / Assumed / Deferred

**Proved by this reproduction.** A positive continuous density at `(base,0)`
supplies the density hypotheses needed by the generic source-edge-family
chart-produced finite-integral theorem after shrinking the regular-coordinate
radius.

**Assumed.** Retained-data determinant proof and a.e. measurability, ambient
`EdgeFamily` measurable/open-measurable/Borel structure, determinant-subtype
measurable/open-measurable structure, the retained-data residual-factor matrix
identity, positive residual radii, the selected-entry critical inequality,
regular-coordinate Haar measure, and the local loss lower bound on
`ball 0 Rmax`.

**Deferred.** Endpoint provenance, original prior/source measure
identification, Jacobian comparison, source-rank coverage, normal crossings,
pole order, and RLCT extraction.
