# A2 Case 2 lossDLN finite integral with product-step inverse density

## Source calculation

The existing Case 2 finite-integral theorem for endpoint `lossDLN` accepts an
arbitrary product-coordinate density

```text
density : EdgeFamily x rhoReg -> Real
```

and assumes

```text
ContinuousAt density (base,0)
0 < density(base,0).
```

For the p.13 product-reduction step, the density is not arbitrary.  It is the
chart-side inverse Jacobian density of the raw product-reduction coordinates
evaluated on the p.13 raw-shaped tuple:

```text
invJacDensity(x,u)
  =
productReductionStepRawOrderInverseJacobianDensity
  (paperEndpointFixedBaseP13RawOrderTuple
    W2 B2 U0 hU0 (fun E => E) (x,u)).
```

The base edge-family map is the identity on `EdgeFamily`:

```text
CedgeBase = fun E => E.
```

This is essential.  The density belongs to the edge-family p.13 coordinates in
the finite-integral theorem, not to the selected-entry value-coordinate source
chart used in the product-measure handoff.

## Density regularity

The p.13 density file proves the two required facts at the self-base point:

```text
continuousAt_paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_selfBase
paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_pos_center
```

With `CedgeBase = id`, continuity of `CedgeBase` is `continuous_id`, and the
base identity is exactly the definition of

```text
base p = toContinuousLinearMap (reverseEdge W2 B2 p).
```

Therefore the arbitrary-density hypotheses in the existing Case 2 theorem can
be discharged for `invJacDensity`.

## Finite-integral handoff

After this substitution, the existing endpoint `lossDLN` theorem supplies
`R`, `C`, and an open neighborhood `U` of `base` such that

```text
lintegral
  ofReal
    (indicator ball(0,R)
      (fun u =>
        lossDLN(...) ^ (-(t + regularVariableCount/2))
          * invJacDensity(z.1,u))
      z.2)
  over (mu.restrict (U cap sourceStratum)).prod nu
  < infinity.
```

The theorem still assumes the selected-entry source-chart measure, source-rank
stratum data, positive selected-entry radii, and the selected-entry critical
inequality.  It also still uses the local loss lower bound produced inside the
existing arbitrary-density theorem.  The new theorem only removes the
unnecessary caller-supplied density regularity hypotheses.

## Lean target

Implemented in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Declaration:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure
```

## Boundary

This proves only a Case 2 finite-integral handoff with the concrete p.13
product-step inverse-Jacobian density.  It does not identify the original
source prior, prove source/product-coordinate measure transport, prove raw
Haar transport, construct normal crossings, compute pole order, or extract
RLCT.
