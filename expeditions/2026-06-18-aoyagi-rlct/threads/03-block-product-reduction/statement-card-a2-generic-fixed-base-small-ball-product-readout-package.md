# Statement Card - A2 generic fixed-base small-ball product readout package

## Claim

For the generic fixed-base p.13 source-dependent product-coordinate family,
there is a positive regular-coordinate radius `R <= Rmax` such that every base
point `x` and every `u in ball 0 R` satisfy one fixed-base readout package:

```text
IsUnit det(Ctop(u))
regularCoordinateMap(CedgeProd(x,u)) = u
residualCoordinateMap(CedgeProd(x,u))
  =
residualCoordinateMap(CedgeBase x)
sourceReadback(CedgeProd(x,u)) has the canonical p.13 product fields
```

Public Lean name:

```text
exists_pos_radius_le_forall_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_readout_package
```

## Inputs Used

- an arbitrary fixed-base source edge family `CedgeBase`;
- the p.13 source-dependent product-coordinate constructor over that family;
- a positive radius cap `Rmax`;
- determinant-unit smallness for `ctopMatrix`;
- the pointwise raw regular/residual coordinate readout theorem;
- the pointwise generic fixed-base source-readback field theorem.

## Output

Lean returns `R > 0`, `R <= Rmax`, and for every `x` and every
`u in ball 0 R`:

```text
IsUnit det(Ctop(u))
regularCoordinateMap(CedgeProd(x,u)) = u
residualCoordinateMap(CedgeProd(x,u))
  =
residualCoordinateMap(CedgeBase x)
A1passive = 1
F2        = first decoded F2(u), then zeros
A3passive = 0
C         = residualBlock(fixedBase(CedgeBase x))
Ctop      = decoded Ctop(u)
F3        = decoded F3(u)
```

## Proof Shape

Choose `R` using

```text
AoyagiRegularBlockCoordinateIndex.exists_pos_radius_le_forall_isUnit_det_ctopMatrix_euclidean
```

Then use the resulting `hCtop` in:

```text
paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily
paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceReadback_fields
```

## Nonclaims

This is fixed-base local coordinate algebra.  It does not recover an original
parameter, prove source-image coverage, identify a source prior, prove
Haar/Jacobian transport, establish normal crossings, compute pole order, or
extract an RLCT.

## Status

Focused direct Lean check, focused module build, full local `lake build
DLNFibre`, `scripts/sorries`, `git diff --check`, and direct axiom probe
passed.  The axiom footprint is `[propext, Classical.choice, Quot.sound]`.
