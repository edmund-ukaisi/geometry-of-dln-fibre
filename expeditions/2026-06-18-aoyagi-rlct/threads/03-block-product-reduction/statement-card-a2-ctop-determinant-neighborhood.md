# Statement Card - A2 Ctop determinant neighborhood

Date: 2026-06-25.

## Claim

Let

```text
rho = (ι × ι) ⊕ ((ι × ν) ⊕ (μ × ι))
u : EuclideanSpace ℝ rho.
```

Define `X(u)` from the first tagged coordinate block and set
`Ctop(u) = 1 + X(u)`.  Then

```text
Ctop(0) = 1,
det(Ctop(0)) = 1,
∀ᶠ u in nhds 0, IsUnit(det(Ctop(u))).
```

Equivalently, there is `R > 0` such that every
`u ∈ Metric.ball 0 R` satisfies `IsUnit(det(Ctop(u)))`.  The radius can be
chosen no larger than any prescribed positive `Rmax`.

## Lean Artifacts

```text
AoyagiRegularBlockCoordinateIndex.continuous_ctopMatrix_euclidean
AoyagiRegularBlockCoordinateIndex.continuous_det_ctopMatrix_euclidean
AoyagiRegularBlockCoordinateIndex.ctopMatrix_zero
AoyagiRegularBlockCoordinateIndex.ctopMatrix_euclidean_zero
AoyagiRegularBlockCoordinateIndex.det_ctopMatrix_zero
AoyagiRegularBlockCoordinateIndex.det_ctopMatrix_euclidean_zero
AoyagiRegularBlockCoordinateIndex.isUnit_det_ctopMatrix_euclidean_zero
AoyagiRegularBlockCoordinateIndex.eventually_isUnit_det_ctopMatrix_euclidean_nhds_zero
AoyagiRegularBlockCoordinateIndex.exists_pos_ball_forall_isUnit_det_ctopMatrix_euclidean
AoyagiRegularBlockCoordinateIndex.exists_pos_radius_le_forall_isUnit_det_ctopMatrix_euclidean
```

## Inputs Kept Explicit

- `Fintype ι` and `DecidableEq ι` for the determinant;
- `Fintype μ` and `Fintype ν` for the metric-ball extraction on the full
  Euclidean regular-coordinate space.

## Nonclaims

No product-family continuity, source coverage, rank-stratum openness, product
chart, signed-box pushforward, density/Jacobian transport, normal crossings,
pole order, or RLCT extraction is proved.

## Verification

Focused direct local Lake build passed:
`env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates`.

Full direct local Lake build passed:
`env LEAN_NUM_THREADS=3 lake build DLNFibre`.
`scripts/sorries` reports zero `sorry`, `#exit`, `native_decide`, and
`axiom`; `git diff --check` is clean.
