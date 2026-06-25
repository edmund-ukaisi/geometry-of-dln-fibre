# Reproduction - A2 Ctop determinant neighborhood

Date: 2026-06-25.

Status: pen-and-paper reproduction for the elementary determinant-chart
neighborhood used by the p.13 product-coordinate family.

## Source Boundary

This is independent of the quiver-based paper.  It formalizes only the
elementary fact that Aoyagi's regular-coordinate block

```text
Ctop(u) = I + X(u)
```

is invertible for all sufficiently small regular-coordinate vectors `u`.
It discharges the explicit chart hypothesis
`IsUnit(det(Ctop(u)))` near `u = 0`.

It does not prove continuity of the full product edge family, source
coverage, rank-stratum openness, signed-box pushforward, density/Jacobian
transport, normal crossings, pole order, or RLCT extraction.

## Calculation

Let

```text
rho = (ι × ι) ⊕ ((ι × ν) ⊕ (μ × ι))
u : EuclideanSpace ℝ rho.
```

Decode the first coordinate block as

```text
X(u) i j = u (Sum.inl (i,j)).
```

Then the p.13 regular block convention used in this repository is

```text
Ctop(u) = I + X(u).
```

At the centered coordinate vector,

```text
X(0) = 0,
Ctop(0) = I,
det(Ctop(0)) = det(I) = 1.
```

Since `1 ≠ 0` in `ℝ`, this determinant is a unit.

Each entry of `Ctop(u)` is either a constant identity entry plus one scalar
coordinate projection of `u`.  Hence `u ↦ Ctop(u)` is continuous.  The
determinant is a polynomial in finitely many matrix entries, hence

```text
d(u) = det(Ctop(u))
```

is continuous.  The unit locus in `ℝ` is open, so
`d⁻¹(ℝˣ)` is a neighborhood of `0`.  Therefore

```text
∀ᶠ u in nhds 0, IsUnit(det(Ctop(u))).
```

Equivalently, because the full regular-coordinate type is finite, there is a
positive Euclidean radius `R` such that

```text
u ∈ Metric.ball 0 R -> IsUnit(det(Ctop(u))).
```

The same radius may be shrunk below any prescribed positive `Rmax`.

## Lean Target

The new formal lemmas are in `AoyagiRegularBlockCoordinateIndex`:

```text
continuous_ctopMatrix_euclidean
continuous_det_ctopMatrix_euclidean
ctopMatrix_zero
ctopMatrix_euclidean_zero
det_ctopMatrix_zero
det_ctopMatrix_euclidean_zero
isUnit_det_ctopMatrix_euclidean_zero
eventually_isUnit_det_ctopMatrix_euclidean_nhds_zero
exists_pos_ball_forall_isUnit_det_ctopMatrix_euclidean
exists_pos_radius_le_forall_isUnit_det_ctopMatrix_euclidean
```

The continuity proof uses matrix-entry continuity and
`Continuous.matrix_det`.  The neighborhood proof uses the open-unit helper
`isOpen_setOf_isUnit`.

## Boundary

Only the determinant chart condition for `Ctop(u)` is proved.  This result
does not construct a product chart, prove that a source-dependent product
family is continuous in `(x,u)`, prove exact-rank/source coverage, transport
measures, produce normal crossings, prove pole order, or extract RLCT.
