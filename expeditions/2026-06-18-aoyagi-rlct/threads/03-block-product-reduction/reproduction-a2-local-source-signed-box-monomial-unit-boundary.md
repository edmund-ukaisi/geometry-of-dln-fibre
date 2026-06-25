# Reproduction - A2 local-source signed-box and monomial-unit boundary

Date: 2026-06-25.

## Scope

This slice moves the p.13 finite-integral front end from a global source-rank
stratum boundary toward a genuinely local chart boundary.  It does not construct
the Aoyagi chart or the measure pushforward.  It records two elementary
chart-side moves:

- local source restriction: if the signed-box chart only parametrizes a local
  source set, the finite-integral theorem should integrate over that source
  set rather than over the whole source-rank stratum;
- monomial units: if residual and source density are monomials times bounded
  units on the signed box, then they satisfy the exact lower/upper hypotheses
  consumed by the existing weighted signed-box source constructor.

## Pen-And-Paper Calculation

Let

```text
Q_k(y) = prod_i |y_i|^(2 k_i)
Q_h(y) = prod_i |y_i|^(h_i).
```

If the residual square is

```text
residual(y) = u_res(y) Q_k(y)
```

and `c <= u_res(y)` almost everywhere, then, because every factor
`|y_i|^a` is nonnegative for real `a`, we have

```text
c Q_k(y) <= u_res(y) Q_k(y) = residual(y)
```

almost everywhere.

Similarly, if the source density is

```text
sourceDensity(y) = u_den(y) Q_h(y),
```

with `0 <= u_den(y) <= C` almost everywhere, then

```text
0 <= sourceDensity(y)
sourceDensity(y) <= C Q_h(y)
```

almost everywhere.  If `u_den` is a.e.-measurable, then the density itself is
a.e.-measurable, because `Q_h` is a finite product of measurable functions
`y |-> |y_i|^(h_i)`.

For the local-source measure handoff, replace the full source-rank stratum `S`
by an arbitrary measurable local source `T`.  A bound holding eventually in
`nhdsWithin x0 T` becomes a.e. after restricting any base measure to
`U inter T` for a small open `U`.  The residual source hypotheses also restrict
from `T` to `U inter T` by monotonicity.  The finite p.13 integrability adapter
then applies with base measure `mu.restrict (U inter T)`.

## Lean Landing

The landed theorems are in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`:

```text
exists_open_ae_restrict_localSource_prod_p13RegularCoordinates_loss_density_bounds
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource
signedBox_monomialLower_sourceDensityBounds_of_monomialUnits
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
```

## Remaining Boundary

The local chart map, weighted pushforward identity, concrete residual/density
monomial-unit identities, normal-crossing extraction, pole order, and RLCT
extraction remain outside this slice.
