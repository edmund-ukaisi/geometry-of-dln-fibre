# Reproduction - A2 open-source-stratum signed-box two-sided loss-density iff

Date: 2026-06-29.

Status: pen-and-paper checked; Lean formalised.

## Source Anchor

Aoyagi p. 13 works locally on the source-rank stratum.  A local signed-box
chart should therefore be allowed to represent only an open neighborhood piece
of the source stratum, not necessarily the entire source stratum.

This step packages that boundary.  It does not derive a local chart from a
larger chart image.  Instead it assumes the weighted signed-box pushforward
for the actual local piece

```text
source = Ulocal inter sourceStratum.
```

## Calculation

Let

```text
sourceStratum = paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge
source = Ulocal inter sourceStratum
```

with `Ulocal` open and `x0 in Ulocal`.  Then

```text
nhdsWithin x0 source = nhdsWithin x0 sourceStratum.
```

This is the only topology calculation: intersecting a set by an open
neighborhood of `x0` does not change the relative neighborhood filter.

Assume the signed-box source measure is exactly the restricted measure on this
local piece:

```text
mu.restrict source =
  Measure.map sourceChart
    (signedBox.withDensity (fun y => ofReal (sourceDensity y))).
```

Together with `0 < cres` and the monomial lower bound

```text
cres * product_i |y_i|^(2*kres_i) <= residualSquareSum(sourceChart y),
```

the local-source signed-box theorem supplies residual positivity on
`mu.restrict source`.  The explicit local boundedness input

```text
residualSquareSum x <= Rreg^2
```

is assumed on the same restricted measure.

The four supplied two-sided bounds are stated on
`nhdsWithin x0 sourceStratum`; the filter equality transports them to
`nhdsWithin x0 source`.  Applying the local-source signed-box two-sided iff
gives an open `Uchart` such that the actual p.13 loss-density integral over

```text
mu.restrict (Uchart inter source)
```

is finite iff the residual negative-power integral over that same source is
finite.  Returning

```text
U = Uchart inter Ulocal
```

rewrites `U inter sourceStratum` to `Uchart inter source`.

## Lean Shape

Lean formalises this in:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

Main theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_openSourceStratum_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
```

The proof:

1. defines `sourceStratum` and `source := Ulocal inter sourceStratum`;
2. proves the `nhdsWithin` filter equality using `Ulocal` open;
3. applies the local-source signed-box two-sided iff to `source`;
4. returns `Uchart inter Ulocal` and rewrites intersections.

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

passed after the Lean change.

## Nonclaims

- No proof of a signed-box chart construction.
- No proof that a pushforward identity for a larger source restricts to this
  open piece.
- No proof of local source-rank-stratum coverage.
- No proof of residual boundedness or the four p.13 loss/density comparison
  bounds.
- No proof of residual integrability from signed-box critical inequalities.
- No source-prior, Jacobian, density, or product-measure transport theorem.
- No original-loss identification.
- No normal-crossing theorem, pole-order theorem, or RLCT extraction.
