# Statement Card - A2 regular-coordinate F2/F3 smallness projection

Date: 2026-06-24.

Lean file:

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`

## Lean Name

```text
AoyagiRegularBlockCoordinateIndex.f2_f3_squareSum_eventually_le_one_of_forall_centered_continuousAt
```

## Statement Shape

For a finite tagged p. 13 regular-coordinate family

```text
coord : alpha -> AoyagiRegularBlockCoordinateIndex iota mu nu -> real,
```

if every tagged coordinate is zero at `x0` and continuous at `x0`, then
eventually in the ambient filter `nhds x0`,

```text
squareSum (fun ij : iota x nu =>
  coord x (inr (inl ij)))
+
squareSum (fun ij : mu x iota =>
  coord x (inr (inr ij)))
<= 1.
```

The theorem is a direct application of
`aoyagiCoordinateSquareSum_add_eventually_le_one_of_forall_centered_continuousAt`
to the `F2` and `F3` tagged subfamilies.

## Scope

Finite real product-topology projection only.  The theorem knows the p. 13
regular-coordinate tags, but it is not a source-stratum theorem and not an
analytic-coordinate theorem.

## Nonclaims

No source-rank openness, no source-stratum `nhdsWithin` wrapper, no analytic
chart, no ideal transport, no Fubini/polar shift, no normal-crossing
construction, no pole-order theorem, and no RLCT extraction is proved.
