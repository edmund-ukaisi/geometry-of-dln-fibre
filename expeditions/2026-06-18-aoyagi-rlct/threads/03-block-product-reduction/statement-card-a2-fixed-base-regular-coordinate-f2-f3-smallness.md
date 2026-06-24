# Statement Card - A2 fixed-base regular-coordinate F2/F3 smallness

Date: 2026-06-24.

Lean file:

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`

## Lean Names

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one
PaperEndpointFixedBaseRegularCoordinateSourceData.regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one_nhdsWithin_source
```

## Statement Shape

For real fixed-base source data

```text
sourceData :
  PaperEndpointFixedBaseRegularCoordinateSourceData
    W B U0 hU0 x0 Cedge H r rEdge,
```

let

```text
coord x =
  paperEndpointFixedBaseRegularBlockCoordinateMap W B U0 hU0 Cedge x.
```

Then eventually in the ambient filter `nhds x0`,

```text
squareSum (fun ij : iota x nu => coord x (inr (inl ij)))
+
squareSum (fun ij : mu x iota => coord x (inr (inr ij)))
<= 1.
```

The second theorem gives the same conclusion in

```text
nhdsWithin x0 (paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge).
```

## Proof Inputs

- The source-data theorem
  `regularBlockCoordinateMap_centered_continuousAt`, which packages
  `coord x0 = 0` and `ContinuousAt coord x0`.
- The tagged finite-real theorem
  `AoyagiRegularBlockCoordinateIndex.f2_f3_squareSum_eventually_le_one_of_forall_centered_continuousAt`.
- The filter inequality
  `nhdsWithin x0 S <= nhds x0` for the relative corollary.

## Scope

Real fixed-base source-data topology only.  The theorem specialises the actual
fixed-base scalar coordinate map; it does not construct analytic charts.

## Nonclaims

No source-rank openness, no source coverage, no analytic coordinate theorem,
no analytic ideal transport, no Fubini/polar regular-variable shift, no
normal-crossing construction, no pole-order theorem, and no RLCT extraction.
