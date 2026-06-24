# Reproduction - A2 fixed-base regular-coordinate F2/F3 smallness

Date: 2026-06-24.

Status: pen-and-paper reproduced; real fixed-base source-data wrapper
formalised in Lean.

## Target

The finite loss-comparison theorem needs the local hypothesis

```text
squareSum(F2_x) + squareSum(F3_x) <= 1.
```

The preceding two slices prove this first for arbitrary centered continuous
finite real coordinate families, and then for arbitrary tagged p. 13
regular-coordinate families.  This note records the fixed-base source-data
specialisation: the actual scalar coordinate map produced by
`PaperEndpointFixedBaseRegularCoordinateSourceData` satisfies the same
smallness condition in an ambient neighborhood of the base chain.

## Source-Data Coordinate Family

Specialise the scalar field to `real`.  Let `sourceData` be

```text
PaperEndpointFixedBaseRegularCoordinateSourceData
  W B U0 hU0 x0 Cedge H r rEdge.
```

It supplies the fixed-base p. 13 regular-coordinate map

```text
coord(x) =
  paperEndpointFixedBaseRegularBlockCoordinateMap W B U0 hU0 Cedge x.
```

The coordinate index is

```text
iota = Fin(finrank_R U0),
mu   = endpoint complement at Fin.last N,
nu   = endpoint complement at 0,

AoyagiRegularBlockCoordinateIndex iota mu nu
  = (iota x iota) ⊕ ((iota x nu) ⊕ (mu x iota)).
```

The `sourceData.scalarCoordinates_centered_continuousAt` field, equivalently
the packaged theorem

```text
regularBlockCoordinateMap_centered_continuousAt
```

gives

```text
coord(x0) = 0
and coord is continuous at x0.
```

Therefore each scalar coordinate is centered and continuous:

```text
for every c,
  coord(x0,c) = 0
  and x |-> coord(x,c) is continuous at x0.
```

## Ambient Smallness

Apply the tagged-coordinate theorem

```text
AoyagiRegularBlockCoordinateIndex
  .f2_f3_squareSum_eventually_le_one_of_forall_centered_continuousAt
```

to this `coord`.  It gives

```text
eventually x in nhds x0,
  squareSum(coord_x restricted to inr(inl -))
  +
  squareSum(coord_x restricted to inr(inr -))
  <= 1.
```

Under the p. 13 tags, `inr(inl -)` is exactly the `F2` block and
`inr(inr -)` is exactly the `F3` block.

## Relative Source-Stratum Corollary

Since

```text
nhdsWithin x0 sourceRankStratum <= nhds x0,
```

the same event also holds eventually in

```text
nhdsWithin x0 (paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge).
```

This step is only a filter weakening.  It uses no openness of the source-rank
stratum.

## Boundary

This is a real finite-topology theorem for the actual fixed-base scalar
coordinate map.  It is not a proof that the source-rank stratum is open, not
an analytic chart theorem, not a source coverage theorem, not analytic
ideal/germ transport, not Fubini/polar regular-variable additivity, not a
normal-crossing construction, and not an RLCT or pole-order theorem.
