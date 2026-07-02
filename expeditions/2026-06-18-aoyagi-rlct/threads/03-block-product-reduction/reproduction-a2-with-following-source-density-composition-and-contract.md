# Reproduction - A2 with-following source-density composition and contract

Date: 2026-07-02.

Status: reproduced before ledger integration; Lean implemented.

## Goal

Use the selected-entry source-density convention to make nested source
densities explicit, and use the existing raw-pushforward-to-source-reference
handoff to build the A2 bounded-density contract without separately supplying
the contract's equality and bound fields.

## Source-Density Composition

Let

```text
unweightedSource =
  passiveRef x centerSignedBox x followingRef
```

and let

```text
selectedEntryDensity(z) =
  ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext z.1.yNext).
```

The previous rung proved

```text
referenceSource =
  unweightedSource.withDensity selectedEntryDensity.
```

If `rawDensity : theta -> ENNReal` is any further source-side density, then
Mathlib's `withDensity_mul_0` gives

```text
(referenceSource.withDensity rawDensity)
  =
unweightedSource.withDensity
  (fun z => selectedEntryDensity z * rawDensity z),
```

provided both densities are a.e. measurable for `unweightedSource`.

The selected-entry a.e. measurability comes from the center selected-entry
source-density bounds, pulled through the product source:

```text
centerSignedBox --comp_snd--> passiveRef x centerSignedBox
                 --comp_fst--> (passiveRef x centerSignedBox) x followingRef.
```

The local restricted version is the same calculation after replacing
`unweightedSource` by `unweightedSource|Omega`, using `restrict_withDensity`
on both sides.

## Contract Constructor

The A2 formal-product/source-image contract stores:

```text
formalProductMeasure|chartPiece =
  ((map sourceChart (thetaReference|V)).withDensity density)|chartPiece
```

and

```text
density <= bound
```

almost everywhere on the restricted source reference.

The existing with-following source-reference theorem proves, under the raw
pushforward hypothesis

```text
map rawMap (thetaReference|V) = rawHaar|rawSourceSet,
```

that the p.13 formal-product measure satisfies the contract equality with
constant density `1` and bound `1`.

To package this as an `A2Case2FormalProductSourceImagePieceContract`, take two
shrinks:

1. First choose `V0` from the local with-following source-chart theorem.  On
   `V0`, the source chart is continuous and injective, its image is
   measurable, and readback is a left inverse.
2. Then apply the formal-product/source-reference raw-pushforward theorem
   inside `G = V0`, obtaining `V ⊆ V0` with the constant-density identity.

The local chart fields restrict from `V0` to `V`.  The image measurability of
`sourceChart '' V` is reproved from `V` open, `sourceChart` continuous on `V`,
and injective on `V`.  For any measurable chart piece lying both in
`sourceChart '' V` and in the p.13 source set, the contract is built with

```text
density = fun _ => 1,
bound = 1.
```

## Boundary

The constructor still assumes the raw-pushforward identity.  It also still
requires chart-piece measurability, membership in the actual local source
image, and membership in the p.13 source set.  It does not prove raw Haar
transport, determinant-chart Haar transport, source-image coverage,
source-prior transport, normal crossings, pole order, or RLCT extraction.

The source-density multiplication theorem is source-side measure algebra.  It
does not assert that the extra density is the retained-passive raw-order
Jacobian unless that density is supplied separately.

## Kill Conditions

- If the selected-entry density were not a.e. measurable for the unweighted
  source, `withDensity_mul_0` could not be used.  The product-measure
  measurability lift proves this explicitly.
- If the chart piece were only known to lie in the p.13 source set, the
  contract's readback field would be under-justified.  The theorem therefore
  keeps the separate `chartPiece subset sourceChart '' V` hypothesis.
- If the raw-pushforward equality were dropped, the formal-product equality
  would become a raw-Haar transport theorem.  It remains an explicit
  hypothesis.
