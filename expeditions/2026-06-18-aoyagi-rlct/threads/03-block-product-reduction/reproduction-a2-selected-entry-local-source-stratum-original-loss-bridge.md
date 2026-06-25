# Reproduction - A2 selected-entry local source-stratum original-loss bridge

Date: 2026-06-25.

## Scope

This slice weakens the previous global source-identification hypothesis

```text
sourceStratum = chartMap pivot '' signedBoxSet Rres
```

to a local source-identification hypothesis on a supplied open neighborhood
`Ulocal` of `x0`:

```text
Ulocal ∩ sourceStratum =
Ulocal ∩ (chartMap pivot '' signedBoxSet Rres).
```

It still does not construct Aoyagi's p.13 source chart or prove this local
equality.

## Pen-And-Paper Check

Let

```text
S = paperEndpointFixedBaseSourceRankStratum,
I = chartMap pivot '' signedBoxSet Rres.
```

Assume `Ulocal` is open, `x0 in Ulocal`, and `Ulocal ∩ S = Ulocal ∩ I`.
Then `Ulocal` is a neighborhood of `x0`, so relative neighborhoods may be
intersected with `Ulocal` without changing their germs:

```text
nhdsWithin x0 S
= nhdsWithin x0 (Ulocal ∩ S)
= nhdsWithin x0 (Ulocal ∩ I)
= nhdsWithin x0 I.
```

Thus any source-stratum-local lower bound can be reused on the finite
selected-entry chart image.

The existing product-family source theorem supplies a local source
`source = sourceU ∩ S`, a radius `Rprod > 0`, a constant `cprod > 0`, and

```text
cprod * (residualBase(x) + |u|^2)
  <= adaptedProductDifferenceSquareSum(x,u)
```

eventually in `nhdsWithin x0 source`.  Since the theorem also proves
`nhdsWithin x0 source = nhdsWithin x0 S`, the local equality above transports
this adapted lower bound to `nhdsWithin x0 I`.

The positive continuous transported density gives, after possibly shrinking
the radius to `R <= Rprod`, bounds on `nhdsWithin x0 I`:

```text
0 <= density(x,u),       density(x,u) <= C
```

for `u` in the regular-coordinate ball of radius `R`.

Now apply the finite chart-image original-loss wrapper on `I`.  It returns an
open set `Uchart` containing `x0` and a finite integral over

```text
volume.restrict (Uchart ∩ I).
```

Set `U = Uchart ∩ Ulocal`.  Then `U` is open, contains `x0`, and is contained
in `Ulocal`, so the local equality gives

```text
U ∩ S = U ∩ I.
```

The measure rewrite is therefore literal:

```text
volume.restrict (U ∩ S) = volume.restrict (U ∩ I).
```

Since `U ∩ I ⊆ Uchart ∩ I`, product-measure monotonicity gives finiteness of
the same nonnegative integrand over the smaller chart-image restriction.  The
measure equality then rewrites this finite integral as the desired integral
over `volume.restrict (U ∩ S)`.

## Lean Landing

Implemented in
`lean/DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean`.

Bridge lemmas:

```text
nhdsWithin_eq_of_mem_nhds_inter_eq
restrict_inter_eq_of_subset_inter_eq
```

Endpoint theorem:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_eq_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase
```

The proof calls the finite chart-image original-loss wrapper and the local
source product-family adapted lower-bound theorem.  The source/image equality
is used only as a local open-neighborhood hypothesis.

## Remaining Boundary

Still not proved:

- construction of the original p.13 DLN source chart;
- the local equality `Ulocal ∩ S = Ulocal ∩ I`;
- source-rank chart image/coverage;
- original-source Jacobian/prior transport beyond this local rewrite;
- normal crossings, pole order, or RLCT extraction.
