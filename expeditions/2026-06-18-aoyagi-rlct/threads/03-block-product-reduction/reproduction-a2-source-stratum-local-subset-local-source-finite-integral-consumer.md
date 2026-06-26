# Reproduction - A2 source-stratum local-subset local-source finite-integral consumer

Date: 2026-06-26.

## Scope

This slice is a boundary-explicit consumer for the local-source p.13
finite-integral theorem.  It does not construct the p.13 source chart.  It
assumes a local inclusion

```text
Ulocal ∩ sourceStratum ⊆ Ulocal ∩ localSource
```

and transports finite integrability from the supplied `localSource` to a
shrunk neighborhood of the full source-rank stratum.

## Pen-And-Paper Calculation

Let `S` be Aoyagi's fixed-base source-rank stratum, and let `L` be a supplied
measurable local source.  Assume `Ulocal` is open, `x0 in Ulocal`, and

```text
Ulocal ∩ S ⊆ Ulocal ∩ L.
```

The existing local-source theorem gives an open set `Uchart`, with
`x0 in Uchart`, such that the nonnegative p.13 integrand `F` has finite lower
integral over

```text
(mu.restrict (Uchart ∩ L)).prod nu.
```

Set

```text
U = Uchart ∩ Ulocal.
```

Then `U` is open and contains `x0`.  If `x in U ∩ S`, then
`x in Uchart` and `x in Ulocal ∩ S`; by the assumed local inclusion,
`x in L`.  Therefore

```text
U ∩ S ⊆ Uchart ∩ L.
```

By monotonicity of restricted measures, and then product-measure monotonicity,

```text
(mu.restrict (U ∩ S)).prod nu
  <= (mu.restrict (Uchart ∩ L)).prod nu.
```

Hence

```text
∫ F d((mu.restrict (U ∩ S)).prod nu)
  <= ∫ F d((mu.restrict (Uchart ∩ L)).prod nu) < ∞.
```

In Lean the product-restriction comparison uses
`Measure.restrict_prod_eq_prod_univ`, so the generic consumer carries
`[SFinite mu]`.

## Lean Landing

The landed theorem is in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_subset_localSource
```

It calls

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource
```

and then shrinks the returned open set by `Ulocal`.

## Boundary

Proved: finite integrability transfers from a measurable local source to a
locally covered portion of the source-rank stratum.

Assumed: local inclusion of the source-rank stratum in the supplied
`localSource`, residual positivity and negative-power integrability on
`localSource`, and the local source-filter loss/density bounds.

Cited: none beyond the existing analytic boundary elsewhere in the expedition.

Deferred: the actual p.13 local inverse/source-coverage theorem,
source-measure transport, density/Jacobian identity, normal-crossing
production, pole order, and RLCT extraction.
