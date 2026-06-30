# Reproduction - A2 Source-Level External-Measure Density Handoff

Date: 2026-06-30.

Status: pen-and-paper check before Lean. This is a source-measure density
handoff into the existing full-product domination socket. It is not a proof of
original-prior transport.

## Question

The full-product domination handoff accepts an arbitrary product-coordinate
measure `mprod_ext` once we know

```text
mprod_ext <= Cext *
  ((sourceImageMeasure.restrict (U intersect sourceStratum)).prod nu).
```

Can this be fed by a source-level external measure whose local restriction is a
bounded-density perturbation of the chart-produced source-image measure?

## Calculation

Let

```text
mu = sourceImageMeasure
s  = U intersect sourceStratum
g  = externalDensity
```

and assume `s` is measurable. Suppose the externally supplied source measure
`mext` satisfies the local identity

```text
mext.restrict s = (mu.withDensity g).restrict s
```

and the local a.e. density bound

```text
g <= Cext    a.e. with respect to mu.restrict s,
```

with `Cext < infinity`.

The measure-theoretic calculation is:

```text
(mu.withDensity g).restrict s
  = (mu.restrict s).withDensity g
  <= (mu.restrict s).withDensity (fun _ => Cext)
  = Cext * (mu.restrict s).
```

Therefore

```text
mext.restrict s <= Cext * (mu.restrict s).
```

Taking product with the p.13 regular-coordinate Haar measure `nu` gives

```text
(mext.restrict s).prod nu
  <= Cext * ((mu.restrict s).prod nu).
```

This is exactly the domination hypothesis required by the earlier
full-product theorem. The only extra Lean-side hypothesis is `[SFinite nu]`,
which is the Mathlib API requirement for the product-domination lemma used
here.

## Lean Targets

Add the reusable local density helper in
`lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean`:

```text
restrict_withDensity_le_smul_restrict_of_ae_le
```

Add the source-level external-measure consumer in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge.lean`:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_externalSourceMeasure_eq_withDensity_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Source-Prior Boundary

The external source measure is not identified with the original DLN prior.
The theorem asks the caller to supply both the local equality against
`sourceImageMeasure.withDensity externalDensity` and the local finite upper
bound on `externalDensity`.

This leaves the actual source-prior task separate: constructing the full p.13
chart/readback map, proving the relevant Jacobian or density identity, and
showing the original prior satisfies such a bounded-density local equality.

## Nonclaims

No original/source-prior density identity, no proof that the original prior
satisfies the local equality, no Haar transport, no source-rank coverage, no
source-image equality, no normal crossings, no pole order, and no RLCT
extraction.
