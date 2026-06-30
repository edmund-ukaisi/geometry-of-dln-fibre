# Statement Card - A2 Source-Level External-Measure Density Handoff

## Claim

The full p.13 product finite-integral theorem can be fed by an external source
measure whose local restriction is a bounded-density perturbation of the
chart-produced source-image measure.

Public Lean names:

```text
restrict_withDensity_le_smul_restrict_of_ae_le

exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_externalSourceMeasure_eq_withDensity_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Inputs Used

- the previous full-product domination theorem;
- the same source-image density assumptions on
  `Measure.map sourceChart (baseJ.restrict W)`;
- source-stratum loss lower bound;
- local measurability of `sourceLocal = U intersect sourceStratum`;
- a source-level external measure `externalSourceMeasure`;
- a local equality
  `externalSourceMeasure.restrict sourceLocal =
  (sourceImageMeasure.withDensity externalDensity).restrict sourceLocal`;
- a local a.e. upper bound
  `externalDensity <= Cext` with respect to
  `sourceImageMeasure.restrict sourceLocal`;
- `Cext < infinity`;
- `[SFinite nu]` for the product-measure domination API.

## Output

For the returned open `U`, the theorem proves

```text
integral over ((externalSourceMeasure.restrict sourceLocal).prod nu)
  of the ball-truncated negative loss power is finite.
```

In Lean this is the lower integral of

```text
ofReal ((ball R).indicator
  (fun u => loss (z.1,u) ^ (-(t + regularCount/2))) z.2).
```

## Proof Shape

First prove the source-level domination:

```text
externalSourceMeasure.restrict sourceLocal
  <= Cext * sourceImageMeasure.restrict sourceLocal.
```

This is the local `restrict_withDensity` calculation from the reproduction
note. Then apply product domination to get

```text
(externalSourceMeasure.restrict sourceLocal).prod nu
  <= Cext * (sourceImageMeasure.restrict sourceLocal).prod nu,
```

and feed that into the previous full-product domination handoff.

## Nonclaims

No original DLN prior is constructed. No theorem says the original prior is
equal to this external source measure or satisfies the required density bound.
No Haar/source-prior transport, source-rank coverage, source-image equality,
normal crossings, pole order, or RLCT extraction is proved.
