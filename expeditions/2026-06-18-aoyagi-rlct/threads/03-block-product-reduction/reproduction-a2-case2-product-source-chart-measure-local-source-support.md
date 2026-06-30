# Reproduction - A2 Case 2 Product Source-Chart Measure Local-Source Support

Date: 2026-06-30.

Status: pen-and-paper check before Lean. This is chart-produced measure
support only.

## Question

The pointwise small-ball theorem says that, after shrinking the p.13 regular
variables, the constructed product source point

```text
productSourceChart(theta,u)
```

lies in the retained-passive p.13 local source whenever `theta` is sufficiently
near the base source-rank filter and `u` lies in the small regular ball.

Can we turn that pointwise support into a pushforward-measure support identity?

## Calculation

Let the source-rank carrier be `sourceStratum`, and let the eventual theorem
return a neighborhood witness

```text
V inter sourceStratum ⊆
  {theta | forall u in regularBall,
    productSourceChart(theta,u) in localSource}.
```

For arbitrary measures `thetaMeasure` and `regularMeasure`, restrict the
product-domain measure to

```text
(thetaMeasure.restrict (V inter sourceStratum)).prod
  (regularMeasure.restrict regularBall).
```

The first marginal is almost everywhere in `V inter sourceStratum`; hence the
pointwise support statement holds for the first coordinate almost everywhere.
The second marginal is almost everywhere in `regularBall`. Therefore

```text
productSourceChart(theta,u) in localSource
```

holds almost everywhere for the restricted product-domain measure.

Applying the existing support helper

```text
measure_map_restrict_retainedPassiveP13LocalSource_eq_self_of_ae_mem
```

to the product source chart gives

```text
(Measure.map productSourceChart productDomainMeasure).restrict localSource =
  Measure.map productSourceChart productDomainMeasure.
```

## Lean Target

Add to
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`:

```text
exists_pos_radius_open_measure_map_case2PassiveThetaEndpointProductSourceChart_restrict_sourceRankStratum_ball_retainedPassiveP13LocalSource_eq_self
```

## Nonclaims

This does not prove source-rank coverage, source-image equality, original
source-prior transport, Haar/Jacobian transport, normal crossings, pole order,
or RLCT extraction. It also does not prove product-chart invertibility.
