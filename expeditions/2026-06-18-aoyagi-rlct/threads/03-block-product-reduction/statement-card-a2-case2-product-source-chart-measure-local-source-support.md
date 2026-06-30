# Statement Card - A2 Case 2 Product Source-Chart Measure Local-Source Support

## Claim

After shrinking p.13 regular variables and choosing an open ambient base
neighborhood `V`, every pushforward of a product-domain measure restricted to
`V inter sourceStratum` and the regular ball is supported on the named
retained-passive p.13 local source.

Public Lean name:

```text
exists_pos_radius_open_measure_map_case2PassiveThetaEndpointProductSourceChart_restrict_sourceRankStratum_ball_retainedPassiveP13LocalSource_eq_self
```

## Inputs Used

- `exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_mem_retainedPassiveP13LocalSource_nhdsWithin_source`;
- `ae_restrict_mem` for the theta and regular restrictions;
- product-measure first/second projection a.e. facts;
- `measure_map_restrict_retainedPassiveP13LocalSource_eq_self_of_ae_mem`.

## Output

For any `thetaMeasure` and `regularMeasure`, if `productSourceChart` is
a.e. measurable for the restricted product-domain measure, then

```text
let μ := Measure.map productSourceChart productDomainMeasure
μ.restrict localSource = μ.
```

The theorem also exposes the deterministic support inclusion

```text
V inter sourceStratum ⊆
  {theta | forall u in regularBall,
    productSourceChart(theta,u) in localSource}.
```

## Nonclaims

No source-rank coverage, source-image equality, original source-prior
transport, Haar/Jacobian transport, normal crossings, pole order, RLCT, or
product-chart invertibility is proved.
