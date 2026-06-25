# Statement Card - A2 local measure handoff

## Statement

If `S` is measurable and

```text
forall eventually x in nhdsWithin x0 S, P(x),
```

then there exists an open neighborhood `U` of `x0` such that

```text
forall almost every x with respect to mu.restrict (U inter S), P(x).
```

For any auxiliary measurable coordinate space with measure `nu`, the product
version gives

```text
forall almost every z with respect to (mu.restrict (U inter S)).prod nu,
  P(z.1).
```

## Lean Names

```text
exists_open_ae_restrict_inter_of_eventually_nhdsWithin
exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin
```

## Dependencies

- `mem_nhdsWithin` for open relative-neighborhood witnesses;
- `ae_restrict_of_forall_mem`;
- `Measure.quasiMeasurePreserving_fst`.

## Nonclaims

No p.13 product chart, source-coordinate/product-coordinate identification,
loss comparison, density/Jacobian transport, integrability theorem, normal
crossing, pole order, or RLCT extraction is proved.
