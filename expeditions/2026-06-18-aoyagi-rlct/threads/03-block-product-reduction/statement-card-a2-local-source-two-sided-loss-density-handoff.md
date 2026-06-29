# Statement Card - A2 local-source two-sided loss-density handoff

Date: 2026-06-29.

## Claim

If four two-sided loss and density bounds are supplied in
`nhdsWithin x0 source`, uniformly for all regular coordinates in `ball(0,R)`,
then after shrinking to an open base neighborhood `U`, the same four bounds
hold almost everywhere over the restricted product measure

```text
(mu.restrict (U inter source)).prod nu.
```

The model is

```text
model(x,u) =
  aoyagiCoordinateSquareSum
    (paperEndpointFixedBaseResidualBlockCoordinateMap ... Cedge x)
  + aoyagiCoordinateSquareSum (fun i => u i).
```

The supplied bounds are:

```text
cL * model <= loss,
loss <= CL * model,
dRho <= density,
density <= DRho.
```

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

Main theorem name:

```text
exists_open_ae_restrict_localSource_prod_p13RegularCoordinates_two_sided_loss_density_bounds
```

## Proof Ingredients

- Four source-filter, uniform-in-fiber hypotheses;
- `exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin`;
- projection of one bundled a.e. base predicate into four product-measure a.e.
  conclusions.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

`scripts/sorries`, `git diff --check`, the touched Lean-file forbidden-marker
scan, and the direct axiom probe passed.  The axiom footprint for the theorem
is `[propext, Classical.choice, Quot.sound]`.

Independent xhigh review passed in
`review-a2-local-source-two-sided-loss-density-handoff.md`.

## Nonclaims

- No proof of the comparison hypotheses.
- No positivity assumptions on `R`, `cL`, `CL`, `dRho`, or `DRho`.
- No chart construction, chart coverage, source-prior transport, Jacobian
  theorem, density transport, residual integrability, integrability iff,
  normal-crossing, pole-order, or RLCT claim.
