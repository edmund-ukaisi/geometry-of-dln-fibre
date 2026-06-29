# Statement Card - A2 source-stratum two-sided loss-density handoff

Date: 2026-06-29.

## Claim

The local-source two-sided loss-density handoff specializes to Aoyagi's
source-rank stratum.  Four supplied `nhdsWithin x0 sourceStratum` bounds,
uniform in the regular-coordinate ball, become four a.e. facts over one common
restricted product measure:

```text
(mu.restrict (U inter sourceStratum)).prod nu.
```

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

Main theorem name:

```text
exists_open_ae_restrict_source_prod_p13RegularCoordinates_two_sided_loss_density_bounds
```

## Proof Ingredients

- the local-source two-sided handoff;
- `source := paperEndpointFixedBaseSourceRankStratum (K := R) W B Cedge r rEdge`;
- definitional rewriting by the local abbreviation `sourceStratum`.

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
`review-a2-source-stratum-two-sided-loss-density-handoff.md`.

## Nonclaims

- No proof of the comparison hypotheses.
- No positivity assumptions on `R`, `cL`, `CL`, `dRho`, or `DRho`.
- No proof that the source-rank stratum is open, a neighborhood, covered by a
  chart, or equal to a chart image.
- No source-prior transport, Jacobian/density theorem, product-measure
  transport, residual integrability, finite integral, integrability iff,
  normal-crossing, pole-order, or RLCT claim.
