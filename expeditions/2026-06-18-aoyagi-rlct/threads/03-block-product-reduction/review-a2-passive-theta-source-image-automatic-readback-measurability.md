# Review - A2 passive theta source-image automatic readback measurability

Status: controller review before final build verification.

## Soundness Check

The proof only concerns the chart-produced measure

```text
Measure.map sourceChart (thetaReference.restrict V).
```

It does not assert readback measurability for arbitrary external measures.
The measurable-embedding argument is valid because the local source-chart
package supplies all four required facts on the same returned set `V`:
measurability of `V`, continuity on `V`, injectivity on `V`, and the pointwise
left inverse.

## Source Fidelity

The new step is not a new Aoyagi source claim.  It is standard measurable
embedding bookkeeping applied to the already-formalised p.13 local
source-chart/readback calculation.  It therefore stays inside the expedition's
allowed elementary formalisation boundary.

## Remaining Boundary

The previous source-prior boundary is unchanged.  The next non-wrapper target
is still an actual source-prior density/readback theorem, or a local
Haar/source-measure transport theorem that supplies the density identity for
the intended source/original prior.  The normal-crossing-to-RLCT extraction
remains cited.
