# A2 Case 2: same-shrink raw domination and source-chart package

Status: reproduced and formalised in Lean.

## Question

The current reverse raw-source density theorem returns a local shrink `V` with

```text
rawHaar.restrict rawSourceSet
  <= (Cdet * epsilon^{-1}) *
     Measure.map rawMap (coordinateSourceMeasure.restrict V),
```

under explicit determinant-side reverse domination and an explicit lower bound
for `sourceDensity`.

Future original-volume/readback wrappers need this same `V` to also carry the
source-chart facts:

```text
readback (sourceChart z) = z,
sourceChart injective on V,
sourceChart continuous on V,
sourceChart '' V measurable,
sourceChart '' V subset p13SourceSet,
```

and the raw-chart/source-chart two-stage identity for measures restricted to
`V`.

## Shrink Order

Use three nested local shrinks.

1. Choose `Vsrc subset G` from the source-chart image package.  This gives the
   readback, injectivity, continuity, image measurability, and p.13 source-set
   inclusion facts on `Vsrc`.

2. Choose `Vtwo subset Vsrc` from the raw-order/source-chart two-stage package.
   This gives the pointwise raw-chart equality and, for every source measure,

   ```text
   Measure.map rawChart (Measure.map rawMap (sourceMeasure.restrict Vtwo))
     =
   Measure.map sourceChart (sourceMeasure.restrict Vtwo).
   ```

   The source-chart facts restrict from `Vsrc` to `Vtwo`.

3. Choose `V subset Vtwo` from the reverse raw-source density theorem.  This
   gives the determinant/lower-density domination conclusion on `V`.

All source-chart facts restrict from `Vsrc` to `V`.  The two-stage identity
also restricts to `V`: apply the `Vtwo` identity to the measure
`sourceMeasure.restrict V`.  Since `V subset Vtwo`, restricting this measure
again to `Vtwo` leaves it unchanged.

## Boundary

The package does not prove determinant-chart Haar transport, exact raw-Haar
pushforward, raw-Haar normalization, source-image coverage, source-rank
coverage, original source-prior transport, normal crossings, pole order, or
RLCT extraction.

The determinant-side reverse domination and source-density lower bound remain
explicit hypotheses in the final domination field.

## Lean Landing

Lean now proves the package theorem

```text
exists_open_subset_case2PassiveTheta_sourceChart_rawMap_coordinateSourceMeasure_reverse_domination_package_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
```

in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean`.

The proof follows the shrink order above.  The final two-stage identity is
obtained by applying the two-stage theorem to `sourceMeasure.restrict V` and
using the fact that this restricted measure is a.e. supported on `Vtwo`
because `V subset Vtwo`.

Verification passed through focused elaboration, focused module build, full
local `lake build DLNFibre`, `scripts/sorries`, `git diff --check`, and a
direct theorem axiom probe.  The theorem reports only
`[propext, Classical.choice, Quot.sound]`.

Xhigh read-only reviewer `Bohr` passed the theorem-shape and boundary audit in
`review-a2-case2-same-shrink-raw-domination-source-chart-package.md`.
