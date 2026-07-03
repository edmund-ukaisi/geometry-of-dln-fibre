# Thread 03 - block and product reduction

Type: formalisation. Status: in-progress.

## Task

Formalise Aoyagi's elementary matrix reductions: the full-rank block elimination
and product reduction.

## Output contract

- Lean statements for Claim A1 and Claim A2 at exact scope.
- Proofs where elementary; any analytic/local hypotheses named explicitly.
- Statement cards at AUDIT time.

## Controller notes

Read `lean/CLAUDE.md` before Lean work. Keep Aoyagi/DLN application code out of
`DLNFibre.Core`.

Build-policy override for this expedition worktree: use local `lake build` and
`lake env lean`, not `scripts/lb`.

## 2026-07-03 A2 endpoint-patch null-measurability

Reproduction:
`reproduction-a2-endpoint-patch-null-measurability.md`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13SourceMeasureBridge.lean
```

Lean now proves the generic helper:

```text
nullMeasurableSet_inter_preimage_inter_of_aemeasurable_comp
```

and the p.13 endpoint-patch specialization:

```text
nullMeasurableSet_topologyTupleDetChart_inter_rawOrder_preimage_p13RawOrderSourceChart_chartPiece
```

For a measurable p.13 chart piece and the natural patch

```text
P = rawSourceSet ∩ rawChart ⁻¹' chartPiece,
```

the specialization proves `P ⊆ rawSourceSet` and

```text
NullMeasurableSet
  (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P) m.
```

Boundary: this is only the set/null-measurability half of the localized
endpoint-patch socket.  It does not prove the finite scalar domination
needed by the readback layer, endpoint Haar transport, raw-Haar
normalization, source-image coverage, original-prior transport, normal
crossings, pole order, or RLCT.

Verification passed: focused local builds of
`DLNFibre.DLN.Aoyagi.LocalMeasureHandoff`,
`DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13SourceMeasureBridge`, and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination`;
full local `lake build DLNFibre`; `lean/scripts/sorries`; `git diff --check`;
touched Lean-file marker scan; and direct axiom probe.  The two new
declarations report `[propext, Classical.choice, Quot.sound]`.

## 2026-07-03 A2 unit source-image density finite-integral wrapper

Reproduction:
`reproduction-a2-unit-source-image-density-finite-integral-wrapper.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_passiveLocalSet_matrixEntryReference_open_followingPatch_open_subset_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_sourceImageDensity_one
```

This is the unit-density specialization of the source-density continuity
finite-integral wrapper.  It fixes:

```text
sourceImageDensity E = 1
sourceDensity z = 1
```

so the continuity and finite-base-value assumptions are discharged internally
by constant continuity and `1 < top`.

Boundary: this only proves the unweighted chart-produced coordinate-source
case.  It does not identify an original DLN prior, construct an arbitrary
source-image density, prove source-image coverage, determinant-Haar/raw-Haar
transport, original-prior transport, normal crossings, pole order, or RLCT.

Verification passed: focused local build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawImageHandoff`; full
local `lake build DLNFibre`; `lean/scripts/sorries`; `git diff --check`;
touched Lean-file marker scan; and direct axiom probe.  The new theorem
reports `[propext, Classical.choice, Quot.sound]`.

Xhigh read-only scouts separated the next frontier: there is no existing
concrete arbitrary `sourceImageDensity` theorem beyond this unit-density
specialization; the larger non-wrapper target is localized determinant-Haar
endpoint-patch domination for the original-volume/readback layer.

## 2026-07-03 A2 source-density continuity finite-integral wrapper

Reproduction:
`reproduction-a2-source-density-continuity-finite-integral-wrapper.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_passiveLocalSet_matrixEntryReference_open_followingPatch_open_subset_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_sourceDensity_continuousAt_lt_top
```

The theorem composes the finite eventual-density package with the
eventual-density coordinate-source finite-integral handoff.  It hides the
choice of `CJ` and `CS`, requiring instead:

```text
ContinuousAt sourceDensity z0
sourceDensity z0 < top
```

where `sourceDensity z = sourceImageDensity (sourceChart z)`.

Boundary: it does not construct `sourceImageDensity`, prove source-density
continuity/finiteness, or prove determinant-Haar/raw-Haar transport,
original-prior transport, normal crossings, pole order, or RLCT.

Verification passed: focused local build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawImageHandoff`; full
local `lake build DLNFibre`; `lean/scripts/sorries`; `git diff --check`;
touched Lean-file marker scan; and direct axiom probe.  The new theorem
reports `[propext, Classical.choice, Quot.sound]`.

## 2026-07-03 A2 source-density continuity density-bounds package

Reproduction:
`reproduction-a2-source-density-continuity-density-bounds-package.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_finite_eventually_jacobianDensity_sourceDensity_bounds_case2PassiveThetaWithFollowingFactorEndpointSourceChart_of_sourceDensity_continuousAt_lt_top
```

The theorem packages the two finite eventual upper-density inputs expected by
the eventual-density coordinate-source handoff.  The Jacobian side is
discharged by the endpoint determinant-sector Jacobian theorem.  The source
side is a deliberately explicit local boundedness socket:

```text
ContinuousAt sourceDensity z0
sourceDensity z0 < top
```

where `sourceDensity z = sourceImageDensity (sourceChart z)` and
`sourceImageDensity` remains arbitrary.

Boundary: this is only a density-bounds package.  It does not construct a
source-image density, prove source-density continuity/finiteness, compose to
the finite-integral endpoint, or prove determinant-Haar/raw-Haar transport,
original-prior transport, normal crossings, pole order, or RLCT.

Verification passed: focused local build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawImageHandoff`; full
local `lake build DLNFibre`; `lean/scripts/sorries`; `git diff --check`;
touched Lean-file marker scan; and direct axiom probe.  The new theorem
reports `[propext, Classical.choice, Quot.sound]`.

## 2026-07-03 A2 Jacobian eventual upper bound

Reproduction:
`reproduction-a2-jacobian-eventual-upper-bound.md`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
```

Lean now proves generic ENNReal local boundedness helpers:

```text
eventually_le_const_ennreal_of_continuousAt_lt
exists_lt_top_eventually_le_of_continuousAt_lt_top
exists_open_ae_restrict_le_of_continuousAt_lt_top
```

and the with-following endpoint Jacobian specialization:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_finite_eventually_le_jacobianDensity_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
```

The Jacobian theorem composes endpoint-topology-tuple continuity, determinant
sector membership at `z0`, and the retained-passive real local-unit Jacobian
bound.  It chooses `CJ = ENNReal.ofReal K` and lifts the eventual real bound
to `jacobianDensity z <= CJ` by monotonicity of `ENNReal.ofReal`.

Boundary: this closes only the Jacobian-density eventual upper-bound input
for the coordinate-source handoff.  The source-density eventual upper bound
still needs an explicit continuity and finite/base-upper-bound hypothesis for
`sourceImageDensity` composed with the endpoint source chart, or a concrete
source-image density construction.  No determinant-Haar/raw-Haar transport,
original-prior transport, normal crossings, pole order, or RLCT is proved.

Verification passed: focused local builds of
`DLNFibre.DLN.Aoyagi.LocalMeasureHandoff`,
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaJacobianMeasure`, and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawImageHandoff`; full
local `lake build DLNFibre`; `lean/scripts/sorries`; `git diff --check`;
touched-file marker scan; and direct axiom probes.  The four probed
declarations report `[propext, Classical.choice, Quot.sound]`.

## 2026-07-03 A2 eventual upper-density coordinate-source finite integral

Reproduction:
`reproduction-a2-eventual-upper-density-coordinate-source-finite-integral.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_passiveLocalSet_matrixEntryReference_open_followingPatch_open_subset_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_eventually_density_bounds
```

The theorem takes the passive-self open coordinate-source finite-integral
handoff and replaces its two a.e. upper-density continuations by eventual
upper bounds near `z0`:

```text
forall eventually z in nhds z0, jacobianDensity z <= CJ
forall eventually z in nhds z0, sourceDensity z <= CS
```

It shrinks the caller's ambient open set by the two eventual-bound
neighborhoods, calls the passive-self handoff there, and then supplies the
required a.e. bounds on the returned `V` via `ae_restrict_mem`.

Boundary: this proves no continuity theorem for `jacobianDensity` or
`sourceDensity` and no density upper bound by itself.  It also proves no
determinant-Haar/raw-Haar transport, original-prior transport, normal
crossings, pole order, or RLCT.

Verification passed: focused local build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawImageHandoff`; full
local `lake build DLNFibre`; `lean/scripts/sorries`; `git diff --check`;
touched-file marker scan; direct axiom probe; and independent xhigh audit.
The new declaration reports `[propext, Classical.choice, Quot.sound]`.

## 2026-07-03 A2 passive-self open coordinate-source finite integral

Reproduction:
`reproduction-a2-passive-self-open-coordinate-source-finite-integral.md`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

Lean now proves:

```text
isOpen_case2PassiveThetaWithFollowingFactor_passiveFieldCylinder
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_passiveLocalSet_matrixEntryReference_open_followingPatch_open_subset_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_density_bounds
```

The topology lemma says the cylinder over an open passive-field patch is open
in the enlarged with-following source.  The composed handoff uses the
passive-field coordinate-reference self-restriction theorem to construct the
passive local set internally, intersects the ambient open source set with its
passive cylinder, and then calls the already proved supplied-passive
open-following-patch coordinate-source finite-integral wrapper.

The returned data include the open passive local set, the self-restricted
passive measure, the open following patch, and an open source set `V` with
`V subset G`, `V subset {z | z.1.1 in passiveLocalSet}`, and
`V subset {z | z.2 in followingPatch}`.  The passive comparison is now the
coordinate-reference self-domination

```text
passiveRef.restrict passiveLocalSet <= 1 • passiveMeasure.
```

Boundary: this still proves no Jacobian-density upper bound, no
source-density upper bound, no determinant-Haar/raw-Haar transport, no
original-prior transport, no normal crossings, pole order, or RLCT.

Verification passed: focused local build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawImageHandoff`; full
local `lake build DLNFibre`; `lean/scripts/sorries`; `git diff --check`;
touched-file marker scan; direct axiom probes; and independent xhigh audit.
The two new declarations report `[propext, Classical.choice, Quot.sound]`.

## 2026-07-03 A2 passive-field local reference self-restriction

Reproduction:
`reproduction-a2-passive-field-local-reference-self-restriction.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaEndpointReference.lean
```

Lean now proves:

```text
piMatrixEntryBox
case2PassiveThetaPassiveFieldBox
case2PassiveThetaPassiveFieldReferenceMeasure_box_lt_top
exists_open_passiveLocalSet_case2PassiveThetaPassiveFieldReferenceMeasure_restrict_self_le_smul
```

The theorem constructs a radius-1 entrywise coordinate product box around any
passive-field point, restricts the passive coordinate reference measure to
that box, and sets `Cpassive = 1`.  The resulting local set is open,
measurable, contains the base point, has finite restricted mass, and satisfies
the self-domination

```text
passiveRef.restrict passiveLocalSet <= Cpassive • passiveMeasure.
```

Boundary: this is only a coordinate-reference self-restriction.  It proves no
original-prior comparison, determinant-Haar/raw-Haar transport,
Jacobian-density upper bound, source-density upper bound, normal crossings,
pole order, or RLCT.

Verification passed: focused local build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaEndpointReference`; full
local `lake build DLNFibre`; `lean/scripts/sorries`; `git diff --check`;
touched-file marker scan; and direct axiom probes.  The two probed
declarations report `[propext, Classical.choice, Quot.sound]`.

## 2026-07-03 A2 fixed-following-patch coordinate-source finite integral

Reproduction:
`reproduction-a2-fixed-following-patch-coordinate-source-finite-integral.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

Lean now proves:

```text
case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_restrict_of_followingPatch_passive_restrict_le_smul_and_density_bounds
exists_matrixEntryReference_open_followingPatch_open_subset_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_passive_restrict_le_smul_and_density_bounds
```

The first theorem is the supplied-patch coordinate-source finite-integral
handoff: it consumes a fixed following patch with finite matrix-entry measure,
unit determinant on the patch, and a uniform inverse-square-sum bound.  The
second theorem constructs an open following patch first, shrinks the
with-following source-chart neighborhood inside the same patch cylinder, and
then calls the supplied-patch handoff.

The source-domain opens-measurable, Borel, and Polish hypotheses in the open
wrapper are explicit hypotheses for the canonical source-domain measurable
structure.  They are not fresh arbitrary measurable-space binders, so the
concrete reference-source measure remains on its canonical product measurable
space.

Boundary: still no passive local comparison measure construction, no passive
local-set existence theorem, no Jacobian-density upper bound, no source-density
upper bound, no determinant-Haar/raw-Haar transport, no original-prior
transport, no normal crossings, pole order, or RLCT.

Verification passed: focused local build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawImageHandoff`; full
local `lake build DLNFibre`; `lean/scripts/sorries`; `git diff --check`;
touched-file marker scan; and direct axiom probes.  The two new declarations
report `[propext, Classical.choice, Quot.sound]`.

## 2026-07-03 A2 open coordinate-source finite-integral handoff

Reproduction:
`reproduction-a2-open-coordinate-source-finite-integral-from-cylinder-domination.md`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

Lean now proves:

```text
exists_matrixEntryReference_open_followingPatch_case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_of_measure_le_smul_restrict_sourceCylinder_restrict_of_base_reindexed_det_isUnit
exists_matrixEntryReference_open_followingPatch_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_passive_restrict_le_smul_and_density_bounds
exists_open_subset_continuousOn_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_readback_leftInverse_subset_followingPatchCylinder
```

The first theorem preserves `IsOpen followingPatch` through the endpoint
finite-source/dominated-target package.  The second theorem preserves that
open witness through the concrete coordinate-source finite-integral wrapper.
The third theorem shrinks a with-following source-chart neighborhood inside
the open following-patch cylinder, returning both `V subset G` and
`V subset {z | z.2 in followingPatch}`.

Boundary: this proves no passive local comparison measure construction, no
passive-cylinder shrinking, no Jacobian-density upper bound, no source-density
upper bound, no determinant-Haar/raw-Haar transport, no original-prior
transport, no normal crossings, pole order, or RLCT.

Focused local builds of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference`
and `DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawImageHandoff`
passed, as did full local `lake build DLNFibre`, `lean/scripts/sorries`,
`git diff --check`, touched-file marker scan, and direct axiom probes.  The
three new declarations report `[propext, Classical.choice, Quot.sound]`.

Explorer notes: `Dalton the 3rd` confirmed the source-chart shrink shape;
`Hegel the 3rd` identified finite passive local restrict-self comparison as
the passive frontier; `Aristotle the 3rd` identified the missing determinant
sector and continuity/finite-value hypotheses for density upper bounds.

## 2026-07-03 A2 coordinate-source finite integral from cylinder domination

Reproduction:
`reproduction-a2-coordinate-source-finite-integral-from-cylinder-domination.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

Lean now proves:

```text
exists_matrixEntryReference_followingPatch_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_passive_restrict_le_smul_and_density_bounds
```

The theorem composes three existing sockets after the finite-source theorem
returns its following patch:

```text
referenceSource.restrict V <= Cpassive • localSourceMeasure
coordinateSourceMeasure.restrict V
  <= (CS * (CJ * Cpassive)) • localSourceMeasure
target domination -> p.13 positivity and finite negative-power integral
```

The following-patch containment is a continuation:

```text
V subset {z | z.2 in followingPatch} ->
  finite-integral result for coordinateSourceMeasure.restrict V.
```

That avoids overclaiming: a later source-chart shrinking theorem should
discharge the containment after the patch has been constructed.

Boundary: this proves no passive local comparison measure construction, no
passive support theorem, no Jacobian-density upper bound, no source-density
upper bound, no determinant-Haar/raw-Haar transport, no original-prior
transport, no normal crossings, pole order, or RLCT.

Focused local build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawImageHandoff`, full
local `lake build DLNFibre`, `lean/scripts/sorries`, `git diff --check`,
touched-file marker scan, and direct axiom probe passed.  The new declaration
reports `[propext, Classical.choice, Quot.sound]`.

## 2026-07-03 A2 reference-source finite-cylinder base domination

Reproduction:
`reproduction-a2-reference-source-finite-cylinder-base-domination.md`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

Lean now proves:

```text
prod_prod_restrict_le_smul_restrict_cylinder_of_left_restrict_le_smul_of_subset
case2PassiveThetaWithFollowingFactor_referenceSource_restrict_le_smul_sourceCylinder_restrict_of_passive_restrict_le_smul
```

The generic lemma lifts a left-factor local domination through a two-level
product and then restricts to a set `V` supported in both the left-factor
patch and a right-factor cylinder.  The concrete wrapper applies this to

```text
referenceSource = (passiveRef.prod weightedBox).prod followingMeasure
```

and proves:

```text
referenceSource.restrict V <= Cpassive • localFiniteCylinder
```

where `localFiniteCylinder` is the finite following-patch source cylinder
restricted to `V`.

This is the missing base-domination input for the concrete two-density
coordinate-source handoff.  The next wrapper should be thin: after the
following patch and local source measure are in scope, combine this theorem
with the Jacobian/source-density upper bounds to dominate
`coordinateSourceMeasure.restrict V`, then feed that domination into the
existing dominated-target finite-integral theorem.

Implementation note: the endpoint-reference chain now uses the canonical
passive-field product measurable space.  Removing the arbitrary
`[MeasurableSpace PassiveFields]` binders avoids a typeclass split between
`passiveMeasure` and the concrete named reference measures.

Boundary: this is only product-measure restriction bookkeeping.  It proves no
passive local finite measure construction, no passive support theorem, no
Jacobian-density upper bound, no source-density upper bound, no coordinate
source finite-integral theorem by itself, no determinant-Haar/raw-Haar
transport, no original-prior transport, no normal crossings, pole order, or
RLCT.

Focused local builds of `DLNFibre.DLN.Aoyagi.LocalMeasureHandoff` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference`,
full local `lake build DLNFibre`, `lean/scripts/sorries`, `git diff --check`,
touched-file marker scan, and direct axiom probes passed.  The new
declarations report `[propext, Classical.choice, Quot.sound]`.

## 2026-07-03 A2 concrete coordinate-source two-density handoff

Reproduction:
`reproduction-a2-concrete-coordinate-source-two-density-handoff.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

Lean now proves:

```text
case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_restrict_le_smul_of_referenceSource_restrict_le_smul
case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_restrict_le_smul_of_referenceSource_restrict_le_smul_of_lt_top
```

These are the concrete with-following wrappers around the generic
two-density handoff.  They unfold the named Aoyagi source stack

```text
referenceSource -> baseJ -> coordinateSourceMeasure
```

and prove that base domination plus local upper bounds on the Jacobian density
and source-image density imply

```text
coordinateSourceMeasure.restrict V
  <= (CS * (CJ * Cbase)) • nu.
```

The comparison measure `nu` stays abstract so later work can instantiate it
with the finite following-patch cylinder after proving the separate
product-cylinder/passive-local base domination.

Boundary: this proves no passive local domination, no finite-cylinder
domination for `referenceSource.restrict V`, no Jacobian-density upper bound,
no source-density upper bound, no determinant-Haar/raw-Haar transport, no
original-prior transport, no normal crossings, pole order, or RLCT.

Focused local build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawImageHandoff`, full
local `lake build DLNFibre`, `scripts/sorries`, `git diff --check`, touched
Lean-file marker scan, and direct axiom probes passed.  The new declarations
report `[propext, Classical.choice, Quot.sound]`.

## 2026-07-03 A2 two-density domination handoff

Reproduction:
`reproduction-a2-two-density-domination-handoff.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
```

Lean now proves:

```text
restrict_two_withDensity_le_smul_of_restrict_le_smul_of_ae_le
restrict_two_withDensity_le_smul_of_restrict_le_smul_of_ae_le_of_lt_top
```

The theorem composes the existing one-density bounded-density adapter twice.
Given base domination `mu.restrict V <= Cbase • nu`, a first density bound
`J <= CJ` a.e. against `mu.restrict V`, and a second density bound `S <= CS`
a.e. against `(mu.withDensity J).restrict V`, it proves

```text
((mu.withDensity J).withDensity S).restrict V
  <= (CS * (CJ * Cbase)) • nu.
```

The finite wrapper also proves the final scalar is finite from finite
`Cbase`, `CJ`, and `CS`.

Boundary: this is only the conditional measure-theory handoff.  It proves no
passive local domination, no Jacobian-density upper bound, no source-density
upper bound, no concrete coordinate-source/original-prior domination, no
normal crossings, pole order, or RLCT.

Focused local build of `DLNFibre.DLN.Aoyagi.LocalMeasureHandoff`, full local
`lake build DLNFibre`, `lean/scripts/sorries`, `git diff --check`, touched
Lean-file marker scan, and direct axiom probes passed.  The new declarations
report `[propext, Classical.choice, Quot.sound]`.

## 2026-07-03 A2 open finite following-factor patch

Reproduction:
`reproduction-a2-matrix-entry-following-factor-local-patch.md`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaEndpointReference.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

Lean now strengthens the matrix-entry patch API:

```text
isOpen_matrixEntryBox
exists_matrixEntryReferenceMeasure_finite_open_followingPatch_of_reindexed_det_isUnit
isOpen_case2PassiveThetaWithFollowingFactor_followingPatchCylinder
```

The generic theorem returns a following patch containing the base following
factor, finite for `matrixEntryReferenceMeasure`, open, measurable, determinant
unit on the patch, and with a uniform reindexed inverse square-sum bound.  The
with-following helper proves the cylinder `{z | z.2 ∈ followingPatch}` is open,
so later source-chart arguments can shrink an open neighborhood by intersecting
with that cylinder.

Boundary: this is only a topology/localization strengthening of the existing
finite patch.  It proves no positive patch mass, concrete coordinate-source or
original-prior domination, determinant-Haar/raw-Haar transport, normal
crossings, pole order, or RLCT.  The determinant hypothesis remains separate on
the independent following factor.

Focused local build passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference`;
full local `lake build DLNFibre` passed as well.
`lean/scripts/sorries`, `git diff --check`, touched Lean-file marker scan, and
direct axiom probes passed.  The new declarations report
`[propext, Classical.choice, Quot.sound]`.

## 2026-07-03 A2 dominated target product-residual handoff

Reproduction:
`reproduction-a2-dominated-target-product-residual-handoff.md`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

Lean now proves the generic handoff:

```text
ae_and_lintegral_lt_top_of_measure_le_smul
```

and the Case 2 with-following endpoint wrapper:

```text
exists_matrixEntryReference_followingPatch_case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_of_measure_le_smul_restrict_sourceCylinder_restrict_of_base_reindexed_det_isUnit
```

The generic handoff packages the two existing facts:
`ae_of_measure_le_smul` and `lintegral_lt_top_of_measure_le_smul`.  The Case 2
wrapper keeps the local finite following-patch source theorem as the base
result and adds the conditional target conclusion

```text
forall targetMeasure C,
  targetMeasure <= C • localSourceMeasure -> C < infinity -> ...
```

for p.13 product-residual a.e. positivity and finite negative-power
integrability over `targetMeasure`.

The target measure, scalar, and domination hypothesis are deliberately
conditional and placed inside the existential package because
`localSourceMeasure` depends on the constructed `followingPatch`.  This proves
no domination for the coordinate source measure, Jacobian-weighted source
measure, original volume, or original prior.  Those remain separate
source-density/Jacobian/readback tasks.

Focused local builds passed for `DLNFibre.DLN.Aoyagi.LocalMeasureHandoff` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference`.

## 2026-07-03 A2 finite-passive source-cylinder local restriction

Reproduction:
`reproduction-a2-finite-passive-source-following-patch-local-restriction.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

Lean now proves:

```text
exists_matrixEntryReference_followingPatch_case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_restrict_sourceCylinder_restrict_of_base_reindexed_det_isUnit
```

This theorem takes an arbitrary local set `V` and localizes the previous
finite-passive following-patch cylinder source theorem to
`sourceMeasure.restrict V`.  The proof is pure measure monotonicity:
`ae_restrict_of_ae` carries a.e. positivity to the restriction, and
`lintegral_mono' Measure.restrict_le_self` carries finite negative-power
integrability.

Xhigh scouts `Bohr the 3rd` and `Cicero the 3rd` agreed on the boundary.  The
source-chart/readback theorems already return open `V` and mapping identities;
the finite-integral theorem should not bundle them.  Downstream code should
apply the source-chart theorem separately, then feed its open `V` to this
arbitrary-local-set wrapper.

Boundary: this local-restriction theorem itself does not require the following
patch to be open, although a later open-patch strengthening now exists for the
matrix-entry construction.  The determinant hypothesis on `z₀.2` remains
separate from the passive determinant sector.  Finite passive mass remains
explicit.  This proves no positive patch mass,
Haar/source-density/original-prior transport, normal crossings, pole order, or
RLCT.

Focused local build, full local `lake build DLNFibre`, `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker scan, direct axiom
probe, and xhigh review by `Volta the 3rd` passed.  The new declaration
reports `[propext, Classical.choice, Quot.sound]`.

## 2026-07-02 A2 finite-passive source-cylinder following patch

Reproduction:
`reproduction-a2-finite-passive-source-following-patch-integrability.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

Lean now proves:

```text
case2PassiveThetaWithFollowingFactor_productSourceMeasure_restrict_followingPatch_eq_prod_restrict
exists_matrixEntryReference_followingPatch_case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_restrict_sourceCylinder_of_base_reindexed_det_isUnit
```

The first theorem is the product-measure bookkeeping for a following-patch
cylinder:

```text
((passiveMeasure.prod weightedBox).prod followingRef)
  .restrict {z | z.2 ∈ followingPatch}
= (passiveMeasure.prod weightedBox).prod (followingRef.restrict followingPatch).
```

The second theorem is the source-point wrapper around the matrix-entry
following patch.  It takes a full source point `z₀` and the separate following
determinant hypothesis

```text
IsUnit ((z₀.2.submatrix id eNext.symm).det)
```

then returns a measurable finite following patch containing `z₀.2`, with
determinant-unit and uniform inverse-square-sum bounds, and proves p.13
product-residual a.e. positivity and finite negative-power integrability over
the finite-passive product source restricted to the cylinder `{z | z.2 ∈
followingPatch}`.

Boundary: this intentionally keeps `passiveMeasure Set.univ < ∞`; the global
passive-field coordinate reference measure is not known finite.  It does not
derive the following determinant condition from
`case2PassiveThetaWithFollowingFactorDetSector`, and proves no open
source-chart neighborhood, positive patch mass, Haar/source-density/original
prior transport, normal crossings, pole order, or RLCT.

Focused local build, full local `lake build DLNFibre`, `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker scan, direct axiom
probe, and xhigh review by `Pasteur the 3rd` passed.  The two new declarations
report `[propext, Classical.choice, Quot.sound]`.

## 2026-07-02 A2 matrix-entry following-factor local patch

Reproduction:
`reproduction-a2-matrix-entry-following-factor-local-patch.md`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaEndpointReference.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

Lean now proves the matrix-entry coordinate box helpers:

```text
matrixEntryBox
mem_matrixEntryBox_self
measurableSet_matrixEntryBox
matrixEntryReferenceMeasure_matrixEntryBox_lt_top
```

and the local following-factor patch theorem:

```text
exists_matrixEntryReferenceMeasure_finite_followingPatch_of_reindexed_det_isUnit
```

Given `e : τ ≃ ι`, a base following factor `F₀ : Matrix ι τ ℝ`, and
`IsUnit ((F₀.submatrix id e.symm).det)`, it produces a patch and `K` with
`0 < K`, `F₀ ∈ patch`, finite `matrixEntryReferenceMeasure` mass, determinant
unit on the patch, and a uniform bound for the reindexed inverse square-sum.
The finite-mass primitive is the entrywise box
`Π_i Π_j (F₀ i j - 1, F₀ i j + 1)`, evaluated by `Measure.pi_pi` and
`Real.volume_Ioo`.

The Case 2 consumer wrapper is:

```text
exists_matrixEntryReference_followingPatch_case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_of_base_reindexed_det_isUnit
```

It specializes the generic patch to
`Matrix (Case2ResidualColIndex n S (J+1)) τ ℝ` and then invokes the
determinant-chart finite patch wrapper to get a.e. positivity and finite
negative-power integrability for the p.13 product residual over the restricted
following-patch source measure.

Focused local build passed:

```text
cd lean && env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference
```

Full verification passed:

```text
cd lean && env LEAN_NUM_THREADS=3 lake build DLNFibre
lean/scripts/sorries
git diff --check
rg -n '\b(sorry|admit|axiom)\b|#exit|native_decide' touched Lean files
```

Direct axiom probe reports `[propext, Classical.choice, Quot.sound]` for the
new finite-box and following-patch declarations.

Xhigh scouts `Fermat the 3rd` and `Descartes the 3rd` confirmed the coordinate
box route and the generic-then-Case-2 theorem order.  Xhigh review by
`Hume the 3rd` found no issues.  Review specifically checked finite box
measure, inverse-square-sum measurability, determinant hypothesis orientation,
intersection membership, and absence of determinant-sector overclaim.

Boundary: this does not prove positive patch mass and does not derive the base
following-factor determinant condition from
`case2PassiveThetaWithFollowingFactorDetSector`; that sector imposes no
condition on the independent following factor.  It also does not prove
source-prior/original-prior transport, normal crossings, pole order, or RLCT.

## 2026-07-02 A2 determinant following-factor patch wrapper

Reproduction:
`reproduction-a2-determinant-following-factor-patch-wrapper.md`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

Lean now proves the generic determinant-chart right-inverse constructor:

```text
exists_rightInverse_squareSum_le_of_reindexed_det_isUnit_inverse_squareSum_le
```

and the Case 2 p.13 finite-integral wrapper:

```text
case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_restrict_followingPatch_of_forall_mem_reindexed_det_isUnit_inverse_squareSum_le
```

The calculation is: set `A(F) = F.submatrix id eNext.symm`, take
`G(F) = A(F)^(-1).submatrix eNext id`, and use
`Matrix.submatrix_mul_equiv` plus `A(F) * A(F)^(-1) = 1` to prove
`F * G(F) = 1`.  The inverse square-sum bound is exactly the requested
right-inverse bound.

Boundary: this is a determinant-chart instantiation of the finite patch
theorem, not a construction of an open finite-measure patch.  It assumes
measurability, finite following mass, unit determinant on the reindexed square
following factor, and a uniform inverse square-sum bound on the patch.  No
source-prior/original-prior transport, normal crossings, pole order, or RLCT is
proved.

Focused local build passed:

```text
cd lean && env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference
```

Full verification passed:

```text
cd lean && env LEAN_NUM_THREADS=3 lake build DLNFibre
lean/scripts/sorries
git diff --check
rg -n '\b(sorry|admit|axiom)\b|#exit|native_decide' touched Lean files
```

Direct axiom probe reports `[propext, Classical.choice, Quot.sound]` for both
new declarations.

Xhigh scouts `Peirce the 3rd` and `Mill the 3rd` mapped the next two
directions.  `Peirce the 3rd` recommends the actual open
`matrixEntryReferenceMeasure` finite patch around a base determinant-unit
factor; `Mill the 3rd` recommends threading the abstract patch theorem into
the with-following source-chart residual-source sockets.

Xhigh reviewer `Meitner the 3rd` found no issues.  Review specifically checked
the reindexing orientation, the right-inverse shape for the `D * F` comparison,
and the nonclaim boundary that this theorem does not construct the patch and is
separate from `case2PassiveThetaWithFollowingFactorDetSector`.

## 2026-07-02 A2 finite following-factor patch wrapper

Reproduction:
`reproduction-a2-finite-following-factor-patch-wrapper.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

Lean now proves:

```text
case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_restrict_followingPatch_of_forall_mem_rightInverse_squareSum_le
```

This is the restricted following-patch wrapper around the previous a.e.
right-inverse theorem.  A measurable patch `followingPatch` with finite
following measure and a pointwise uniform right-inverse bound supplies the
a.e. right-inverse socket after restricting the following factor measure.  The
proof uses `ae_restrict_mem` on the following factor and
`Measure.quasiMeasurePreserving_snd` for the product source.

Boundary: this does not construct an open following-factor patch or prove
right-invertibility/topological inverse bounds near a base factor.  It assumes
the measurable finite patch and the pointwise uniform right-inverse bound.  No
source-prior/original-prior transport, normal crossings, pole order, or RLCT is
proved.

Focused local build passed:

```text
cd lean && env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference
```

Full local `lake build DLNFibre`, `lean/scripts/sorries`, `git diff --check`,
touched Lean-file forbidden-marker scan, direct axiom probe, and xhigh review
by `Dirac the 3rd` passed.  Xhigh API scout `Schrodinger the 3rd` confirmed
the `ae_restrict_mem`/`Measure.quasiMeasurePreserving_snd` route and the need
for a measurable patch.  The new declaration reports
`[propext, Classical.choice, Quot.sound]`.

Post-interruption agent inventory: xhigh scout `Wegener the 3rd` found no
edits needed and identified the next pure wrapper shape: combine the
with-following `C 1` and `C 0` readouts with the generic residual-factor
product theorem to expose the raw RHS as
`case2DisplayedPostPivotResidualBlock ... * z.2`.  Xhigh scout
`Rawls the 3rd` found no edits needed and restated the comparison theorem card:
the correct local hypothesis is full-row-rank/right-invertible following
factor with a uniform inverse bound; if the rank drops, choose nonzero `D` with
`D * F = 0`, so no comparison can hold.

## 2026-07-02 A2 product-residual finite integral under following-factor nondegeneracy

Reproduction:
`reproduction-a2-product-residual-right-inverse-finite-integral.md`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaCFieldReadout.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

Lean now proves the finite reindexing bridge:

```text
Case2PassiveThetaWithFollowingFactor.displayedPostPivotResidualBlock_squareSum_eq_activeReadout_squareSum
```

and the conditional p.13 product-residual finite-integral wrappers:

```text
case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_of_ae_const_mul_activeReadout_le
case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_of_ae_followingFactor_rightInverse_squareSum_le
```

The calculation is the expected one.  If the following factor `F` has a right
inverse `G` with a uniform square-sum bound, then `D = (D * F) * G`, hence
`c * sq(D) <= sq(D * F)` for a single `c > 0`.  Since `t >= 0`, this is the
correct direction for transferring finite integrability from `sq(D)^(-t)` to
`sq(D * F)^(-t)`.

Boundary: the theorem assumes the a.e. right-inverse bound; it does not
construct the following-factor patch, prove openness/nonzero singular-value
control, perform source-prior or original-prior transport, prove normal
crossings, compute pole order, or extract RLCT.

Focused local build passed:

```text
cd lean && env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference
```

Full local `lake build DLNFibre`, `lean/scripts/sorries`, `git diff --check`,
touched Lean-file forbidden-marker scan, direct axiom probe, and xhigh review
by `Darwin the 3rd` passed.  The new declarations report
`[propext, Classical.choice, Quot.sound]`.

## 2026-07-02 A2 following-factor right-inverse product comparison

Reproduction:
`reproduction-a2-following-factor-right-inverse-product-comparison.md`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaCFieldReadout.lean
```

Lean now proves the generic finite-coordinate right-inverse comparison:

```text
const_mul_matrixCoordinateSquareSum_le_mul_right_of_rightInverse_squareSum_le
exists_pos_const_forall_matrixCoordinateSquareSum_le_mul_right_of_mul_eq_one
exists_pos_const_forall_matrixCoordinateSquareSum_le_mul_right_of_forall_exists_rightInverse_squareSum_le
```

and the with-following endpoint product readout/comparison:

```text
Case2PassiveThetaWithFollowingFactor.endpointRetainedData_residualFactorProduct_submatrix_eq_displayedPostPivotResidualBlock_mul_followingFactor
Case2PassiveThetaWithFollowingFactor.exists_pos_const_activeResidualSquareSum_le_endpointRetainedData_residualFactorProduct_of_followingFactor_mul_eq_one
```

The calculation is elementary: if the following factor `F` has a right inverse
`G`, then `D = (D * F) * G`.  The existing Frobenius-style product estimate
`sq(A * B) <= sq(A) * sq(B)` gives `sq(D) <= sq(D * F) * sq(G)`, hence a
positive constant `c` with `c * sq(D) <= sq(D * F)`.

Boundary: this is still pointwise algebra.  It does not construct a local
following-factor patch, prove a uniform inverse bound on the actual reference
measure, transfer negative-power integrability, identify a source-prior image,
prove normal crossings, pole order, or RLCT.  The next p.13-facing measure
target should combine this comparison with
`lintegral_ofReal_rpow_neg_lt_top_of_ae_pos_of_ae_const_mul_le` and the
active-readout finite-integral theorem, under a local finite following-factor
patch with an a.e. right inverse bound.

Focused local builds passed:

```text
cd lean && env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
cd lean && env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaCFieldReadout
```

## 2026-07-02 A2 with-following active-readout finite integral and p.13 frontier

Reproduction/frontier note:
`reproduction-a2-with-following-finite-local-source-residual-integrability-frontier.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

Lean now proves:

```text
case2PassiveThetaWithFollowingFactor_activeReadout_pos_ae_and_lintegral_rpow_neg_prod_finiteMass
```

This is the finite-side-mass integrability theorem for the active
selected-entry `C 1` readout of the enlarged with-following source
coordinates.  It works over
`(passiveMeasure.prod weightedBox).prod followingMeasure` and scales the
selected-entry chart-image integral by the passive and following total masses.

Boundary: the p.13 residual-coordinate map is still the full two-edge
residual product `C 1 * C 0`, not this active `C 1` readout.  Finite following
mass alone is not a p.13 residual-product bridge.  The next p.13-facing target
needs either a local nondegeneracy/comparison for `D(y) * F` or a direct
product-integrability theorem for the actual following-factor local measure.

Focused local build passed:

```text
cd lean && env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference
```

## 2026-07-02 A2 with-following localized source-density raw domination

Reproduction:
`reproduction-a2-with-following-localized-source-density-raw-domination.md`.
Statement card:
`statement-card-a2-with-following-localized-source-density-raw-domination.md`.
Review:
`review-a2-with-following-localized-source-density-raw-domination.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

Lean now proves localized source-density lower wrappers:

```text
exists_open_subset_rawHaar_restrict_patch_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_endpointPatch_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
exists_open_subset_rawHaar_restrict_patch_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_endpointPatch_restrict_le_smul_endpointTopologyTuple_eventually_sourceDensity_lower
```

They replace the old global target `rawHaar.restrict rawSourceSet` by
`rawHaar.restrict P` for any raw-order patch `P subset rawSourceSet`, provided
the corresponding endpoint patch is dominated and the same source-density
lower bound is available.

Boundary: endpoint-patch domination and source-density lower bounds remain
explicit hypotheses.  No endpoint-Haar transport, exact raw-Haar pushforward,
source-prior/original-prior transport, coverage, normal crossings, pole order,
or RLCT is proved.

Focused local build, full local `lake build DLNFibre`, no-sorry audit,
whitespace check, touched-file marker scan, direct axiom probes, and xhigh
review passed.  Both declarations report
`[propext, Classical.choice, Quot.sound]`.

## 2026-07-02 A2 with-following inverse-Haar original-volume readback density socket

Reproduction:
`reproduction-a2-with-following-original-volume-invhaar-readback-density-socket.md`.
Statement card:
`statement-card-a2-with-following-original-volume-invhaar-readback-density-socket.md`.
Review:
`review-a2-with-following-original-volume-invhaar-readback-density-socket.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadback.lean
```

Lean now proves:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_and_readback_le_smul_sourceReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
```

This consumes the exact with-following source-image inverse-Haar bridge and
the generic original-volume `withDensity` readback socket.  Under the supplied
exact raw-pushforward identity, every measurable chart piece contained in the
returned local source image gets both the exact restricted-volume identity

```text
originalVolume.restrict chartPiece =
  (sourceRef.withDensity (fun _ => ((c^-1 : NNReal) : ENNReal))).restrict chartPiece
```

and the readback domination

```text
Measure.map readback (originalVolume.restrict chartPiece)
  <= ((c^-1 : NNReal) : ENNReal) • thetaReference.restrict G.
```

Boundary: exact raw-pushforward remains a hypothesis.  No determinant-Haar
transport, raw-Haar transport, source-prior/original-prior transport,
source-image coverage beyond the local chart, source-rank coverage, normal
crossings, pole order, or RLCT is proved.

Focused local module build, full local `lake build DLNFibre`, no-sorry audit,
whitespace check, touched-file marker scan, direct axiom probe, and xhigh
review passed.  The declaration reports
`[propext, Classical.choice, Quot.sound]`.

```text
cd lean && env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeReadback
cd lean && env LEAN_NUM_THREADS=3 lake build DLNFibre
```

## 2026-07-02 A2 with-following original-volume readback from reverse raw-source domination

Reproduction:
`reproduction-a2-with-following-original-volume-readback-reverse-raw-source-domination.md`.
Statement card:
`statement-card-a2-with-following-original-volume-readback-reverse-raw-source-domination.md`.
Review:
`review-a2-with-following-original-volume-readback-reverse-raw-source-domination.md`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaFormalProductSourceReference.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeBridge.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadback.lean
```

Lean now proves:

```text
exists_open_subset_formalProductMeasure_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_restrict_rawSource_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
```

These are the with-following analogues of the existing non-following
reverse-raw-source original-volume/readback bridges.  They consume a supplied
finite domination

```text
rawHaar.restrict rawSourceSet <=
  D • Measure.map rawMap (thetaReference.restrict V)
```

and transport it through the p.13 source chart to dominate restricted original
edge-family volume, then through the local readback to dominate the readback
pushforward by `((cHaar^-1) * D) • thetaReference.restrict G`.

Boundary: reverse raw-source domination remains a hypothesis.  This is a
consumer of the with-following reverse raw-source theorem, not determinant-Haar
transport or source-density positivity.  It does not prove exact raw-Haar
pushforward, source-prior/original-prior transport without the reverse
domination input, p.13 coverage/equality, source-rank coverage, normal
crossings, pole order, or RLCT.

Focused local module builds, full local `lake build DLNFibre`, no-sorry audit,
whitespace check, touched-file marker scan, direct axiom probes, and xhigh
review passed.  The three declarations report
`[propext, Classical.choice, Quot.sound]`.

## 2026-07-02 A2 with-following eventual source-density raw domination

Reproduction:
`reproduction-a2-with-following-eventual-source-density-raw-domination.md`.
Statement card:
`statement-card-a2-with-following-eventual-source-density-raw-domination.md`.
Review:
`review-a2-with-following-eventual-source-density-raw-domination.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

Lean now proves:

```text
exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple_eventually_sourceDensity_lower
```

This wraps the concrete with-following reference-source reverse raw-domination
theorem by replacing its a.e. source-density lower-bound input with an
eventual pullback lower bound near the base point.  The proof extracts an open
lower-bound neighborhood `H`, applies the previous theorem inside `G inter H`,
then uses `V subset H` and `ae_restrict_mem` to prove the a.e. lower bound on
the returned shrink.

Boundary: determinant-chart reverse domination and the eventual lower bound on
`sourceDensity` remain hypotheses.  No continuity, positivity, or concrete
identification of `sourceImageDensity` is proved.  No determinant-Haar
transport/equality, exact raw-Haar pushforward, source-prior/original-prior
transport, p.13 coverage/equality, source-rank coverage, normal crossings,
pole order, or RLCT is proved.

Focused local module build, full local `lake build DLNFibre`, no-sorry audit,
whitespace check, touched-file marker scan, direct axiom probe, and xhigh
review passed.  The theorem reports `[propext, Classical.choice, Quot.sound]`.

## 2026-07-02 A2 with-following reference-source reverse raw domination

Reproduction:
`reproduction-a2-with-following-reference-source-reverse-raw-domination.md`.
Statement card:
`statement-card-a2-with-following-reference-source-reverse-raw-domination.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

Lean now proves:

```text
exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
```

This specializes the existing with-following reverse determinant/raw-order
transport theorem to the concrete enlarged reference source
`case2PassiveThetaWithFollowingFactorReferenceSourceMeasure`, then applies the
lower-density adapter to pass from `baseJ` to
`coordinateSourceMeasure = baseJ.withDensity sourceDensity`.

Boundary: determinant-chart reverse domination and the lower bound on
`sourceDensity` remain hypotheses.  No determinant-Haar transport/equality,
exact raw-Haar pushforward, source-prior/original-prior transport, p.13
coverage/equality, source-rank coverage, normal crossings, pole order, or RLCT
is proved.

Focused local module build, full local `lake build DLNFibre`, no-sorry audit,
whitespace check, touched-file marker scan, direct axiom probe, and xhigh
review passed.  The theorem reports `[propext, Classical.choice, Quot.sound]`.

## 2026-07-02 A2 with-following determinant/raw-order transport

Reproductions:

```text
reproduction-a2-with-following-forward-det-to-raw-domination.md
reproduction-a2-with-following-reverse-det-to-raw-domination.md
```

Statement card:
`statement-card-a2-with-following-determinant-raw-order-transport.md`.

Review:
`review-a2-with-following-determinant-raw-order-transport.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

Lean now proves:

```text
exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_baseJ_restrict_le_smul_rawHaar_restrict_rawSource_of_endpointTopologyTuple_restrict_le_smul_detHaar
exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_baseJ_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple
```

These are the with-following analogues of the existing non-following
determinant-to-raw-order transport theorems.  On the local determinant/pivot
shrink, they compose the endpoint topology-tuple map `Y`, the raw-order map
`Phi`, the formal retained-passive determinant density, and the raw-order COV
identity.  The forward theorem transports endpoint-image domination by
determinant Haar to raw-order domination by raw Haar.  The reverse theorem
transports determinant Haar domination by the endpoint image to reverse
raw-source domination by the Jacobian-weighted raw-order source image.

Boundary: determinant-chart domination is still a hypothesis in each theorem.
The source measure is arbitrary on the enlarged with-following theta domain.
No source-prior/original-prior transport, exact raw-Haar pushforward,
determinant-Haar source production, p.13 coverage/equality, source-rank
coverage, normal crossings, pole order, or RLCT is proved.

Focused module build, full local `lake build DLNFibre`, no-sorry audit,
whitespace check, touched-file marker scan, direct axiom probes, and xhigh
review passed.  The two declarations report
`[propext, Classical.choice, Quot.sound]`.

## 2026-07-02 A2 with-following source-image p.13 discharge

Reproductions:

```text
reproduction-a2-with-following-source-chart-p13-support.md
reproduction-a2-with-following-original-volume-domination-source-image-p13-discharge.md
reproduction-a2-with-following-original-volume-readback-source-image-p13-discharge.md
```

Statement cards:

```text
statement-card-a2-with-following-source-chart-p13-support.md
statement-card-a2-with-following-original-volume-domination-source-image-p13-discharge.md
statement-card-a2-with-following-original-volume-readback-source-image-p13-discharge.md
```

Review:

```text
review-a2-with-following-source-image-p13-discharge.md
```

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeBridge.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadback.lean
```

Lean now proves:

```text
exists_open_subset_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_subset_p13SourceEdgeFamilySet
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource_of_chartPiece_subset_sourceImage
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource_of_chartPiece_subset_sourceImage
```

This batch proves local one-way p.13 support for the actual with-following
source-chart image, then uses it to discharge the explicit
`chartPiece subset p13SourceSet` input from the original-volume domination and
readback domination wrappers whenever `chartPiece subset sourceChart '' V` is
already available.

Boundary: raw-pushforward equality, chart-piece measurability, and actual
source-image containment remain hypotheses.  No raw Haar transport,
determinant-chart Haar transport, p.13 coverage/equality,
source-prior/original-prior transport, density lower-bound removal, normal
crossings, pole order, or RLCT is proved.

Focused module builds, full local `lake build DLNFibre`, no-sorry audit,
whitespace check, touched-file marker scan, and direct axiom probes passed.
The three declarations report `[propext, Classical.choice, Quot.sound]`.
Xhigh reviewer `Avicenna the 2nd` passed with no findings.

## 2026-07-02 A2 with-following original-volume readback domination

Reproduction:
`reproduction-a2-with-following-original-volume-readback-domination.md`.
Statement card:
`statement-card-a2-with-following-original-volume-readback-domination.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadback.lean
```

Lean now proves:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
```

This composes the with-following source-chart readback package, the
with-following original-volume/source-reference domination theorem, and the
generic readback domination handoff.  Under the supplied raw-pushforward
equality, any measurable p.13 chart piece contained in the actual
with-following source-chart image has a.e.-measurable readback and readback
pushforward dominated by `thetaReference.restrict G` with scalar
`((cHaar^-1 : NNReal) : ENNReal) * 1`.

Boundary: raw-pushforward equality, chart-piece measurability,
`chartPiece subset sourceChart '' V`, and `chartPiece subset p13SourceSet`
remain hypotheses.  No raw Haar transport, determinant-chart Haar transport,
p.13 source-image coverage, source-prior/original-prior transport, density
lower-bound removal, normal crossings, pole order, or RLCT is proved.

Focused elaboration, focused module build, full local `lake build DLNFibre`,
no-sorry audit, whitespace check, touched-file marker scan, and direct axiom
probe passed.  The theorem reports `[propext, Classical.choice, Quot.sound]`.
Xhigh reviewer `Laplace the 2nd` passed after the reproduction wording was
sharpened to say image measurability is re-established on the smaller open
set.

## 2026-07-02 A2 with-following original-volume domination

Reproduction:
`reproduction-a2-with-following-contract-original-volume-domination.md`.
Statement card:
`statement-card-a2-with-following-original-volume-domination.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeBridge.lean
```

Lean now proves:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
```

This composes the with-following constant-density
formal-product/source-reference handoff with the p.13 bounded-density
original-volume bridge.  Under the supplied raw-pushforward equality, any
measurable p.13 chart piece contained in the actual with-following source-chart
image has original edge-family volume dominated by the enlarged source-image
reference with scalar `((cHaar^-1 : NNReal) : ENNReal) * 1`.

Boundary: raw-pushforward equality, chart-piece measurability,
`chartPiece subset sourceChart '' V`, and `chartPiece subset p13SourceSet`
remain hypotheses.  No raw Haar transport, determinant-chart Haar transport,
source-image coverage, source-prior transport, density lower-bound removal,
normal crossings, pole order, or RLCT is proved.

Focused elaboration, focused module build, full local `lake build DLNFibre`,
no-sorry audit, whitespace check, targeted marker scan, and direct axiom probe
passed.  The theorem reports `[propext, Classical.choice, Quot.sound]`.

## 2026-07-02 A2 with-following source-density composition and contract constructor

Reproduction:
`reproduction-a2-with-following-source-density-composition-and-contract.md`.
Statement card:
`statement-card-a2-with-following-source-density-composition-and-contract.md`.
Review:
`review-a2-with-following-source-density-composition-and-contract.md`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaFormalProductSourceImageContract.lean
```

Lean now proves:

```text
aemeasurable_case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity_unweightedSource
case2PassiveThetaWithFollowingFactorReferenceSourceMeasure_withDensity_eq_unweighted_withDensity_selectedEntrySourceDensity_mul
case2PassiveThetaWithFollowingFactorReferenceSourceMeasure_withDensity_restrict_eq_unweighted_withDensity_selectedEntrySourceDensity_mul_restrict
exists_open_subset_a2FormalProductSourceImagePieceContract_case2PassiveThetaWithFollowingFactorEndpointSourceChart_of_rawMap_eq_restrict_rawSource
```

This rung flattens selected-entry source density composed with an additional
source density, and packages the existing raw-pushforward-to-source-reference
handoff into the A2 bounded-density contract with constant density and bound
`1`.

Boundary: raw-pushforward equality, chart-piece measurability, local source
image membership, and p.13 source-set membership remain hypotheses.  No raw
Haar transport, determinant-chart Haar transport, source-image coverage,
source-prior transport, density lower-bound removal, normal crossings, pole
order, or RLCT is proved.

Focused elaboration, focused module builds, full local `lake build DLNFibre`,
no-sorry audit, whitespace check, direct axiom probe, and xhigh review passed.
The four new declarations report `[propext, Classical.choice, Quot.sound]`.

## 2026-07-02 A2 with-following endpoint selected-entry source density

Reproduction:
`reproduction-a2-case2-with-following-endpoint-selected-entry-source-density.md`.
Statement card:
`statement-card-a2-case2-with-following-endpoint-selected-entry-source-density.md`.
Review:
`review-a2-case2-with-following-endpoint-selected-entry-source-density.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

Lean now defines and proves:

```text
case2PassiveThetaWithFollowingFactorUnweightedSourceMeasure
case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity
case2PassiveThetaWithFollowingFactorReferenceSourceMeasure_eq_unweighted_withDensity_selectedEntrySourceDensity
measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_unweighted_withDensity_selectedEntrySourceDensity_restrict_eq_endpointReferenceImageMeasure
```

The result records the source-side selected-entry change-of-variables
convention for the enlarged endpoint reference image: the existing reference
source is the unweighted passive/center/following coordinate-product source
with exactly the selected-entry source density on `yNext`, and its endpoint
pushforward is the named endpoint reference image.

Boundary: actual endpoint image/source-density convention only.  No
determinant-chart Haar equality, no bare target-Haar `Y` COV theorem, no
retained-passive raw-order determinant factor, no raw-Haar transport,
source-prior transport, source-image coverage, formal-product domination,
normal crossings, pole order, or RLCT is proved.

Focused elaboration, focused module build, full local `lake build DLNFibre`,
no-sorry audit, whitespace check, touched-file marker scan, direct axiom
probe, and xhigh review passed.  The four new declarations report
`[propext, Classical.choice, Quot.sound]`.

## 2026-07-02 A2 with-following raw-order reference image same-shrink package

Reproduction:
`reproduction-a2-case2-with-following-raw-order-reference-image-same-shrink.md`.
Statement card:
`statement-card-a2-case2-with-following-raw-order-reference-image-same-shrink.md`.
Review:
`review-a2-case2-with-following-raw-order-reference-image-same-shrink.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawOrderReference.lean
```

Lean now defines and proves:

```text
case2PassiveThetaWithFollowingFactorRawOrderReferenceImageMeasure
exists_open_subset_case2PassiveThetaWithFollowingFactorRawOrderReferenceImage_same_shrink_package
```

The definition names the actual raw-order image of the enlarged reference
source:

```text
Measure.map rawMap (referenceSource.restrict Ω).
```

The same-shrink theorem uses the existing with-following raw-order/source-chart
bridge and packages, on one local open `V`, support on the raw-order
source-recursive determinant chart, domination for arbitrary source measures
dominated by the full enlarged reference source, endpoint-image-to-raw-image
composition, source-chart composition, and raw-density transport.

Boundary: actual image-measure bookkeeping only.  No raw-Haar theorem,
determinant-chart Haar equality, Jacobian determinant formula, local
change-of-variables theorem, source-prior transport, source-image coverage,
formal-product domination, normal crossings, pole order, or RLCT is proved.

Focused elaboration, focused module build, full local `lake build DLNFibre`,
no-sorry audit, whitespace check, touched-file marker scan, direct axiom
probe, and xhigh review passed.  The new definition and theorem probes report
`[propext, Classical.choice, Quot.sound]`.

## 2026-07-02 A2 formal-product/source-image theta-side density constructor

Reproduction:
`reproduction-a2-formal-product-source-image-theta-side-density-constructor.md`.
Statement card:
`statement-card-a2-formal-product-source-image-theta-side-density-constructor.md`.
Review:
`review-a2-formal-product-source-image-theta-side-density-constructor.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaFormalProductSourceImageContract.lean
```

Lean now proves:

```text
A2Case2FormalProductSourceImagePieceContract.formalProduct_restrict_eq_withDensity_of_restrict_eq_map_sourceChart_withDensity
A2Case2FormalProductSourceImagePieceContract.exists_of_restrict_eq_map_sourceChart_withDensity
```

These theorems convert a supplied theta-side weighted source-chart pushforward
identity into the edge-side `withDensity` equality expected by the
formal-product/source-image contract, and then construct the contract from the
same local source-chart fields plus a supplied a.e. density bound.

Boundary: pure measure bookkeeping only.  No Jacobian density is constructed,
no density bound is proved, and no formal-product/source-image domination
follows without supplied equality and bound.  No raw-Haar transport,
determinant-chart Haar equality, source-image coverage, original prior
transport, normal crossings, pole order, or RLCT extraction is proved.

Focused elaboration, focused module build, full local `lake build DLNFibre`,
no-sorry audit, whitespace check, touched-file marker scan, direct axiom
probe, and xhigh review passed.  The two theorem probes report
`[propext, Classical.choice, Quot.sound]`.  Reviewer nits about unnecessary
topology scope and a missing dependency path were fixed.

Frontier note: the next A2 source-moving target is the with-following raw-order
actual-image same-shrink package.  The non-following package already exists;
the with-following source-chart bridge exists, but the named raw-order
reference image/package still needs to be built without calling it raw Haar.

## 2026-07-02 A2 with-following endpoint active-readout derivative determinant

Reproduction:
`reproduction-a2-case2-with-following-endpoint-active-readout-derivative-determinant.md`.
Statement card:
`statement-card-a2-case2-with-following-endpoint-active-readout-derivative-determinant.md`.
Review:
`review-a2-case2-with-following-endpoint-active-readout-derivative-determinant.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaEndpointDerivative.lean
```

Lean now proves:

```text
Case2PassiveThetaWithFollowingFactor.activeSelectedEntryChartMapFDeriv
Case2PassiveThetaWithFollowingFactor.hasFDerivAt_activeSelectedEntryChartMap
Case2PassiveThetaWithFollowingFactor.activeSelectedEntryChartMapFDeriv_absDet_eq_sourceDensity
Case2PassiveThetaWithFollowingFactor.fderiv_activeSelectedEntryChartMap
Case2PassiveThetaWithFollowingFactor.fderiv_endpointTopologyTupleActiveReadout_comp_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_absDet_eq_sourceDensity
```

The final theorem computes the determinant of the source-type endomorphism
obtained by composing the enlarged endpoint topology-tuple map `Y` with
`endpointTopologyTupleActiveReadout`.  The derivative is identity on passive
fields and the normalized following factor, and is the selected-entry chart
derivative on `yNext`; hence the absolute determinant is exactly
`SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext z.1.yNext`.

Boundary: this is not a determinant theorem for the bare endpoint map `Y`.
It is not a local change-of-variables theorem, determinant-chart
Haar/reference-image equality, raw-Haar transport, raw-order composition,
source-image coverage, formal-product domination, normal crossings, pole
order, or RLCT.  No pivot-nonzero hypothesis is needed for the determinant
identity itself; pivot nonzero remains a downstream hypothesis for inverse
readback, injectivity, local COV, and positive lower bounds.

Focused elaboration, focused module build, full local `lake build DLNFibre`,
no-sorry audit, whitespace check, touched-file marker scan, direct axiom
probe, and xhigh read-only review passed.  The focused module build replayed
existing warnings from `ProductReductionStepRegularDensity`; the full build
replayed the existing repository warning profile.  The four theorem probes
report `[propext, Classical.choice, Quot.sound]`.

## 2026-07-02 A2 with-following endpoint reference image pivot-measurable support

Reproduction:
`reproduction-a2-case2-with-following-endpoint-reference-image-pivot-measurable-support.md`.
Statement card:
`statement-card-a2-case2-with-following-endpoint-reference-image-pivot-measurable-support.md`.
Review:
`review-a2-case2-with-following-endpoint-reference-image-pivot-measurable-support.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

Lean now proves:

```text
case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_restrict_image_eq_self_of_subset_pivotNonzero
measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_referenceSource_restrict_eq_endpointReferenceImageMeasure_restrict_image_of_subset_pivotNonzero
```

These wrappers remove the separate `MeasurableSet (Y '' Ω)` input from the
endpoint reference image support theorem when `Ω` is measurable and contained
in the selected-pivot-nonzero locus.  Image measurability is supplied by the
with-following endpoint injectivity/measurable-image theorem from the previous
rung.

Boundary: this is actual endpoint image support only.  It does not prove a
local change-of-variables formula, Jacobian determinant theorem,
determinant-chart Haar equality, raw-Haar transport, raw-order composition,
source-image coverage beyond the actual image `Y '' Ω`, formal-product
domination, normal crossings, pole order, or RLCT.

Focused elaboration, focused module build, full local `lake build DLNFibre`,
no-sorry audit, whitespace check, touched-file forbidden-marker scan, direct
axiom probe, and xhigh review passed.  The two new declarations report
`[propext, Classical.choice, Quot.sound]`.

## 2026-07-02 A2 with-following endpoint Y injectivity and measurable image

Reproduction:
`reproduction-a2-case2-with-following-endpoint-y-injectivity.md`.
Statement card:
`statement-card-a2-case2-with-following-endpoint-y-injectivity.md`.
Review:
`review-a2-case2-with-following-endpoint-y-injectivity.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaCFieldReadout.lean
```

Lean now proves:

```text
case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_injOn_pivotNonzero
measurableSet_case2PassiveThetaWithFollowingFactorEndpointSectorSet_of_subset_pivotNonzero
```

The first theorem says that the enlarged with-following endpoint topology-tuple
map `Y` is injective on the selected-pivot-nonzero locus.  The proof applies
the active readout to `Y z = Y w`, recovers the passive fields, the following
factor, and equality of the selected-entry chart images, then uses
`SelectedEntrySignedBox.CenterCoord.injOn_chartMap_pivot_ne_zero` to recover
`yNext`.

The second theorem is the standard Lusin-Souslin measurable-image consequence:
if `Ω` is measurable, the source coordinate type is Borel/Polish, the endpoint
target has open-measurable T2 topology, and `Ω` is contained in the
selected-pivot-nonzero locus, then `Y '' Ω` is measurable, written through the
named endpoint sector set.

Boundary: this is endpoint-coordinate injectivity and measurable actual-image
support only.  It does not prove a local change-of-variables formula, Jacobian
determinant theorem, determinant-chart Haar equality, raw-Haar transport,
raw-order composition, source-image coverage beyond actual images,
formal-product domination, normal crossings, pole order, or RLCT.

Focused elaboration, focused module build, full local `lake build DLNFibre`,
no-sorry audit, whitespace check, code-only forbidden-marker scan, direct axiom
probe, and xhigh review passed.  The focused and full builds replay existing
repository warnings, including in
`lean/DLNFibre/DLN/Aoyagi/ProductReductionStepRegularDensity.lean`, not in the
touched file.  The two new declarations report
`[propext, Classical.choice, Quot.sound]`.

## 2026-07-02 A2 with-following endpoint reference image support

Reproduction:
`reproduction-a2-case2-with-following-endpoint-reference-image-support.md`.
Statement card:
`statement-card-a2-case2-with-following-endpoint-reference-image-support.md`.
Review:
`review-a2-case2-with-following-endpoint-reference-image-support.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

Lean now proves:

```text
case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_restrict_image_eq_self
measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_referenceSource_restrict_eq_endpointReferenceImageMeasure_restrict_image
```

These theorems say that the named endpoint reference image measure for the
with-following endpoint map `Y` is supported on the actual image `Y '' Ω`,
assuming `Ω` and `Y '' Ω` are measurable.  The unfolded theorem rewrites
`Measure.map Y (referenceSource.restrict Ω)` as the same named endpoint image
measure restricted to that actual image.

Boundary: this is actual-image support only.  It does not prove
determinant-chart Haar equality, raw-Haar transport, raw-order composition,
source-image coverage beyond `Y '' Ω`, formal-product domination, normal
crossings, pole order, or RLCT.

Focused warning-clean elaboration, focused module build, full local
`lake build DLNFibre`, no-sorry audit, whitespace check, forbidden-marker
scan, direct axiom probe, and xhigh review passed.  The two new declarations
report `[propext, Classical.choice, Quot.sound]`.

Frontier note: xhigh API scout `Banach the 2nd` identified the next small
source-moving A2 theorem as with-following `Y` injectivity on the
selected-pivot-nonzero locus, followed by measurable image for `Y '' Ω`.
There is still no full `Y` derivative/determinant theorem, determinant-chart
Haar equality, raw-Haar/raw-map transport, or endpoint coverage beyond actual
local images.

## 2026-07-02 A2 formal-product/source-image bounded-density contract

Reproduction:
`reproduction-a2-formal-product-source-image-contract.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaFormalProductSourceImageContract.lean
```

Lean now defines:

```text
A2Case2FormalProductSourceImagePieceContract
```

and proves:

```text
A2Case2FormalProductSourceImagePieceContract.formalProductMeasure_restrict_le_smul_sourceRef
A2Case2FormalProductSourceImagePieceContract.aemeasurable_readback_and_map_readback_restrict_le_smul_thetaReference_restrict
```

The record stores the local source-chart facts, the p.13 formal-product
measure, the chart piece, the source-image reference, an explicit density, and
the equality-with-density plus local a.e. upper-bound fields.  The first
theorem derives exactly the formal-product/source-image domination consumed by
the same-shrink original-volume bridge.  The second theorem feeds the readback
domination socket over any theta set containing the local `V`.

Boundary: this is bounded-density bookkeeping, not the Jacobian calculation.
The contract does not construct the density identity, prove its bound, prove
coordinate-count agreement, prove source-image coverage, identify determinant
or raw Haar transport, transport the original prior, or prove normal crossings,
pole order, or RLCT extraction.  It also does not assert `bound < infinity`;
finite-integral users still carry separate finiteness hypotheses.

Verification passed: warning-clean direct elaboration of the new Lean file,
focused Lake build, full local `lake build DLNFibre`, `lean/scripts/sorries`,
`git diff --check`, forbidden-marker grep on the new Lean file, and direct
axiom probes for both new theorems.  The axiom footprint is
`[propext, Classical.choice, Quot.sound]`.  Xhigh post-Lean reviewer `Popper`
reported no findings; residual risk is exactly that source-image inclusion and
bounded finite Jacobian density still have to be constructed.

## 2026-07-02 A2 formal-product/source-image local change-of-variables frontier

Construction card:
`construction-card-a2-case2-formal-product-source-image-local-change-of-variables.md`.
Reproduction:
`reproduction-a2-case2-formal-product-source-image-local-change-of-variables.md`.
Review:
`review-a2-case2-formal-product-source-image-local-change-of-variables.md`.

The current source-moving A2 target is the missing comparison

```text
muP13.restrict chartPiece <=
  D • Measure.map sourceChart (thetaReference.restrict V)
```

for measurable `chartPiece subset sourceChart '' V`.  The already-proved
original-volume bridge consumes exactly this formal-product/source-image
domination and turns it into the original-volume domination needed downstream.

The packet records the pen-and-paper gates before Lean: coordinate/dimension
check, source-image/inverse domain, Jacobian density, local boundedness, and
the kill condition that a lower-dimensional selected section cannot dominate
ambient p.13 formal-product measure.

Xhigh A2 scout `Pascal` passed the packet direction and confirmed that the
next Lean target should be the `muP13 <= D * sourceRef` socket, not another
conditional wrapper.

## 2026-07-02 A2 source-prior density and determinant-Haar frontier audit

Audit:
`source-audit-a2-source-prior-density-and-det-haar-frontier.md`.

Two xhigh read-only scouts rechecked the frontier after the formal-product
wrapper.  `Dalton` found no current route to construct or identify the full
`sourceImageDensity` or prove its lower bound; the selected-entry residual
density is only the residual signed-box factor already in `weightedBox`.
`Hegel` found no current route to prove determinant-side reverse domination
by the passive-theta endpoint image; endpoint reference measures are image
references, not unrestricted determinant-chart Haar.

Controller decision: no further conditional wrapper is proposed here.  The
next non-wrapper progress must construct source/prior density transport,
determinant-chart transport for `Y`, or local image/coverage plus Jacobian
comparison strong enough to imply one of those.

## 2026-07-02 A2 formal-product domination from determinant domination and source-density lower bound

Reproduction:
`reproduction-a2-formal-product-coordinate-source-domination-det-density.md`.
Statement card:
`statement-card-a2-formal-product-coordinate-source-domination-det-density.md`.
Review:
`review-a2-formal-product-coordinate-source-domination-det-density.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
```

Lean now proves:

```text
exists_open_subset_formalProductMeasure_restrict_chartPiece_le_smul_coordinateSourceReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
```

The theorem composes the determinant-domination/source-density lower package
with the p.13 formal-product source-reference domination theorem.  It removes
the reverse raw-source domination socket for this formal-product conclusion,
but keeps the determinant-side reverse domination and source-density lower
bound explicit.  Focused direct elaboration and focused Lake module build
passed, as did full local `lake build DLNFibre`, `scripts/sorries`, `git diff
--check`, and direct axiom probing.  The theorem reports only
`[propext, Classical.choice, Quot.sound]`.  Xhigh read-only reviewer `Dirac`
passed the theorem-shape and nonclaim-boundary audit.

Nonclaims: no determinant-chart Haar transport, exact raw-Haar pushforward,
raw-Haar normalization, source-density identification, source-image/source-rank
coverage, original source-prior transport, normal crossings, pole order, or
RLCT extraction.

## 2026-07-02 A2 density pullback continuity to eventual bounds

Reproduction:
`reproduction-a2-density-pullback-continuity-eventual-bounds.md`.
Statement card:
`statement-card-a2-density-pullback-continuity-eventual-bounds.md`.
Review:
`review-a2-density-pullback-continuity-eventual-bounds.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
```

Lean now proves:

```text
eventually_const_le_of_continuousAt_lt
eventually_le_const_of_continuousAt_lt
eventually_sourceImageDensity_comp_lower_priorDensity_comp_upper_of_continuousAt
```

These helpers turn strict basepoint bounds plus continuity of the two density
pullbacks into the eventual sockets consumed by the full prior-domination
eventual-pullback wrapper.  Verification passed: direct elaboration, focused
module build, direct axiom probe, and xhigh read-only route review.  The new
declarations report only `[propext, Classical.choice, Quot.sound]`.

Nonclaims: no construction or identification of `sourceImageDensity`, no
original prior-density transport, no proof of continuity or strict basepoint
bounds, no determinant-chart Haar transport, exact raw-Haar pushforward,
raw-Haar normalization, source-image/source-rank coverage, normal crossings,
pole order, or RLCT extraction.

## 2026-07-02 A2 Case 2 full-image prior domination from eventual pullback bounds

Reproduction:
`reproduction-a2-case2-full-image-prior-domination-eventual-pullback-bounds-wrapper.md`.
Statement card:
`statement-card-a2-case2-full-image-prior-domination-eventual-pullback-bounds-wrapper.md`.
Review:
`review-a2-case2-full-image-prior-domination-eventual-pullback-bounds-wrapper.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
```

Lean now proves:

```text
exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_eventually_sourceImageDensity_comp_sourceChart_lower_priorDensity_comp_sourceChart_upper
```

It wraps the input-image-bound full prior theorem by obtaining the input
neighborhood `G` from two `nhds z0` eventual pullback bounds via
`eventually_nhds_iff`.  Verification passed: focused elaboration, focused
module build, full local `lake build DLNFibre`, `scripts/sorries`, `git diff
--check`, direct axiom probe, and xhigh read-only review.  The theorem reports
only `[propext, Classical.choice, Quot.sound]`.

Nonclaims: no proof of the eventual pullback bounds, no proof of
positivity/boundedness/identification of `sourceImageDensity`, no proof of the
prior-density upper bound, no determinant-chart Haar transport, exact
raw-Haar pushforward, raw-Haar normalization, source-image/source-rank
coverage, normal crossings, pole order, or RLCT extraction.  The shrink `V`
is not uniform in future density bounds.

## 2026-07-01 A2 Case 2 full-image prior domination from input-image bounds

Reproduction:
`reproduction-a2-case2-full-image-prior-domination-input-image-bounds-wrapper.md`.
Statement card:
`statement-card-a2-case2-full-image-prior-domination-input-image-bounds-wrapper.md`.
Review:
`review-a2-case2-full-image-prior-domination-input-image-bounds-wrapper.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
```

Lean now proves:

```text
exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceImageDensity_input_image_lower_priorDensity_input_image_upper
```

It wraps the returned-image-bound full prior theorem and inherits its pointwise
density bounds from the caller's larger input image `sourceChart '' G`, using
the returned containment `V subset G`.  Verification passed: focused
elaboration, focused module build, full local `lake build DLNFibre`,
`scripts/sorries`, `git diff --check`, direct axiom probe, and xhigh
read-only review.  The theorem reports only
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no proof that the input-image bounds hold, no proof that
`sourceChart '' G` is measurable/open/convenient, no determinant-chart Haar
transport, exact raw-Haar pushforward, raw-Haar normalization,
source-image/source-rank coverage, normal crossings, pole order, or RLCT
extraction.

## 2026-07-01 A2 Case 2 full-image prior domination from image bounds

Reproduction:
`reproduction-a2-case2-full-image-prior-domination-image-bounds-wrapper.md`.
Statement card:
`statement-card-a2-case2-full-image-prior-domination-image-bounds-wrapper.md`.
Review:
`review-a2-case2-full-image-prior-domination-image-bounds-wrapper.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
```

Lean now proves the generic helper

```text
ae_restrict_upper_of_forall_mem
```

and the full-image prior-domination image-bound wrapper


```text
exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceImageDensity_image_lower_priorDensity_image_upper
```

It wraps the existing full-image prior-domination theorem and replaces the two
a.e. density hypotheses by pointwise bounds on the returned
`sourceChart '' V`.  Verification passed: focused elaboration, focused module
build, full local `lake build DLNFibre`, `scripts/sorries`, `git diff
--check`, direct axiom probe, and xhigh read-only review.  The new
declarations report only `[propext, Classical.choice, Quot.sound]`.

Nonclaims: no positivity or boundedness proof for either density, no
determinant-chart Haar transport, exact raw-Haar pushforward, raw-Haar
normalization, source-image/source-rank coverage, normal crossings, pole
order, or RLCT extraction.

## 2026-07-01 A2 Case 2 finite integral from reverse raw-source domination

Reproduction:
`reproduction-a2-case2-original-volume-finite-integral-reverse-raw-source-domination.md`.
Statement card:
`statement-card-a2-case2-original-volume-finite-integral-reverse-raw-source-domination.md`.
Review:
`review-a2-case2-original-volume-finite-integral-reverse-raw-source-domination.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadback.lean
```

Lean now proves:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolume_readback_invHaar_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

This weakens the previous finite-integral wrapper from exact raw-pushforward
equality to a finite reverse raw-source domination hypothesis:

```text
m.restrict rawSourceSet
  <= D • Measure.map rawMap (coordinateSourceMeasure.restrict V),
D < ∞.
```

Current verification: focused warning-clean elaboration, focused module build,
full local `lake build DLNFibre`, `scripts/sorries`, `git diff --check`,
direct axiom audit, and xhigh read-only review all passed.  The direct axiom
probe reported only `[propext, Classical.choice, Quot.sound]`.

Nonclaims: no proof of reverse raw-source domination, determinant-chart Haar
transport, raw-Haar pushforward equality, source-image coverage, source-rank
coverage, original source-prior transport, normal crossings, pole order, or
RLCT extraction.

## 2026-07-01 A2 Case 2 readback from reverse raw-source domination

Reproduction:
`reproduction-a2-case2-original-volume-readback-domination-from-reverse-raw-source.md`.
Statement card:
`statement-card-a2-case2-original-volume-readback-domination-from-reverse-raw-source.md`.
Review:
`review-a2-case2-original-volume-readback-domination-from-reverse-raw-source.md`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadback.lean
```

Lean now proves:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap
```

The theorem keeps the reverse raw-source domination explicit:

```text
rawHaar.restrict rawSourceSet
  <= D • Measure.map rawMap (thetaReference.restrict V).
```

It returns a same-shrink source-chart image with readback, injectivity,
continuity, measurable image, p.13 source-set containment, readback
a.e.-measurability for `originalVolume.restrict chartPiece`, and readback
domination by `(cHaar^{-1} * D) • thetaReference.restrict G`.

Current verification: focused warning-clean elaboration, focused module build,
full local `lake build DLNFibre`, `scripts/sorries`, `git diff --check`,
direct axiom audit, and xhigh read-only review all passed.  The direct axiom
probe reported only `[propext, Classical.choice, Quot.sound]`.

Nonclaims: no proof of reverse raw-source domination, determinant-chart Haar
transport, raw-Haar pushforward equality, source-image coverage, source-rank
coverage, original source-prior transport, normal crossings, pole order, or
RLCT extraction.

## 2026-07-01 A2 Case 2 reverse raw-source domination handoff

Reproduction:
`reproduction-a2-case2-reverse-raw-source-domination-to-source-reference.md`.
Statement card:
`statement-card-a2-case2-reverse-raw-source-domination-to-source-reference.md`.
Review:
`review-a2-case2-reverse-raw-source-domination-to-source-reference.md`, PASS
by xhigh read-only scout `Mendel` plus controller check.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaFormalProductSourceReference.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeBridge.lean
```

Lean now proves:

```text
exists_open_subset_formalProductMeasure_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap

exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap
```

The theorems assume the reverse raw-source domination

```text
rawHaar.restrict rawSourceSet
  <= D • Measure.map rawMap (thetaReference.restrict V).
```

They turn it into formal-product/source-reference domination and then
original-volume/source-reference domination with the inverse Haar scalar.

Current verification:

```text
env LEAN_NUM_THREADS=3 lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaFormalProductSourceReference.lean
env LEAN_NUM_THREADS=3 lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeBridge.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaFormalProductSourceReference
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeBridge
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
env LEAN_NUM_THREADS=3 lake env lean --stdin  # direct #print axioms audit
```

The direct axiom audit reports only `[propext, Classical.choice, Quot.sound]`
for both new theorem names.  Nonclaims: no proof of the reverse raw-source
domination, determinant-chart Haar transport, exact raw-Haar pushforward,
source coverage, source-rank coverage, original source-prior transport, normal
crossings, pole order, or RLCT.

## 2026-06-30 A2 original edge-family prior in fixed bases

Reproduction:
`reproduction-a2-original-edge-family-prior-fixed-basis.md`.
Statement card:
`statement-card-a2-original-edge-family-prior-fixed-basis.md`.
Review:
`review-a2-original-edge-family-prior-fixed-basis.md`, PASS by xhigh
sidecar `Noether the 2nd` plus controller check.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyPrior.lean
```

Lean now proves the fixed-basis equivalence between continuous edge families
and original matrix tuples, and defines:

```text
originalEdgeFamilyVolume
originalEdgeFamilyVolume_map_edgeFamilyMatrixTuple
originalEdgeFamilyPrior
originalEdgeFamilyPrior_restrict_le_smul_of_ae_le
```

The key theorem is:

```text
Measure.map (edgeFamilyMatrixTuple b) (originalEdgeFamilyVolume b)
  = originalTupleVolume d.
```

Current verification:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyPrior.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyPrior
env LEAN_NUM_THREADS=3 lake env lean DLNFibre.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_edge_family_prior_axioms.lean
```

Nonclaims: no source-chart transport, chart-image equality, readback
domination, source-rank coverage, Haar/Jacobian transport, normal crossings,
pole order, or RLCT.  The direct axiom probe reports only the baseline
`[propext, Classical.choice, Quot.sound]`.

## 2026-06-30 A2 chart-piece external-source measure handoff

Reproduction:
`reproduction-a2-chart-piece-external-source-measure-handoff.md`.
Statement card:
`statement-card-a2-chart-piece-external-source-measure-handoff.md`.
Review:
`review-a2-chart-piece-external-source-measure-handoff.md`, PASS by xhigh
reviewer `Nietzsche the 2nd`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge.lean
```

Lean now proves:

```text
restrict_withDensity_le_smul_restrict_of_ae_le_of_subset

exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_externalSourceMeasure_restrict_chartPiece_eq_withDensity_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

For the returned `sourceLocal = U ∩ sourceStratum`, the theorem accepts any
measurable `chartPiece ⊆ sourceLocal`; equality with a bounded-density
perturbation of `sourceImageMeasure` on that piece gives finite integrability
over `(externalSourceMeasure.restrict chartPiece).prod ν`.

Current verification:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_chart_piece_external_source_measure_handoff_axioms.lean
```

The direct axiom probe reports only the baseline
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no chart-image measurability, no source-image equality,
original/source-prior transport, Haar/Jacobian transport, normal crossings,
pole order, or RLCT.

## 2026-06-30 A2 product source-chart measure local-source support

Reproduction:
`reproduction-a2-case2-product-source-chart-measure-local-source-support.md`.
Statement card:
`statement-card-a2-case2-product-source-chart-measure-local-source-support.md`.
Review:
`review-a2-case2-product-source-chart-measure-local-source-support.md`,
PASS by xhigh reviewer `Aquinas the 2nd`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Lean now proves:

```text
exists_pos_radius_open_measure_map_case2PassiveThetaEndpointProductSourceChart_restrict_sourceRankStratum_ball_retainedPassiveP13LocalSource_eq_self
```

This wraps the pointwise product source-chart local-source support theorem as
a pushforward-measure support identity for arbitrary product-domain measures
restricted to `V inter sourceStratum` and the regular ball.

Current verification:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_product_source_measure_support_axioms.lean
```

The direct axiom probe reports only the baseline
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no source-rank coverage, source-image equality,
original/source-prior transport, Haar/Jacobian transport, normal crossings,
pole order, RLCT, or product-chart invertibility.

## 2026-06-30 A2 retained-passive source-chart image coverage

Reproduction:
`reproduction-a2-retained-passive-source-chart-image-coverage.md`.
Statement card:
`statement-card-a2-retained-passive-source-chart-image-coverage.md`.
Review:
`review-a2-retained-passive-source-chart-image-coverage.md`, PASS by xhigh
reviewer `Hooke the 2nd`; no formal or mathematical issue found.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean
```

Lean now proves:

```text
exists_open_paperEndpointFixedBaseRetainedPassiveP13SourceChart_image_coverage_of_selfBase
```

This strengthens the existing retained-passive local-source self-base coverage
by exposing a determinant-chart coordinate datum whose retained-passive source
chart realizes `Cedge x` for every `x` in the returned local neighborhood.

Verification:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveLocalSource
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_retained_passive_source_chart_image_coverage_axioms.lean
```

The direct axiom probe reports only the baseline
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no Case 2 passive-theta coverage, no selected-entry coverage, no
source-image equality with a source-rank stratum, no original/source-prior
transport, no Haar/Jacobian transport, no normal crossings, no pole order, and
no RLCT extraction.

## 2026-06-30 A2 Case 2 product source-chart local-source support

Reproduction:
`reproduction-a2-case2-product-source-chart-local-source-support.md`.
Statement card:
`statement-card-a2-case2-product-source-chart-local-source-support.md`.
Review:
`review-a2-case2-product-source-chart-local-source-support.md`, PASS by
xhigh reviewer `Avicenna the 2nd`; no formal or mathematical issue found.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Lean now proves:

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_mem_retainedPassiveP13LocalSource
case2PassiveThetaEndpointProductSourceChart_mem_retainedPassiveP13LocalSource
exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_mem_retainedPassiveP13LocalSource_nhdsWithin_source
```

The generic theorem converts the product-coordinate certificate's recursive
determinant-chart field into membership in the named retained-passive p.13
local source. The concrete wrappers specialize this to the Case 2 endpoint
product source chart and package the determinant-unit hypothesis by a small
regular-coordinate ball.

Verification:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_case2_product_local_source_axioms.lean
```

The direct axiom probe reports only the baseline
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no source-rank coverage, no source-image equality, no
original/source-prior transport, no Haar/Jacobian transport, no normal
crossings, no pole order, and no RLCT extraction.

## 2026-06-30 A2 Case 2 product source-chart product-reduction certificate

Reproduction:
`reproduction-a2-case2-product-source-chart-product-reduction-certificate.md`.
Statement card:
`statement-card-a2-case2-product-source-chart-product-reduction-certificate.md`.
Review:
`review-a2-case2-product-source-chart-product-reduction-certificate.md`, PASS
by xhigh reviewer `Avicenna the 2nd`; no formal or mathematical issue found.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Lean now proves:

```text
exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_productReductionCertificate_nhdsWithin_source
```

For every `Rmax > 0`, the theorem chooses `0 < R ≤ Rmax` so that eventually
along the base source-rank filter, every small regular variable `u` makes the
concrete Case 2 product source chart satisfy
`PaperEndpointFixedBaseProductReductionCertificate`.

Verification:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_case2_product_local_source_axioms.lean
```

The direct axiom probe reports only the baseline
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no source-rank coverage, no source-image equality, no
original/source-prior transport, no Haar/Jacobian transport, no normal
crossings, no pole order, and no RLCT extraction.

## 2026-06-30 A2 source-level external-measure density handoff

Reproduction:
`reproduction-a2-source-level-external-measure-density-handoff.md`.
Statement card:
`statement-card-a2-source-level-external-measure-density-handoff.md`.
Review:
`review-a2-source-level-external-measure-density-handoff.md`, PASS by xhigh
reviewer `Feynman the 2nd`; only non-blocking theorem-name explicitness and
`[SFinite ν]` caller-obligation risks noted.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge.lean
```

Lean now proves:

```text
restrict_withDensity_le_smul_restrict_of_ae_le

exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_externalSourceMeasure_eq_withDensity_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

For the returned `sourceLocal = U ∩ sourceStratum`, a local equality

```text
externalSourceMeasure.restrict sourceLocal
  =
(sourceImageMeasure.withDensity externalDensity).restrict sourceLocal
```

plus an a.e. finite upper bound for `externalDensity` gives the full product
domination needed by the earlier external-product-measure theorem. The result
therefore proves finite loss-power integrability over
`(externalSourceMeasure.restrict sourceLocal).prod ν`.

Verification:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_external_source_measure_handoff_axioms.lean
```

The direct axiom probe reports only the baseline
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no original/source-prior density identity, no proof that the
original prior satisfies the local equality, no Haar transport, no source-rank
coverage, no source-image equality, no normal crossings, no pole order, and no
RLCT extraction.

## 2026-06-30 A2 small-ball fixed-base product source-readback fields

Reproduction:
`reproduction-a2-small-ball-fixed-base-product-source-readback-fields.md`.
Statement card:
`statement-card-a2-small-ball-fixed-base-product-source-readback-fields.md`.
Review:
`review-a2-small-ball-fixed-base-product-source-readback-fields.md`, PASS by
xhigh reviewer `Singer the 2nd`; only non-blocking thin-wrapper `simpa`
fragility noted.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSourceReadback.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Lean now proves:

```text
exists_pos_radius_le_forall_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceReadback_fields
exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_sourceReadback_fields
```

For every `Rmax > 0`, these theorems choose `0 < R ≤ Rmax` so that all
regular variables in `ball(0,R)` satisfy the fixed-base product
source-readback field formula.  The generic theorem is uniform in the base
edge-family point; the Case 2 theorem is uniform in the passive-theta point.

Verification:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionSourceReadback.lean
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RegularSuspensionSourceReadback
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_small_ball_source_readback_axioms.lean
```

The direct axiom probe reports only the baseline
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no full inverse/readback to original parameters, no original/source
prior transport, no Haar/Jacobian density formula, no source-image
coverage/equality, no normal crossings, no pole order, and no RLCT extraction.

## 2026-06-30 A2 generic fixed-base product source-readback fields

Reproduction:
`reproduction-a2-generic-fixed-base-product-source-readback-fields.md`.
Statement card:
`statement-card-a2-generic-fixed-base-product-source-readback-fields.md`.
Review:
`review-a2-generic-fixed-base-product-source-readback-fields.md`, PASS by
xhigh reviewer `Epicurus the 2nd`; only generic proof-maintenance fragility
noted.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSourceReadback.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
lean/DLNFibre.lean
```

Lean now proves:

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceReadback_fields
```

For any fixed-base base edge family `CedgeBase x`, the explicit p.13 product
coordinate family reads back to canonical retained passive fields, decoded
regular fields from `u`, and residual factors extracted from `CedgeBase x`.
The previous concrete Case 2 theorem
`case2PassiveThetaEndpointProductSourceChart_sourceReadback_fields` now calls
this generic theorem with `M = 0`.

Verification:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionSourceReadback.lean
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake env lean DLNFibre.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RegularSuspensionSourceReadback
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_generic_source_readback_axioms.lean
```

The direct axiom probe reports only the baseline
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no full inverse/readback to original parameters, no passive-theta
recovery from the product chart beyond the stated field package, no
original/source-prior transport, no Haar/Jacobian density formula, no
source-image coverage/equality, no normal crossings, no pole order, and no
RLCT extraction.

## 2026-06-30 A2 Case 2 product source-chart source-readback fields

Reproduction:
`reproduction-a2-case2-product-source-chart-source-readback-fields.md`.
Statement card:
`statement-card-a2-case2-product-source-chart-source-readback-fields.md`.
Review:
`review-a2-case2-product-source-chart-source-readback-fields.md`, PASS by
xhigh reviewer `Anscombe the 2nd`; only Lean/API fragility noted.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Lean now proves:

```text
case2PassiveThetaEndpointProductSourceChart_sourceReadback_fields
```

For the concrete endpoint fixed-base product source chart
`productSourceChart(theta,u)`, the theorem instantiates the raw p.13
source-readback field formula.  It returns canonical retained passive fields,
the regular fields decoded from `u`, and residual factors extracted from the
base `sourceChart theta`.

Verification:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_case2_product_source_readback_axioms.lean
```

The direct axiom probe reports only the baseline
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no full inverse/readback to `(theta,u)`, no passive-theta recovery
from the product chart, no original/source-prior transport, no Haar/Jacobian
density formula, no source-image coverage/equality, no normal crossings, no
pole order, and no RLCT extraction.

## 2026-06-30 A2 Case 2 product source-chart regular readback

Reproduction:
`reproduction-a2-case2-product-source-chart-regular-readback.md`.
Statement card:
`statement-card-a2-case2-product-source-chart-regular-readback.md`.
Review:
`review-a2-case2-product-source-chart-regular-readback.md`, PASS by xhigh
reviewer `Goodall the 2nd`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Lean now defines/proves:

```text
case2PassiveThetaEndpointProductSourceChartRegularReadback
case2PassiveThetaEndpointProductSourceChart_regularReadback_eq
```

This packages the p.13 regular-coordinate readout as a source-side map from an
ambient two-edge family to the Euclidean regular block, then proves that the
full Case 2 product source chart sends `(theta,u)` to an edge family whose
regular readback is exactly `u`.

Verification:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_regular_readback_axioms.lean
```

The direct axiom probe reports only the baseline
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no full inverse/readback to `(theta,u)`, no passive-theta recovery
from the product chart, no source-image coverage, no original/source-prior
transport, no Haar transport, no Jacobian formula, no normal crossings, no
pole order, and no RLCT extraction.

## 2026-06-30 A2 Case 2 product source-chart selected inverse readout

Reproduction:
`reproduction-a2-case2-product-source-chart-selected-inverse-readout.md`.
Statement card:
`statement-card-a2-case2-product-source-chart-selected-inverse-readout.md`.
Review:
`review-a2-case2-product-source-chart-selected-inverse-readout.md`, PASS by
xhigh reviewer `Fermat the 2nd`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Lean now proves:

```text
case2PassiveThetaEndpointProductSourceChart_inverseReadout_eq_sourceChart
```

The selected residual inverse readout of `productSourceChart(theta,u)` equals
that of `sourceChart theta`, because the product chart preserves fixed-base
residual block coordinates.  This pairs with the regular readback theorem but
still does not give full passive-theta recovery.

Verification:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_selected_inverse_axioms.lean
```

The direct axiom probe reports only the baseline
`[propext, Classical.choice, Quot.sound]`.

Xhigh scout `Mendel the 2nd` checked full theta recovery and found the exact
missing retained-data identity: current product APIs do not show
`sourceReadback(Eprod) = case2PassiveThetaEndpointRetainedData ... theta eNext
e` for `Eprod` extracted from `productSourceChart(theta,u)`.  For arbitrary
`u`, that statement is conceptually too strong for the present product chart.

Nonclaims: no full inverse/readback to `(theta,u)`, no passive-theta recovery
from the product chart, no sourceReadback retained-data identity, no
source-image coverage, no original/source-prior transport, no Haar transport,
no Jacobian formula, no normal crossings, no pole order, and no RLCT
extraction.

## 2026-06-30 A2 source-image full product domination handoff

Reproduction:
`reproduction-a2-source-image-full-product-domination-handoff.md`.
Statement card:
`statement-card-a2-source-image-full-product-domination-handoff.md`.
Review:
`review-a2-source-image-full-product-domination-handoff.md`.

Lean now proves:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_externalProductMeasure_le_smul_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

The theorem consumes the source-image finite-integral bridge and transfers
finiteness from `(sourceImageMeasure.restrict (U ∩ sourceStratum)).prod ν` to
any externally supplied full product-coordinate measure dominated by a finite
scalar multiple of that product measure.  This includes the p.13 regular
variables through `ν`.

Xhigh source scout `Kierkegaard` checked Aoyagi pp. 10-13 and confirmed that
the future source-prior theorem must be a full p.13 regular-suspension
transport theorem on `(theta, B, F2, F3)`, with positive bounded transported
density `phi(Psi(theta,u)) * |J_Psi(theta,u)|`.  This handoff proves only the
downstream dominated-measure transfer.

Verification:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_source_image_jacobian_axioms.lean
```

The direct axiom probe reports only the baseline
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no original/source-prior density identity, no proof that the
original prior satisfies the domination, no passive-theta-only full p.13 prior
transport, no Haar transport, no source-rank coverage, no normal crossings, no
pole order, and no RLCT extraction.

## 2026-06-30 A2 passive theta source-image Jacobian bridge

Reproduction:
`reproduction-a2-passive-theta-source-image-jacobian-bridge.md`.
Statement card:
`statement-card-a2-passive-theta-source-image-jacobian-bridge.md`.
Review:
`review-a2-passive-theta-source-image-jacobian-bridge.md`, PASS by controller
review after xhigh scouts `Halley` and `Mencius`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge.lean
```

Lean now proves:

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_ae_le_const_globalWithDensity_jacobian_passiveProductMeasure_finiteMass
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_ae_le_const_globalWithDensity_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

The theorem consumes a density on the chart-produced source-image base

```text
sourceImageBase = Measure.map sourceChart (baseJ.restrict W)
```

and proves local-source support, a.e. residual square-sum positivity, and
`residualNegPowerIntegrableOn` for
`sourceImageBase.withDensity sourceImageDensity`, assuming the local
source-image density is a.e.-measurable and bounded and `sourceChart` is
a.e.-measurable for `baseJ.restrict W`.

The proof applies the existing theta-domain Jacobian bounded-density theorem
to `sourceImageDensity ∘ sourceChart`.  The source-image a.e. bound pulls back
by `ae_of_ae_map`, and `restrict_withDensity` plus the standard
map-with-density composition identity identifies the resulting pushforward
with `sourceImageBase.withDensity sourceImageDensity`.

The same source-image measure also feeds the p.13 regular-coordinate
finite-integral wrapper, yielding the local finite integral over
`(sourceImageMeasure.restrict (U ∩ sourceStratum)).prod ν` under the existing
source-stratum loss/density bounds.

Verification:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_source_image_jacobian_axioms.lean
```

The direct axiom probe reports only the baseline
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no original/source prior density identity, no domination for
arbitrary external measures, no passive-theta-only representation of the full
p.13 source prior, no Haar transport, no source-rank coverage, no normal
crossings, no pole order, and no RLCT extraction.

## 2026-06-30 A2 passive theta automatic readback measurability

Reproduction:
`reproduction-a2-passive-theta-source-image-automatic-readback-measurability.md`.
Statement card:
`statement-card-a2-passive-theta-source-image-automatic-readback-measurability.md`.
Review:
`review-a2-passive-theta-source-image-automatic-readback-measurability.md`,
PASS by controller review after the earlier xhigh Lean/API scout identified
the measurable-embedding route.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Lean now proves:

```text
aemeasurable_readback_map_sourceChart_restrict_of_continuousOn_injOn_leftInverse
measure_map_readback_restrict_image_withDensity_le_smul_of_ae_le_of_continuousOn_injOn
exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_withDensity_restrict_image_le_smul_of_continuousOn_injOn
```

The theorem family derives readback a.e. measurability for

```text
Measure.map sourceChart (thetaReference.restrict V)
```

from the local measurable continuous injective source chart and its pointwise
left inverse.  The concrete passive-theta bounded-density source-image
pullback wrapper now supplies this readback measurability internally.

Verification:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_readback_axioms.lean
```

The direct axiom probe for all three new public names reports only the
baseline `[propext, Classical.choice, Quot.sound]`.

Nonclaims: no original/source prior density identity, no source-rank coverage,
no one-chart global support, no Haar transport, no normal crossings, no pole
order, and no RLCT extraction.

## 2026-06-30 A2 passive theta source-image bounded-density pullback

Reproduction:
`reproduction-a2-passive-theta-source-image-bounded-density-pullback.md`.
Statement card:
`statement-card-a2-passive-theta-source-image-bounded-density-pullback.md`.
Review:
`review-a2-passive-theta-source-image-bounded-density-pullback.md`, PASS by
controller review after xhigh source scout `Galileo` and xhigh Lean/API scout
`Euclid`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Lean now proves:

```text
measure_map_readback_map_sourceChart_restrict_eq_self_of_aemeasurable
measure_map_readback_restrict_image_withDensity_le_smul_of_ae_le
measure_map_readback_restrict_image_le_smul_of_restrict_eq_withDensity
exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_withDensity_restrict_image_le_smul
```

The theorem family proves that a bounded-density perturbation of the
chart-produced source-image reference pulls back by `readback` to a measure
dominated by the theta-domain reference.  If an external source measure is
identified with that bounded-density source-image measure on `sourceChart ''
V`, its pulled-back candidate is dominated.  The density identity itself
remains explicit.

Verification:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
```

Axiom probes report only the baseline
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no original/source prior density identity, no source-rank coverage,
no one-chart global support, no Haar transport, no normal crossings, no pole
order, and no RLCT extraction.

## 2026-06-30 A2 passive theta external source-image pullback

Reproduction:
`reproduction-a2-passive-theta-external-source-image-pullback.md`.
Statement card:
`statement-card-a2-passive-theta-external-source-image-pullback.md`.
Review:
`review-a2-passive-theta-external-source-image-pullback.md`, PASS by xhigh
API scout `Huygens` and xhigh source/scope scout `Linnaeus`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Lean now proves:

```text
measure_map_rightInverse_restrict_image_eq_self_of_aemeasurable
measure_map_readback_restrict_image_restrict_eq_self_of_aemeasurable
aemeasurable_of_continuousOn_of_measure_restrict_eq_self
map_le_smul_map_of_le_smul_aemeasurable
measure_restrict_image_le_smul_map_of_map_readback_restrict_image_le_smul
exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_restrict_image_eq_self
```

The concrete theorem returns a local passive-theta source image `sourceChart ''
V` with a right inverse.  For any external source measure restricted to this
image, assuming `readback` is a.e. measurable for that restricted measure, the
pulled-back candidate theta measure is supported on `V` and pushes forward
exactly to the restricted external source measure.

The generic domination handoff also pushes any supplied domination of that
candidate measure by a theta-domain reference measure restricted to `V` to a
domination of the restricted external source measure on `sourceChart '' V`.

Verification:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
```

Axiom probes for the new generic handoff theorem and the new generic
a.e.-measurable map-domination theorem report only the baseline
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no source-rank coverage, no proof that the original prior is
supported in one chart image, no proof of density domination by the
Jacobian-weighted passive product measure, no Haar transport, normal crossings,
pole order, or RLCT extraction.

## 2026-06-30 A2 Case 2 passive theta compatible source right inverse

Reproduction:
`reproduction-a2-case2-passive-theta-compatible-source-right-inverse.md`.
Statement card:
`statement-card-a2-case2-passive-theta-compatible-source-right-inverse.md`.
Review:
`review-a2-case2-passive-theta-compatible-source-right-inverse.md`, PASS by
xhigh read-only checker `Confucius` after a documentation-only correction to
name the ambient open partial homeomorphism `right_inv'`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

Lean now proves:

```text
case2PassiveThetaEndpointSourceChart_readback_eq_and_rightInverse_of_sourceReadback_eq_retainedData
```

The theorem packages the honest local chart boundary.  If a source edge family
`X` is already in the retained-passive determinant source chart, and if its
recursive `sourceReadback` equals the selected Case 2 passive-theta endpoint
retained data while the selected-entry inverse readout equals `theta.yNext`,
then the concrete passive-theta source readback recovers `theta` and the
concrete passive-theta source chart maps `theta` back to `X`.

This uses the existing concrete readback lemma plus the retained-passive
determinant-source `OpenPartialHomeomorph.right_inv'`.  It does not derive the
compatibility hypotheses from source-rank membership.

Verification:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
```

Axiom probe for the new theorem reports only the baseline
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no source-rank coverage, source-image equality, exact-rank
openness, canonical blow-up-center lift, source-prior comparison or transport,
Haar transport, normal crossings, pole order, or RLCT extraction.

## 2026-06-30 A2 Case 2 passive theta source-image source-rank support

Reproduction:
`reproduction-a2-passive-theta-source-image-source-rank-support.md`.
Statement card:
`statement-card-a2-passive-theta-source-image-source-rank-support.md`.
Review:
`review-a2-passive-theta-source-image-source-rank-support.md`, PASS by
xhigh mathematical checker `Bohr` and xhigh Lean/API checker `Anscombe`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Lean now proves:

```text
case2PassiveThetaEndpointSourceChart_mem_sourceRankStratum
exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_subset_sourceRankStratum
exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_restrict_sourceRankStratum_eq_self
```

The pointwise theorem follows the retained-passive p.13 rank calculation:
the two stored residual `C` ranks are `card tau` and the successor
selected-entry residual rank, and endpoint transport preserves the stored
`C` ranks.  The image theorem exposes determinant-chart membership on the
local source-image domain and proves only the forward implication from
`sourceChart '' V` to the source-rank stratum under the explicit
successor-rank equation.  The measure theorem replaces the pointwise
successor-rank equation by an a.e. hypothesis for the restricted theta-domain
measure.

Nonclaims: no source-rank coverage, source-image equality, exact-rank
openness, source-prior comparison or transport, Haar transport, normal
crossings, pole order, or RLCT extraction.

## 2026-06-30 A2 Case 2 passive theta Jacobian measurable endpoint-sector domination

Reproduction:
`reproduction-a2-case2-passive-theta-jacobian-measurable-endpoint-sector-domination.md`.
Statement card:
`statement-card-a2-case2-passive-theta-jacobian-measurable-endpoint-sector-domination.md`.
Review:
`review-a2-case2-passive-theta-jacobian-measurable-endpoint-sector-domination.md`,
PASS by xhigh source/scope reviewer `Poincare` and xhigh Lean/API reviewer
`Feynman`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
```

Lean now proves:

```text
exists_open_subset_measurableSet_case2PassiveThetaEndpointSectorSet
exists_pos_open_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_withDensity_jacobian_restrict_endpointSectorSet_le_smul_passiveProductMeasure
```

The first theorem is a shrink-stable Lusin-Souslin image-measurability lemma.
Inside any prescribed open neighborhood of a determinant-sector, nonzero-pivot
base theta point, it returns a smaller open neighborhood with measurable
endpoint sector image.

The second theorem combines that shrink-stable measurability with the
concrete Jacobian upper sandwich.  It returns a positive `K` and one open
local endpoint sector `V` for which the sector image is measurable and the
Jacobian-weighted passive-product endpoint pushforward is dominated by
`ofReal K` times the unweighted passive-product endpoint pushforward, both
restricted to that named endpoint sector.

Nonclaims: no global endpoint-sector measurability, exact passive-sector Haar
transport, determinant-chart Haar transport, raw-order Haar transport,
source-prior comparison, source-image equality, source-rank coverage, normal
crossings, pole order, or RLCT extraction.

## 2026-06-30 A2 Case 2 passive theta endpoint local injectivity and measurable image

Reproduction:
`reproduction-a2-case2-passive-theta-endpoint-local-injectivity-measurable-image.md`.
Statement card:
`statement-card-a2-case2-passive-theta-endpoint-local-injectivity-measurable-image.md`.
Review:
`review-a2-case2-passive-theta-endpoint-local-injectivity-measurable-image.md`,
PASS by xhigh source/scope reviewer `Hooke` and xhigh Lean/API reviewer
`Pasteur`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

Lean now proves:

```text
exists_open_case2PassiveThetaEndpointTopologyTuple_rawOrderSourceChart_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
exists_open_case2PassiveThetaEndpointTopologyTuple_sourceChart_injOn
exists_open_measurableSet_case2PassiveThetaEndpointSectorSet
```

The pointwise raw-order theorem removes the measure wrapper from the
raw-order/source-chart bridge.  The injectivity theorem returns one open
neighborhood `V` of a determinant-sector, nonzero-pivot base theta point with

```text
Set.InjOn sourceChart V
Set.InjOn (case2PassiveThetaEndpointTopologyTuple ...) V.
```

The measurable-image theorem applies Lusin-Souslin under explicit
Polish/Borel domain hypotheses and opens-measurable/T2 target hypotheses, and
returns an open `V` with

```text
MeasurableSet (case2PassiveThetaEndpointSectorSet ... V).
```

Nonclaims: no global endpoint-sector measurability, source-image equality,
source-rank coverage, exact passive-sector Haar transport, determinant-chart
Haar transport, raw-order Haar transport, source-prior comparison, normal
crossings, pole order, or RLCT extraction.

## 2026-06-30 A2 Case 2 passive theta source-chart readback left inverse

Reproduction:
`reproduction-a2-case2-passive-theta-source-chart-readback-left-inverse.md`.
Statement card:
`statement-card-a2-case2-passive-theta-source-chart-readback-left-inverse.md`.
Review:
`review-a2-case2-passive-theta-source-chart-readback-left-inverse.md`, PASS by
xhigh source/scope reviewer `Dirac` and xhigh Lean/API reviewer `Ramanujan`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

Lean now proves:

```text
endpointTransport_symm_endpointTransport
case2PassiveThetaEndpointSourceChartReadback
case2PassiveThetaEndpointSourceChartReadback_eq_of_sourceReadback_eq_retainedData
exists_open_case2PassiveThetaEndpointSourceChart_readback_leftInverse
```

The final theorem returns an open neighborhood of any determinant-sector,
nonzero-pivot base theta point on which the concrete endpoint p.13 source
chart has a pointwise left inverse:

```text
readback (sourceChart z) = z.
```

The proof is purely local coordinate algebra.  It uses the determinant-domain
source-readback theorem, restricts to the open selected-pivot nonzero set, and
then applies the selected-entry inverse-readout equality.  Passive fields are
recovered by the new endpoint-transport inverse lemma.

Nonclaims: no endpoint-sector image measurability, source-image equality,
exact passive-sector Haar transport, determinant-chart Haar transport,
raw-order Haar transport, source-prior comparison, source-rank coverage,
normal crossings, pole order, or RLCT extraction.  The natural next use is
local injectivity/image measurability for the concrete endpoint theta map.

## 2026-06-30 A2 Case 2 passive theta raw-order two-stage source chart

Reproduction:
`reproduction-a2-case2-passive-theta-raw-order-two-stage-source-chart.md`.
Statement card:
`statement-card-a2-case2-passive-theta-raw-order-two-stage-source-chart.md`.
Review:
`review-a2-case2-passive-theta-raw-order-two-stage-source-chart.md`, PASS by
xhigh source/scope reviewer `Herschel` and xhigh Lean/API reviewer `Gibbs`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

Lean now proves:

```text
exists_open_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
```

This specializes the generic passive selected-entry raw-order bridge to the
concrete full `Case2PassiveTheta` endpoint topology-tuple map.  Locally near a
determinant-sector, nonzero-pivot base point, the raw-order p.13 source chart
applied to

```text
topologyTupleEdgeRawOrder
  (case2PassiveThetaEndpointTopologyTuple ... theta eNext e)
```

equals the direct `case2PassiveThetaEndpointSourceChart`.  The theorem also
records local source membership, `sourceReadback = retainedData`, pointwise
`inverseReadout (sourceChart theta) = theta.yNext`, and the one-stage/two-stage
restricted pushforward equalities through the raw-order intermediate map.

Nonclaims: no exact passive-sector Haar transport, determinant-chart Haar
transport, raw-order Haar transport, source-prior comparison,
endpoint-sector measurability, source-image equality, source-rank coverage,
normal crossings, pole order, or RLCT extraction.  The next frontier is a
local inverse/image theorem for the concrete endpoint theta map, not another
conditional domination wrapper.

## 2026-06-30 A2 Case 2 passive theta global Jacobian-weighted single-open wrapper

Reproduction:
`reproduction-a2-case2-passive-theta-jacobian-global-weighted-single-open.md`.
Statement card:
`statement-card-a2-case2-passive-theta-jacobian-global-weighted-single-open.md`.
Review:
`review-a2-case2-passive-theta-jacobian-global-weighted-single-open.md`.

Lean now repackages the Jacobian-weighted residual-source theorem with one
open neighborhood:

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_passiveProductMeasure_globalWithDensity_jacobian_finiteMass
```

It uses `sourceMeasure = passiveSource.withDensity jacobianDensity` and
`Measure.map sourceChart (sourceMeasure.restrict W)`, with `W = U ∩ V` from
the previous two-open theorem.  The measure equality is just
`restrict_withDensity` plus `Measure.restrict_restrict`.

Focused direct warning check, focused module build, full local build,
aggregator direct warning check, `scripts/sorries`, `git diff --check`, and
direct axiom probe passed.  The public theorem reports only `[propext,
Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer `Leibniz` and
xhigh Lean/API reviewer `Locke` returned PASS.

Nonclaims: no determinant-chart Haar transport, raw-order Haar transport,
source-prior transport, exact passive-sector pushforward, source-image
equality, source-rank coverage, global usefulness of the Jacobian density,
normal crossings, pole order, or RLCT extraction.

## 2026-06-30 A2 Case 2 passive theta Jacobian-weighted residual-source adapter

Reproduction:
`reproduction-a2-case2-passive-theta-jacobian-weighted-residual-source.md`.
Statement card:
`statement-card-a2-case2-passive-theta-jacobian-weighted-residual-source.md`.
Review:
`review-a2-case2-passive-theta-jacobian-weighted-residual-source.md`.

Lean now combines the concrete passive-theta raw-order Jacobian sandwich with
the concrete passive-theta local-domination residual-source socket:

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_passiveProductMeasure_withDensity_jacobian_finiteMass
```

The theorem first chooses an open Jacobian-unit neighborhood `U`, weights
`(passiveMeasure.prod weightedBox).restrict U` by the retained-passive
raw-order Jacobian product read through
`case2PassiveThetaEndpointTopologyTuple`, obtains finite scalar domination by
the passive-product source measure from the upper sandwich, and then obtains a
second open neighborhood `V` from the residual-source socket.  The final
chart-produced measure restricted by `V` is supported on the retained-passive
p.13 local source, has a.e. residual square-sum positivity, and satisfies
`residualNegPowerIntegrableOn`.

Focused direct warning check, focused module build, full local build,
aggregator direct warning check, `scripts/sorries`, `git diff --check`, and
direct axiom probe passed.  The public theorem reports only `[propext,
Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer `Meitner` and
xhigh Lean/API reviewer `Hubble` returned PASS.

Nonclaims: no determinant-chart Haar transport, raw-order Haar transport,
source-prior transport, exact passive-sector pushforward, source-image
equality, source-rank coverage, normal crossings, pole order, or RLCT
extraction.

## 2026-06-30 A2 Case 2 passive theta Jacobian sandwich

Reproduction:
`reproduction-a2-case2-passive-theta-jacobian-sandwich.md`.
Statement card:
`statement-card-a2-case2-passive-theta-jacobian-sandwich.md`.
Review:
`review-a2-case2-passive-theta-jacobian-sandwich.md`.

Lean now specializes the generic passive-parameter retained-passive raw-order
Jacobian sandwich to `Case2PassiveTheta`:

```text
exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2PassiveThetaEndpointTopologyTuple_passiveProductMeasure
```

The theorem gives positive constants `epsilon`, `K`, and an open neighborhood
`U` so that weighting `sourceMeasure.restrict U` by
`ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z))` is
bounded between finite scalar multiples of the unweighted local measure.

Focused direct warning check, focused module build, full local build, and
aggregator direct warning check, `scripts/sorries`, `git diff --check`, and
direct axiom probe passed.  The public theorem reports only `[propext,
Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer `Aristotle`
returned PASS; xhigh Lean/API reviewer `Copernicus` found an unnecessary
`[Fintype tau] [DecidableEq tau]` API restriction, which was removed.

Nonclaims: no determinant-chart Haar transport, raw-order Haar transport,
source-prior transport, exact passive-sector pushforward, source-image
equality, source-rank coverage, normal crossings, pole order, or RLCT
extraction.

## 2026-06-30 A2 Case 2 passive theta bounded-density residual-source adapter

Reproduction:
`reproduction-a2-case2-passive-theta-bounded-density-residual-source.md`.
Statement card:
`statement-card-a2-case2-passive-theta-bounded-density-residual-source.md`.
Review:
`review-a2-case2-passive-theta-bounded-density-residual-source.md`.

Lean now specializes the generic bounded-density passive-product
residual-source handoff to `Case2PassiveTheta`:

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_withDensity_ae_le_const_passiveProductMeasure_finiteMass
```

The theorem uses
`sourceMeasure = (passiveMeasure.prod weightedBox).withDensity sourceDensity`.
It returns a local punctured determinant-sector `V`; after `V` is chosen, any
finite local a.e. density bound against `(passiveMeasure.prod weightedBox).restrict V`
implies retained-passive local-source support, a.e. residual square-sum
positivity, and `residualNegPowerIntegrableOn`.

Focused direct warning check, focused module build, full local build,
`scripts/sorries`, `git diff --check`, aggregator direct warning check, and
direct axiom probe passed.  The public theorem reports only `[propext,
Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer `Fermat` and
xhigh Lean/API reviewer `Pauli` returned PASS.

Nonclaims: no original source-prior density construction, no proof that an
original prior satisfies the bound, no exact restricted `yNext` marginal
equality, determinant-chart Haar transport, raw-order Haar transport,
source-prior transport, exact passive-sector pushforward, source-image
equality, source-rank coverage, normal crossings, pole order, or RLCT
extraction.

## 2026-06-30 A2 Case 2 passive theta product-measure residual-source adapter

Reproduction:
`reproduction-a2-case2-passive-theta-product-measure-residual-source.md`.
Statement card:
`statement-card-a2-case2-passive-theta-product-measure-residual-source.md`.
Review:
`review-a2-case2-passive-theta-product-measure-residual-source.md`.

Lean now specializes the generic passive-product and local-domination
residual-source handoffs to `Case2PassiveTheta`:

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_passiveProductMeasure_finiteMass
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_restrict_le_smul_passiveProductMeasure_finiteMass
```

The concrete product-measure theorem uses
`sourceMeasure = passiveMeasure.prod weightedBox`, finite passive mass, positive
selected-entry radii, `0 <= t`, and the selected-entry critical inequality.
The arbitrary-source theorem leaves
`sourceMeasure.restrict V <= c • passiveSource` and `c < infinity` as explicit
local hypotheses after `V` is chosen.

Focused direct warning check, focused module build, full local build,
`scripts/sorries`, `git diff --check`, aggregator direct warning check, and
direct axiom probes passed.  Both public theorems report only `[propext,
Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer `Parfit` and
xhigh Lean/API reviewer `Averroes` returned PASS.

Nonclaims: no exact restricted `yNext` marginal equality, determinant-chart
Haar transport, raw-order Haar transport, source-prior transport, exact
passive-sector pushforward, source-image equality, source-rank coverage,
finite-integral transfer for the original source prior, normal crossings, pole
order, or RLCT extraction.

## 2026-06-30 A2 Case 2 passive theta source-measure adapter

Reproduction:
`reproduction-a2-case2-passive-theta-source-measure-adapter.md`.
Statement card:
`statement-card-a2-case2-passive-theta-source-measure-adapter.md`.
Review:
`review-a2-case2-passive-theta-source-measure-adapter.md`.

Lean now specializes the generic passive selected-entry source-measure theorem
to the concrete full theta coordinate domain:

```text
case2PassiveThetaEndpointSourceChart
case2PassiveThetaEndpointResidualCoordEquiv
case2PassiveThetaEndpointInverseReadout
exists_open_measure_map_case2PassiveThetaEndpointSourceChart_puncturedSector_inverseReadout_eq_yNext
```

The theorem takes an arbitrary measure on `Case2PassiveTheta`, restricts it to
an existential open punctured determinant-sector neighborhood `V`, and proves
that the chart-produced source measure is supported on the retained-passive
p.13 local source and has selected residual inverse readout equal to the
`Case2PassiveTheta.yNext` marginal.

Focused direct warning check, focused module build, full local build,
`scripts/sorries`, `git diff --check`, aggregator direct warning check, and
direct axiom probe passed.  The public theorem reports only `[propext,
Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer `Banach` and
xhigh Lean/API reviewer `Popper` returned PASS.

Nonclaims: no determinant-chart Haar transport, raw-order Haar transport,
source-prior transport, exact passive-sector pushforward, dominated
passive-sector comparison, finite-integral transfer, source-image equality,
source-rank coverage, normal crossings, pole order, or RLCT extraction.

Next frontier: instantiate the theta-domain measure with a product-style
passive measure and selected-entry weighted box, proving domination of the
restricted `yNext` marginal.  Do not claim exact marginal equality without a
product-saturated sector theorem.

## 2026-06-30 A2 Case 2 passive theta coordinate domain

Reproduction:
`reproduction-a2-case2-passive-theta-coordinate-domain.md`.
Statement card:
`statement-card-a2-case2-passive-theta-coordinate-domain.md`.
Review:
`review-a2-case2-passive-theta-coordinate-domain.md`.

Lean now introduces the concrete full passive-sector coordinate package for
the Case 2 post-pivot selected-entry retained-passive chart:

```text
Case2PassiveTheta.PassiveFields
Case2PassiveTheta
case2PassiveThetaPivotNext
case2PassiveThetaPivotNonzero
case2PassiveThetaDetSector
case2PassiveThetaPuncturedDetSector
case2PassiveThetaRetainedData
case2PassiveThetaEndpointRetainedData
case2PassiveThetaTopologyTuple
case2PassiveThetaEndpointTopologyTuple
continuous_case2PassiveThetaRetainedData
continuous_case2PassiveThetaEndpointRetainedData
continuous_case2PassiveThetaTopologyTuple
continuous_case2PassiveThetaEndpointTopologyTuple
case2PassiveThetaRetainedData_detChart
case2PassiveThetaEndpointRetainedData_detChart
case2PassiveThetaTopologyTuple_mem_detChartSet
case2PassiveThetaEndpointTopologyTuple_mem_detChartSet
```

The determinant sector requires only the retained-passive unit conditions
`Ctop.det` and all passive `A1passive.det` to be units.  The selected pivot
nonzero condition is recorded separately as a punctured-sector predicate.

Focused direct warning check, focused module build, full local build,
`scripts/sorries`, `git diff --check`, and direct axiom probes passed.  Full
local build has only pre-existing warning noise from unrelated modules.
Xhigh source/scope reviewer `Socrates` and xhigh Lean/API reviewer
`Chandrasekhar` returned PASS.

Nonclaims: no determinant-chart Haar transport, source-prior transport,
exact/dominated passive-sector measure theorem, finite-integral transfer,
source-image equality, source-rank coverage, normal crossings, pole order, or
RLCT extraction.

## 2026-06-30 A2 retained-passive passive-sector construction frontier

Reproduction:
`reproduction-a2-retained-passive-passive-sector-construction.md`.
Statement card:
`statement-card-a2-retained-passive-passive-sector-construction.md`.

The live Case 2 retained-passive local-jacobian lane still has an explicit
determinant-chart pushforward hypothesis:

```text
m.restrict Sdet = Measure.map chart weightedBox
```

The reduced selected-entry signed-box chart is lower-dimensional and should
not be used to prove this full determinant-chart Haar statement.  The next
source-moving A2 work is to add the suppressed passive retained p.13
coordinates and prove an exact or finite-scalar/bounded-density dominated
passive-sector measure theorem, provisionally in a future module
`RetainedPassiveCase2PassiveSector.lean`.

This note proves no Lean theorem.  Xhigh reviewer `Raman` found two wording
issues, both repaired: bare mutual absolute continuity was removed as too
weak for the finite-integral handoff, and the passive-coordinate list now
includes `A3passive`.  Review:
`review-a2-retained-passive-passive-sector-construction.md`.

## 2026-06-29 A2 selected-entry all-pivot producer shell

Reproduction:
`reproduction-a2-selected-entry-all-pivot-producer-shell.md`.
Statement card:
`statement-card-a2-selected-entry-all-pivot-producer-shell.md`.
Review:
`review-a2-selected-entry-all-pivot-producer-shell.md`.

Lean now assembles the proved all-pivot analytic fields into a supplied
producer shell:

```text
SelectedEntrySignedBox.CenterCoord.selectedEntryAllPivotSuppliedAnalyticAtlasProducer
```

The shell fills source coverage, chart regularity, transition regularity, unit
regularity, and Jacobian/volume compatibility over the same shared context
`selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv`.  It takes
`SelectedEntryAtlasProducedBranchData` and `SelectedEntryBranchTerminationData`
as explicit inputs over the same `BranchState`.

Focused local `lake build`, direct `lake env lean -E warning`, full local
`lake build DLNFibre`, `lean/scripts/sorries`, `git diff --check`, and direct
axiom probe passed; the declaration reports only `[propext,
Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer `Darwin the 4th`
and xhigh Lean/API reviewer `James the 4th` returned PASS.

Nonclaims: no source production, branch termination, branch guard
exhaustiveness, branch-state transition semantics, normal-crossing extraction,
pole order, or RLCT.

## 2026-06-29 A2 selected-entry all-pivot transition regular data

Reproduction:
`reproduction-a2-selected-entry-all-pivot-transition-regular-data.md`.
Statement card:
`statement-card-a2-selected-entry-all-pivot-transition-regular-data.md`.
Review:
`review-a2-selected-entry-all-pivot-transition-regular-data.md`.

Lean now packages the finite selected-entry normalized overlap formula as
transition regularity over the shared all-pivot universal-domain context:

```text
allPivotTransitionDenom
allPivotTransitionDomain
allPivotTransitionPoint
continuous_allPivotTransitionDenom
continuous_allPivotTransitionNumerator
continuousOn_allPivotTransitionPoint
selectedEntryAllPivotAnalyticTransitionRegularData
selectedEntryAllPivotAnalyticTransitionRegular
```

The transition from source chart `source` to target chart `target` is defined
on the nonzero-denominator overlap
`{x | allPivotTransitionDenom chartEquiv source target x != 0}`.  The map is
the finite selected-entry division formula and preserves chart maps by the
already-proved finite theorem
`chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero`.

Aoyagi PDF pp. 15-22 support the chosen-pivot selected-entry substitution.
The all-pivot transition/renormalization record is expedition-built finite
overlap bookkeeping over existing Lean transition lemmas.

Focused local `lake build`, direct `lake env lean -E warning`, full local
`lake build DLNFibre`, `lean/scripts/sorries`, `git diff --check`, and direct
axiom probes passed; the two new public declarations report only
`[propext, Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer
`Erdos the 4th` returned PASS after source-attribution wording was repaired,
and xhigh Lean/API reviewer `Confucius the 4th` returned PASS.

Nonclaims: no source production, branch termination, source-prior transport,
determinant-chart Haar transport, full supplied analytic atlas producer,
normal-crossing extraction, pole order, or RLCT.

## 2026-06-29 A2 selected-entry all-pivot Jacobian/volume data

Reproduction:
`reproduction-a2-selected-entry-all-pivot-jacobian-volume-data.md`.
Statement card:
`statement-card-a2-selected-entry-all-pivot-jacobian-volume-data.md`.
Review:
`review-a2-selected-entry-all-pivot-jacobian-volume-data.md`.

Lean now lifts the one-pivot selected-entry Jacobian/volume data to the shared
all-pivot universal-domain context:

```text
selectedEntryAllPivotAnalyticJacobianVolumeData
selectedEntryAllPivotAnalyticJacobianVolumeCompatible
```

Each chart `c` is handled by applying the one-pivot chart-point measure
pushforward at the selected pivot `chartEquiv c`.  The chart measure is
`chartPointProductMeasure (chartEquiv c) R`, the density is
`ofReal (chartPointDensity (chartEquiv c) x)`, and the target is
`chartMap (chartEquiv c) '' signedBoxSet R`.

The shared context is exactly
`selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv`, the same
context used by the all-pivot source-coverage and regularity data.  This does
not supply transition regularity between distinct selected-entry pivots or a
full supplied analytic atlas producer.

Focused local `lake build`, direct `lake env lean -E warning`, full local
`lake build DLNFibre`, `lean/scripts/sorries`, `git diff --check`, and direct
axiom probes passed; the two new declarations report only
`[propext, Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer
`Arendt the 4th` and xhigh Lean/API reviewer `Mendel the 4th` returned PASS.

Nonclaims: no transition regularity, source production, branch termination,
source-prior transport, determinant-chart Haar transport, full supplied
analytic atlas producer, normal-crossing extraction, pole order, or RLCT.

## 2026-06-29 A2 Case 2 passive-sector source-stratum-bounds finite integral

Reproduction:
`reproduction-a2-case2-passive-sector-source-stratum-bounds-finite-integral.md`.
Statement card:
`statement-card-a2-case2-passive-sector-source-stratum-bounds-finite-integral.md`.
Review:
`review-a2-case2-passive-sector-source-stratum-bounds-finite-integral.md`.

Lean now proves:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_withPassive_puncturedSector_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

This is the source-stratum-bound sibling of the passive-sector finite-integral
handoff.  It returns an open passive/selected-entry coordinate-domain sector `V`
around `z0`; for

```text
mu = Measure.map sourceChart (sourceMeasure.restrict V)
```

it returns an open edge-family neighborhood `U` around the fixed-base source
family and proves the p.13 regular-coordinate finite integral over
`(mu.restrict (U ∩ sourceStratum)).prod nu`.

The residual-source handoff supplies support on `localSource`, residual
square-sum positivity, and residual negative-power integrability.  The
source-stratum-bound consumer keeps source data, local loss lower bound, local
density nonnegativity, and local density boundedness explicit over
`nhdsWithin base sourceStratum`.  The only bridge from `sourceStratum` to
`localSource` is the self-base local inclusion
`Ulocal ∩ sourceStratum ⊆ Ulocal ∩ localSource`; it is not source-rank coverage.

Focused local `lake build`, direct `lake env lean -E warning`, full local
`lake build DLNFibre`, `lean/scripts/sorries`, `git diff --check`, and direct
axiom probe passed; the theorem reports only `[propext, Classical.choice,
Quot.sound]`.  Xhigh source/scope reviewer `Mencius the 4th` and xhigh Lean/API
reviewer `Dalton the 4th` returned PASS.

Nonclaims: no determinant-chart Haar transport, source-prior transport,
passive/source Jacobian transport, source-image equality, source-rank coverage,
exact localized residual marginal equality, normal crossings, pole order, or
RLCT.

## 2026-06-29 A2 Case 2 passive-sector finite-integral handoff

Reproduction:
`reproduction-a2-case2-passive-sector-finite-integral-handoff.md`.
Statement card:
`statement-card-a2-case2-passive-sector-finite-integral-handoff.md`.
Review:
`review-a2-case2-passive-sector-finite-integral-handoff.md`.

Lean now proves:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_withPassive_puncturedSector_passiveProductMeasure_finiteMass
```

This composes the passive selected-entry punctured-sector residual-source
handoff with the retained-passive p.13 local finite-integral consumer.  It
returns an open passive/selected-entry coordinate-domain sector `V` around
`z0`; for

```text
mu = Measure.map sourceChart (sourceMeasure.restrict V)
```

it returns an open edge-family neighborhood `U` around the fixed-base source
family and proves the p.13 regular-coordinate finite integral over
`(mu.restrict (U ∩ sourceStratum)).prod nu`.

The residual-source handoff supplies support on `localSource`, residual
square-sum positivity, and residual negative-power integrability.  The local
finite-integral consumer keeps source data, local loss lower bound, local
density nonnegativity, and local density boundedness explicit over
`nhdsWithin base localSource`.

Focused local `lake build`, direct `lake env lean -E warning`, `scripts/sorries`,
`git diff --check`, and direct axiom probe passed; the new theorem reports only
`[propext, Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer
`Fermat the 4th` returned PASS after documentation wording was repaired from
"source-rank coverage" to the actual local-source inclusion.  Xhigh Lean/API
reviewer `Curie the 4th` returned PASS.

Nonclaims: no determinant-chart Haar transport, source-prior transport,
passive/source Jacobian transport, source-image equality, source-rank coverage,
exact localized residual marginal equality, normal crossings, pole order, or
RLCT.

## 2026-06-29 A2 selected-entry all-pivot regular data

Reproduction:
`reproduction-a2-selected-entry-all-pivot-regular-data.md`.
Statement card:
`statement-card-a2-selected-entry-all-pivot-regular-data.md`.
Review:
`review-a2-selected-entry-all-pivot-regular-data.md`.

Lean now lifts the one-pivot selected-entry chart and unit regularity facts to
the shared all-pivot universal-domain context:

```text
selectedEntryAllPivotAnalyticChartRegularData
selectedEntryAllPivotAnalyticUnitRegularData
selectedEntryAllPivotAnalyticChartRegular
selectedEntryAllPivotAnalyticUnitRegular
```

Each chart `c` is handled by applying the one-pivot continuity/unit facts at
the selected pivot `chartEquiv c`.  The chart map is the finite substitution
`x_p = u`, `x_i = u r_i`; the unique coordinate is `u`; the loss unit is
`1 + sum r_i^2`; and the formal Jacobian/prior unit is constant `1`.

The shared context is exactly
`selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv`, the same
context used by the all-pivot source-coverage data.  This does not supply
transition regularity between distinct selected-entry pivots.

Focused and full local `lake build` gates passed, along with a direct
`lake env lean -E warning` check of the new file.  The direct axiom probe for
the four new declarations reported only
`[propext, Classical.choice, Quot.sound]`.  Xhigh source/scope reviewer
`Maxwell the 4th` and xhigh Lean/API reviewer `Sartre the 4th` returned PASS.

Nonclaims: no transition regularity, Jacobian/volume compatibility, source
production, branch termination, source-prior transport, determinant-chart Haar
transport, normal-crossing extraction, pole order, or RLCT.

## 2026-06-29 A2 Case 2 selected-entry Schur cleanup

Reproduction:
`reproduction-a2-case2-selected-entry-schur-cleanup.md`.
Statement card:
`statement-card-a2-case2-selected-entry-schur-cleanup.md`.
Review:
`review-a2-case2-selected-entry-schur-cleanup.md`.

Lean now records the source-facing finite block algebra from Aoyagi pp. 19-22:

```text
pivotFirstMatrix_mul_pivotQ_eq_pivotPostQBlock
case2SourceSelectedSubstitutionBlockOfMem_eq_mul_normalized
case2SourceSelectedNormalizedBlockOfMem_mul_pivotQ
case2DisplayedPaperDchart_mul_Q_eq_pivotPostQBlock
```

The wrappers expose the displayed selected-entry factorization `D = u E`,
the right cleanup `E Q = [[1,0],[c,Z-ca]]`, and the displayed-paper spelling
`D_chart * Q` as the post-`Q` Schur block.  The weighted left cleanup remains
the existing finite API:

```text
weightedPivotBlockRowOp_mul_diagonal_mul_pivotPostQBlock
weightedPivotBlockRowOp_mul_diagonal_mul_pivotPreQBlock_mul_pivotQ
weightedPivotBlockRowOp_mul_diagonal_mul_pivotFirstMatrix_mul_pivotQ
weightedPivotBlockRowOp_mul_oldDiagonal_mul_smul_pivotPreQBlock_mul_pivotQ
```

The corrected source-side convention is explicit: when the old block is
`D = u E`, absorb `u` into the row weights `B' = u B_old`; do not keep an
extra global `u`.

Focused and full local `lake build` gates passed.  `scripts/sorries`,
`git diff --check`, and the touched Aoyagi Lean-file forbidden-marker scan
passed.  Xhigh source/scope reviewer `Ampere the 4th` and xhigh Lean/API
reviewer `Franklin the 4th` returned PASS.

Nonclaims: no analytic atlas coverage, chart-domain regularity, transition
regularity, Jacobian or volume compatibility, source production, branch
termination, source-prior transport, determinant-chart Haar transport,
source-rank coverage, normal crossings, pole order, or RLCT.  The lower-right
Schur block is not identified as the next residual block without the separate
continuing-branch reindexing and size hypotheses.

## 2026-06-29 A2 Case 2 source chart-point coverage

Reproduction:
`reproduction-a2-case2-source-chart-point-coverage.md`.
Statement card:
`statement-card-a2-case2-source-chart-point-coverage.md`.
Review:
`review-a2-case2-source-chart-point-coverage.md`.

Lean now specializes the generic all-pivot selected-entry source chart-point
coverage theorem to the Case 2 residual-block certificate:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
  .exists_sourceChartPoint_chartMap_eq_value
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
  .exists_sourceChartPoint_chartMap_eq_value_and_coord_zero_eq_sourceSelected
```

The first theorem chooses a chart index, source selected variable `u`, and
residual function whose `sourceChartPoint` maps to an arbitrary finite
residual-block center value.  The second theorem also records that the unique
certificate coordinate of the witness is `u`.

Aoyagi PDF pp. 19-22 justify the displayed selected-entry substitution
`x_p = u`, `x_i = u r_i`; the all-pivot residual-block version is
expedition-built finite coordinate bookkeeping.

The full `DLNFibre` build passed via local `lake build` fallback after
environment policy rejected escalated `scripts/lb` access to `$HOME/.lake-shared`.
After a docstring wording repair, the focused
`DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing` build passed.  `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker scan, and direct axiom
probes passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh
source/scope reviewer `Euclid the 4th` and xhigh Lean/API reviewer `Feynman
the 4th` returned PASS.

Nonclaims: no analytic atlas coverage, transition regularity, source
production of successor matrices or suffixes, source-prior transport,
determinant-chart Haar theorem, source-rank coverage, normal-crossing
extraction, pole order, or RLCT.

## 2026-06-29 A2 selected-entry all-pivot source coverage data

Reproduction:
`reproduction-a2-selected-entry-all-pivot-source-coverage-data.md`.
Statement card:
`statement-card-a2-selected-entry-all-pivot-source-coverage-data.md`.
Review:
`review-a2-selected-entry-all-pivot-source-coverage-data.md`.

Lean now packages the existing all-pivot finite selected-entry coverage theorem
as a source-coverage record for a shared universal-domain context:

```text
selectedEntryAllPivotAnalyticAtlasContext
selectedEntryAllPivotAnalyticSourceCoverageData
selectedEntryAllPivotAnalyticSourceCoverage
```

The proof is finite coordinate coverage: choose any pivot for the zero value,
and choose a nonzero coordinate as pivot otherwise.  It reuses
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value`.

Aoyagi prints the displayed top-left selected-entry chart, not an all-pivot
analytic atlas theorem.  This is expedition-built finite coordinate coverage
for the all-pivot certificate only.

Focused build of
`DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotSourceCoverageData` passed via local
`lake build`, and the full `DLNFibre` build passed.  `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker scan, and direct axiom
probes passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh
source/scope reviewer `Wegener the 4th` returned PASS after documentation
repairs; xhigh Lean/API reviewer `Nash the 4th` returned PASS.

Nonclaims: no chart regularity, transition regularity, unit regularity,
Jacobian/volume compatibility, full supplied analytic atlas producer, source
production, branch termination, source-prior transport, determinant-chart Haar
theorem, normal-crossing extraction, pole order, or RLCT.

## 2026-06-29 A2 selected-entry one-chart source-coverage obstruction

Reproduction:
`reproduction-a2-selected-entry-one-chart-source-coverage-obstruction.md`.
Statement card:
`statement-card-a2-selected-entry-one-chart-source-coverage-obstruction.md`.
Review:
`review-a2-selected-entry-one-chart-source-coverage-obstruction.md`.

Lean now proves that the exact one-chart selected-entry context with
`sourceDomain = Set.univ` cannot supply `SelectedEntryAnalyticSourceCoverageData`
when the center has a non-pivot coordinate:

```text
formalChartMap_pivot
formalChartMap_eq_zero_of_fst_eq_zero
not_selectedEntryOneChartAnalyticSourceCoverageData_of_ne
```

The witness is the source-domain point with pivot coordinate `0` and a chosen
non-pivot coordinate `1`.  It cannot lie in the one-chart image, because the
selected-entry chart map sends every pivot-zero chart point to the origin.

Focused build of
`DLNFibre.DLN.Aoyagi.SelectedEntryOneChartSourceCoverageObstruction` passed via
local `lake build` fallback, and the full `DLNFibre` build passed.  `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker scan, and direct axiom
probe passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh
source/scope reviewer `Epicurus the 4th` and xhigh Lean/API reviewer
`Nietzsche the 4th` returned PASS.

Nonclaims: this is only an obstruction for
`selectedEntryOneChartAnalyticAtlasContext pivot`.  It does not rule out source
coverage for a smaller source domain, a multi-pivot atlas, or a supplied
analytic atlas producer.  It proves no source production, branch termination,
source-prior transport, determinant-chart Haar theorem, source-rank coverage,
normal-crossing extraction, pole order, or RLCT.

## 2026-06-29 A2 selected-entry one-chart analytic predicate data

Reproduction:
`reproduction-a2-selected-entry-one-chart-analytic-predicate-data.md`.
Statement card:
`statement-card-a2-selected-entry-one-chart-analytic-predicate-data.md`.
Review:
`review-a2-selected-entry-one-chart-analytic-predicate-data.md`.

Lean now wraps the existing one-chart selected-entry analytic records into the
forgetful predicates used by `SelectedEntryAnalyticAtlasProducer`:

```text
selectedEntryOneChartAnalyticChartRegular
selectedEntryOneChartAnalyticTransitionRegular
selectedEntryOneChartAnalyticUnitRegular
selectedEntryOneChartAnalyticJacobianVolumeCompatible
```

The witnesses are all of the form
`<selectedEntryOneChartAnalyticAtlasContext pivot, <data>>`; the
Jacobian/volume-compatible predicate inherits the positive-radii hypothesis
from `selectedEntryOneChartAnalyticJacobianVolumeData`.

Focused build of
`DLNFibre.DLN.Aoyagi.SelectedEntryOneChartAnalyticPredicateData` passed via
local `lake build` fallback, and the full `DLNFibre` build passed.  `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker scan, and direct axiom
probe passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh
source/scope reviewer `Lorentz the 4th` and xhigh Lean/API reviewer `Harvey
the 4th` returned PASS.

Nonclaims: no source-domain coverage, no full supplied analytic atlas
producer, no source production, no branch termination, no source-prior
transport, no determinant-chart Haar theorem, no source-rank coverage, no
normal-crossing extraction, no pole order, and no RLCT.

## 2026-06-29 A2 selected-entry one-chart regular data

Reproduction:
`reproduction-a2-selected-entry-one-chart-regular-data.md`.
Statement card:
`statement-card-a2-selected-entry-one-chart-regular-data.md`.
Review:
`review-a2-selected-entry-one-chart-regular-data.md`.

Lean now proves one-chart regularity data for the selected-entry context:

```text
continuous_chartPointCoord
continuous_chartPointLossUnit
continuous_chartPointJacobianPriorUnit
selectedEntryOneChartAnalyticChartRegularData
selectedEntryOneChartAnalyticTransitionRegularData
selectedEntryOneChartAnalyticUnitRegularData
```

The chart map is continuous componentwise, the unique coordinate is the pivot
coordinate, the transition data is identity on the single chart, the loss unit
is `1 + sum r_i^2`, and the Jacobian/prior unit is constant `1`.  No positive
radii hypothesis is needed.

Focused build of
`DLNFibre.DLN.Aoyagi.SelectedEntryOneChartRegularData` passed via local
`lake build` fallback, and the full `DLNFibre` build passed.  `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker scan, and direct axiom
probe passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh route
scout `Dirac the 4th` returned PASS; xhigh implementation reviewer `Mill the
4th` returned PASS after two low documentation repairs.

Nonclaims: no source-domain coverage, no multi-pivot analytic transition
regularity, no full analytic atlas producer, no source production, no branch
termination, no source-prior transport, no determinant-chart Haar theorem, no
source-rank coverage, no normal-crossing extraction, no pole order, and no
RLCT.

## 2026-06-29 A2 selected-entry one-chart Jacobian/volume data

Reproduction:
`reproduction-a2-selected-entry-one-chart-jacobian-volume-data.md`.
Statement card:
`statement-card-a2-selected-entry-one-chart-jacobian-volume-data.md`.
Review:
`review-a2-selected-entry-one-chart-jacobian-volume-data.md`.

Lean now proves the finite chart-point volume-form pushforward:

```text
map_formalChartMap_chartPointProductMeasure_withDensity_eq_restrict_image
```

and packages it as one `SelectedEntryAnalyticJacobianVolumeData` record:

```text
selectedEntryOneChartAnalyticAtlasContext
selectedEntryOneChartAnalyticJacobianVolumeData
```

The one-chart context uses the selected-entry normal-crossing certificate with
`sourceDomain = Set.univ` and `chartDomain = Set.univ`.  The data uses source
measure `volume`, chart measure `chartPointProductMeasure pivot R`, density
`ofReal (chartPointDensity pivot x)`, and target
`chartMap pivot '' signedBoxSet R`.  Positive radii are needed for target
nonempty and nonzero restricted source measure fields only; the pushforward
equality has no positivity hypothesis.

Focused builds and full `DLNFibre` build passed; `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker scan, and direct axiom
probes passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh
implementation reviewer `Tesla the 4th` returned PASS.

Nonclaims: no full analytic atlas producer, no source coverage, no transition
regularity, no unit regularity as full analytic data, no source production, no
branch termination, no source-prior transport, no determinant-chart Haar
theorem, no source-rank coverage, no normal-crossing extraction, no pole
order, and no RLCT.

## 2026-06-29 A2 selected-entry chart-point weighted product measure

Reproduction:
`reproduction-a2-selected-entry-chart-point-weighted-product-measure.md`.
Statement card:
`statement-card-a2-selected-entry-chart-point-weighted-product-measure.md`.

Lean now proves the finite weighted product-measure transport for the
selected-entry chart-point adapter:

```text
map_chartPointAdapter_withDensity_sourceDensity_eq_chartPointProductMeasure_withDensity
```

The new chart-point density is

```text
chartPointDensity pivot x = |x.1| ^ ((center.erase pivot.1).card : R).
```

The proof uses
`chartPointDensity_chartPointAdapter_eq_sourceDensity`, measurability of the
chart-point density, the banked unweighted adapter pushforward, and a local
`withDensity` transport lemma.  No positivity hypothesis on radii and no
pivot-nonzero hypothesis are needed.

Focused build of
`DLNFibre.DLN.Aoyagi.SelectedEntryChartPointMeasureBridge` and full
`DLNFibre` build passed via `lean/scripts/lb`; only pre-existing replay
warnings appeared.  Xhigh source-scope scout `Pascal the 4th`, xhigh Lean/API
scout `Descartes the 4th`, and xhigh implementation reviewer `Huygens the
4th` returned PASS.  `scripts/sorries`, `git diff --check`, touched Lean-file
forbidden-marker scan, and direct axiom probes passed with
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no analytic atlas construction, no
`SelectedEntryAnalyticJacobianVolumeData`, no unweighted weighted-measure
collapse, no source-prior transport, no determinant-chart Haar theorem, no
source coverage/source-rank coverage, no transition regularity, no source
production, no normal-crossing extraction, no pole order, and no RLCT.

## 2026-06-29 A2 selected-entry chart-point product measure

Reproduction:
`reproduction-a2-selected-entry-chart-point-product-measure.md`.
Statement card:
`statement-card-a2-selected-entry-chart-point-product-measure.md`.
Review:
`review-a2-selected-entry-chart-point-product-measure.md`.

Lean now proves the natural finite product-measure split for the
selected-entry chart-point adapter:

```text
map_chartPointAdapter_signedBoxMeasure_eq_chartPointProductMeasure
```

The new chart-point product measure is the pivot restricted interval measure
times the erased-center residual product measure.  The proof builds the
measurable split equivalence `chartPointSplitEquiv`, proves it is equal to
`chartPointAdapter`, and uses Mathlib product-measure-preserving equivalences.

Nonclaims: no analytic atlas construction, no
`SelectedEntryAnalyticJacobianVolumeData`, no source-prior transport, no
determinant-chart Haar theorem, no source coverage/source-rank coverage, no
transition regularity, no source production, no normal-crossing extraction, no
pole order, and no RLCT.

## 2026-06-29 A2 selected-entry chart-target nonzero measure

Reproduction:
`reproduction-a2-selected-entry-chart-target-nonzero.md`.
Statement card:
`statement-card-a2-selected-entry-chart-target-nonzero.md`.
Review:
`review-a2-selected-entry-chart-target-nonzero.md`.

Lean now proves fixed-pivot nonzero target/source measure facts for the
selected-entry signed-box chart under positive radii `forall i, 0 < R i`.

In `DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure`, the new inner target
box is:

```text
chartMapTargetInnerBox pivot R
```

with pivot interval `(R pivot / 2, R pivot)` and non-pivot intervals
`(-(R pivot * R i / 4), R pivot * R i / 4)`.  Lean proves:

```text
isOpen_chartMapTargetInnerBox,
chartMapTargetInnerBox_nonempty,
chartMapTargetInnerBox_subset_chartMap_image_signedBoxSet,
volume_chartMap_image_signedBoxSet_ne_zero,
volume_restrict_chartMap_image_signedBoxSet_ne_zero,
volume_chartMap_image_signedBoxSet_inter_pivot_ne_zero_ne_zero,
volume_restrict_chartMap_image_signedBoxSet_inter_pivot_ne_zero_ne_zero,
signedBoxMeasure_withDensity_sourceDensity_ne_zero,
restrict_nonzeroSignedBox_withDensity_sourceDensity_ne_zero.
```

In `DLNFibre.DLN.Aoyagi.SelectedEntryChartPointMeasureBridge`, Lean proves:

```text
map_chartPointAdapter_weightedSignedBox_ne_zero,
map_formalChartMap_map_chartPointAdapter_weightedSignedBox_ne_zero.
```

The proof is finite coordinate geometry plus the already-proved selected-entry
Jacobian pushforward theorem.  Focused builds of both touched modules passed
via `scripts/lb`; only pre-existing replay warnings appeared.  Xhigh
source-scope scout `Einstein the 4th` and xhigh Lean/API scout `Beauvoir the
4th` returned PASS.  Xhigh implementation reviewer `Kuhn the 4th` returned
PASS.  Full `DLNFibre` build, `scripts/sorries`, `git diff --check`, touched
Lean-file marker scan, and direct axiom probes passed; the new headline
theorems report `[propext, Classical.choice, Quot.sound]`.

Nonclaims: no analytic atlas construction, no
`SelectedEntryAnalyticJacobianVolumeData`, no natural chart-point product
measure, no source-prior transport, no determinant-chart Haar theorem, no
raw/source Haar theorem, no source coverage, no source-rank coverage, no
transition regularity, no source production, no branch termination, no
normal-crossing extraction, no pole order, and no RLCT.

## 2026-06-29 A2 selected-entry chart-point measure bridge

Reproduction:
`reproduction-a2-selected-entry-chart-point-measure-bridge.md`.
Statement card:
`statement-card-a2-selected-entry-chart-point-measure-bridge.md`.
Review:
`review-a2-selected-entry-chart-point-measure-bridge.md`.

Lean now exposes a small leaf module:

```text
DLNFibre.DLN.Aoyagi.SelectedEntryChartPointMeasureBridge
```

It defines the syntactic one-chart normal-crossing chart-point type

```text
FormalChartPoint pivot = R x (center.erase pivot -> R)
```

and the adapter

```text
chartPointAdapter pivot y = (y pivot, y restricted to center.erase pivot).
```

It proves continuity and measurability of the adapter and exposed certificate
chart map, the pointwise bridge

```text
formalChartMap pivot (chartPointAdapter pivot y)
  = SelectedEntrySignedBox.CenterCoord.chartMap pivot y,
```

and the compatibility facts

```text
coord_chartPointAdapter_eq,
lossUnit_chartPointAdapter_eq_residualUnit,
abs_jacobianPrior_chartPointAdapter_eq_sourceDensity.
```

The measure theorems

```text
map_formalChartMap_comp_chartPointAdapter_weightedSignedBox_eq_restrict_image
map_formalChartMap_map_chartPointAdapter_weightedSignedBox_eq_restrict_image
```

restate the existing signed-box weighted pushforward through the chart-point
adapter.  The two-stage equality uses `Measure.map_map` because both maps are
globally measurable.

Focused build of
`DLNFibre.DLN.Aoyagi.SelectedEntryChartPointMeasureBridge` and full
`DLNFibre` build passed via `scripts/lb`; only pre-existing replay warnings
appeared.  Xhigh source-scope scout `Euler the 4th` and xhigh Lean/API scout
`Halley the 4th` returned PASS.  Xhigh implementation reviewer
`Ptolemy the 4th` returned PASS after two process fixes, both addressed.
`scripts/sorries`, `git diff --check`, touched Lean-file forbidden-marker scan,
and direct axiom probes passed with `[propext, Classical.choice, Quot.sound]`.

Nonclaims: no analytic atlas construction, no
`SelectedEntryAnalyticJacobianVolumeData`, no original source-prior transport,
no determinant-chart Haar theorem, no raw/source Haar theorem, no retained-
passive passive Jacobian, no source-image or source-rank coverage, no
transition regularity, no source production, no branch termination, no
normal-crossing extraction, no pole order, and no RLCT.

## 2026-06-29 A2 retained-passive raw-order two-stage pushforward

Reproduction:
`reproduction-a2-retained-passive-raw-order-two-stage-pushforward.md`.
Statement card:
`statement-card-a2-retained-passive-raw-order-two-stage-pushforward.md`.
Review:
`review-a2-retained-passive-raw-order-two-stage-pushforward.md`.

Lean now exposes:

```text
exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_rawOrderMap_twoStage_eq_sourceChart_inverseReadout_eq_snd
```

The theorem defines

```text
rawMap z = topologyTupleEdgeRawOrder (topologyTuple (retainedData z))
```

and `rawChart` as the public raw-order p.13 source chart.  It returns the same
open punctured-sector shape as the topology-tuple bridge and the one-stage
measure factorization.  For every `z in V`, it proves raw-order
source-recursive determinant-chart membership, equality
`rawChart (rawMap z) = sourceChart z`, pointwise local-source membership,
source-readback recovery of `retainedData z`, and
`inverseReadout (sourceChart z) = z.2`.

For arbitrary `sourceMeasure`, and under Borel measurable structures on the
raw-order topology-tuple target and edge-family target, the measure conclusions
are:

```text
Measure.map (fun z => rawChart (rawMap z)) (sourceMeasure.restrict V)
  = Measure.map sourceChart (sourceMeasure.restrict V),

Measure.map rawChart
    (Measure.map rawMap (sourceMeasure.restrict V))
  = Measure.map sourceChart (sourceMeasure.restrict V).
```

The proof is local a.e. measurability and measure functoriality.  `rawMap` is
continuous on the returned sector through the determinant-chart subtype.
`rawChart` is a.e. measurable after pushing raw-order target support to the
intermediate measure and restricting to the raw-order source-recursive
determinant-chart target.  The proof uses `AEMeasurable.map_map_of_aemeasurable`,
not global `Measure.map_map`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasure`
and full `DLNFibre` build passed via `scripts/lb`; only pre-existing replay
warnings appeared.  `scripts/sorries`, `git diff --check`, touched Lean-file
forbidden-marker scan, and direct axiom probe passed with
`[propext, Classical.choice, Quot.sound]`.  Xhigh source-scope review by
`Boyle the 4th` and xhigh Lean/API review by `Carver the 4th` returned PASS.

Nonclaims: no determinant-chart Haar transport, raw/source Haar theorem,
external/original source-prior comparison, passive Jacobian formula, density
identity, local domination for arbitrary `sourceMeasure`, source-image
equality, source-rank coverage, normal crossings, pole order, or RLCT.  No
downstream intermediate-measure consumer is named yet, so treat this as API
hardening rather than removal of a source-prior or analytic frontier.

## 2026-06-29 A2 retained-passive raw-order composite measure factorization

Reproduction:
`reproduction-a2-retained-passive-raw-order-map-factorization.md`.
Statement card:
`statement-card-a2-retained-passive-raw-order-map-factorization.md`.
Review:
`review-a2-retained-passive-raw-order-map-factorization.md`.

Lean now exposes:

```text
exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_rawOrderMap_comp_eq_sourceChart_inverseReadout_eq_snd
```

The theorem defines

```text
rawMap z = topologyTupleEdgeRawOrder (topologyTuple (retainedData z))
```

and `rawChart` as the public raw-order p.13 source chart.  It returns an open
punctured sector `V` containing the basepoint.  For every `z in V`, it proves
raw-order source-recursive determinant-chart membership, equality
`rawChart (rawMap z) = sourceChart z`, pointwise local-source membership,
source-readback recovery of `retainedData z`, and
`inverseReadout (sourceChart z) = z.2`.

For arbitrary `sourceMeasure`, the measure conclusion is the one-stage
composite equality:

```text
Measure.map (fun z => rawChart (rawMap z)) (sourceMeasure.restrict V)
  = Measure.map sourceChart (sourceMeasure.restrict V).
```

This is proved by `Measure.map_congr` from the pointwise sector bridge.  It is
not the two-stage equality through
`Measure.map rawChart (Measure.map rawMap ...)`, and it does not retain the
earlier theorem's local-source support or inverse-readout pushforward fields.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasure`
and full `DLNFibre` build passed via `scripts/lb`.  `scripts/sorries`,
`git diff --check`, touched-file forbidden-marker scan, and direct axiom probe
passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh source-scope
review by `Sagan the 4th`, xhigh Lean/API review by `Popper the 4th`, and
xhigh implementation review by `Volta the 4th` returned PASS after a
documentation scope repair.

Nonclaims: no determinant-chart Haar transport, raw/source Haar theorem,
external/original source-prior comparison, passive Jacobian formula, density
identity, source-image equality, source-rank coverage, normal crossings, pole
order, or RLCT.

## 2026-06-29 A2 retained-passive topology-tuple punctured-sector transport

Reproduction:
`reproduction-a2-retained-passive-topology-tuple-punctured-sector-transport.md`.
Statement card:
`statement-card-a2-retained-passive-topology-tuple-punctured-sector-transport.md`.
Review:
`review-a2-retained-passive-topology-tuple-punctured-sector-transport.md`.

Lean now exposes:

```text
exists_open_case2EndpointTransport_withPassive_topologyTuple_rawOrderSourceChart_eq_sourceChart_puncturedSector_inverseReadout_eq
```

The theorem returns an open punctured determinant sector `V` containing the
basepoint.  For every `z in V`, it proves topology-tuple determinant-chart
membership for `topologyTuple (retainedData z)`, raw-order source-recursive
determinant-chart membership for its `topologyTupleEdgeRawOrder` image,
equality of the raw-order p.13 source chart with the direct chart-produced
source family, source-readback recovery of `retainedData z`, and
`inverseReadout (sourceChart z) = z.2`.

This is repo-local topology/raw-order source-chart packaging around already
reproduced Aoyagi p.13 and Case 2 selected-entry formulas.  Xhigh source-scope
review by `Laplace the 4th`, xhigh Lean/API review by `Locke the 4th`, and
xhigh implementation review by `Singer the 4th` returned PASS.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySource` passed via
`scripts/lb`.  `scripts/sorries`, `git diff --check`, touched Lean-file
forbidden-marker scan, and direct axiom probe passed with
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no source-image equality, source-rank coverage, determinant-chart
Haar transport, raw/source Haar theorem, external/original source-prior
comparison, measure pushforward theorem, Jacobian formula, normal crossings,
pole order, or RLCT.

## 2026-06-29 A2 retained-passive chart-produced punctured-sector bounded-density residual source

Reproduction:
`reproduction-a2-retained-passive-chart-produced-punctured-sector-bounded-density-residual-source.md`.
Statement card:
`statement-card-a2-retained-passive-chart-produced-punctured-sector-bounded-density-residual-source.md`.
Review:
`review-a2-retained-passive-chart-produced-punctured-sector-bounded-density-residual-source.md`.

Lean now exposes the reusable measure helper:

```text
restrict_withDensity_le_smul_of_ae_le
```

and the Aoyagi wrapper:

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_of_withDensity_ae_le_const_passiveProductMeasure_finiteMass
```

The theorem sets `sourceMeasure = passiveSource.withDensity sourceDensity`,
where `passiveSource = passiveMeasure.prod weightedBox`.  It calls the banked
local-domination socket to choose the open punctured sector `V`.  For
`mu = Measure.map sourceChart ((passiveSource.withDensity sourceDensity).restrict V)`,
it proves `mu.restrict localSource = mu` without any density bound.  Under
`c < infinity` and
`sourceDensity <= c` a.e. with respect to `passiveSource.restrict V`, it
derives the local domination
`(passiveSource.withDensity sourceDensity).restrict V <= c • passiveSource`
and transfers retained-passive residual positivity and negative-power
integrability from the socket.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff`
and full `DLNFibre` build passed via `scripts/lb`.  `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker scan, and direct axiom
probes passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh route
review by `McClintock the 4th` and xhigh post-implementation review by
`Kierkegaard the 4th` returned PASS.

Nonclaims: no proof that an external/original source prior admits the supplied
density or local bound, no determinant-chart Haar transport, raw/source Haar
theorem, passive Jacobian formula, source-image equality, source-rank
coverage, normal crossings, pole order, or RLCT.

## 2026-06-29 A2 retained-passive chart-produced punctured-sector local-domination residual source

Reproduction:
`reproduction-a2-retained-passive-chart-produced-punctured-sector-local-domination-residual-source.md`.
Statement card:
`statement-card-a2-retained-passive-chart-produced-punctured-sector-local-domination-residual-source.md`.
Review:
`review-a2-retained-passive-chart-produced-punctured-sector-local-domination-residual-source.md`.

Lean now exposes:

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_of_restrict_le_smul_passiveProductMeasure_finiteMass
```

The theorem keeps `sourceMeasure` arbitrary.  It calls the residual-source
socket to choose the open punctured sector `V`.  For
`mu = Measure.map sourceChart (sourceMeasure.restrict V)`, it proves
`mu.restrict localSource = mu` without the local domination assumption.  Under
`sourceMeasure.restrict V <= c • (passiveMeasure.prod weightedBox)` and
`c < infinity`, it transfers raw selected-entry residual positivity and
negative-power integrability to the residual marginal and then feeds those
facts to the socket.

The proof uses two domination transfers: finite passive mass transfers the raw
selected-entry facts from `weightedBox` to
`Measure.map Prod.snd (passiveMeasure.prod weightedBox)`, and the local
source-domain domination maps through `Prod.snd` to transfer those facts to
`Measure.map Prod.snd (sourceMeasure.restrict V)`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff`
and full `DLNFibre` build passed via `scripts/lb`.  `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker scan, and direct axiom
probe passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh
post-implementation review by `Einstein the 3rd` returned PASS.

Nonclaims: no proof that an external/original source prior satisfies the local
domination field, no determinant-chart Haar transport, raw/source Haar theorem,
passive Jacobian formula, source-image equality, source-rank coverage, normal
crossings, pole order, or RLCT.

## 2026-06-29 A2 retained-passive chart-produced punctured-sector passive-product residual source

Reproduction:
`reproduction-a2-retained-passive-chart-produced-punctured-sector-passive-product-residual-source.md`.
Statement card:
`statement-card-a2-retained-passive-chart-produced-punctured-sector-passive-product-residual-source.md`.
Review:
`review-a2-retained-passive-chart-produced-punctured-sector-passive-product-residual-source.md`.

Lean now exposes:

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_passiveProductMeasure_finiteMass
```

The theorem specializes the residual-source socket to
`sourceMeasure = passiveMeasure.prod weightedBox`, where `weightedBox` is the
raw selected-entry signed box with Aoyagi's source density.  The socket chooses
the open punctured sector `V`; domination of
`Measure.map Prod.snd ((passiveMeasure.prod weightedBox).restrict V)` by
`passiveMeasure Set.univ • weightedBox`, plus finite passive mass, transfers
the raw selected-entry residual positivity and negative-power integrability
from `weightedBox` to the sector marginal.  The socket then gives
`mu.restrict localSource = mu`, retained-passive residual positivity a.e., and
`residualNegPowerIntegrableOn localSource mu t` for the chart-produced source
measure.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff`
and full `DLNFibre` build passed via `scripts/lb`.  `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker scan, and direct axiom
probe passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh route
review by `Cicero the 3rd` and implementation review by `Epicurus the 3rd`
returned PASS.

Nonclaims: no equality of the restricted residual marginal with the
unrestricted product marginal, no determinant-chart Haar transport, raw/source
Haar theorem, external/original source-prior comparison, passive Jacobian
formula, source-image equality, source-rank coverage, normal crossings, pole
order, or RLCT.

## 2026-06-29 A2 retained-passive chart-produced punctured-sector residual-source socket

Reproduction:
`reproduction-a2-retained-passive-chart-produced-punctured-sector-residual-source-socket.md`.
Statement card:
`statement-card-a2-retained-passive-chart-produced-punctured-sector-residual-source-socket.md`.
Review:
`review-a2-retained-passive-chart-produced-punctured-sector-residual-source-socket.md`.

Lean now exposes:

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_marginal
```

The theorem is a chart-produced residual-source socket for the previously
proved punctured-sector inverse-readout map identity.  It chooses the same kind
of open determinant-and-pivot-nonzero sector `V`, defines
`mu = Measure.map sourceChart (sourceMeasure.restrict V)` and
`marginal = Measure.map Prod.snd (sourceMeasure.restrict V)`, then proves
`mu.restrict localSource = mu` and transfers explicit marginal residual
positivity and finite negative-power integrability to the retained-passive
p.13 source residual hypotheses.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff`
and full `DLNFibre` build passed via `scripts/lb`.  `scripts/sorries`,
`git diff --check`, the added Lean-line forbidden-marker scan, and direct axiom
probe passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh read-only
review by `Harvey the 3rd` returned PASS.

Nonclaims: no marginal positivity/integrability for arbitrary `sourceMeasure`,
determinant-chart Haar transport, raw/source Haar theorem, external/original
source-prior comparison, passive Jacobian formula, selected-entry source-image
equality, source-rank coverage, normal crossings, pole order, or RLCT.

## 2026-06-29 A2 retained-passive chart-produced punctured-sector measure readout

Reproduction:
`reproduction-a2-retained-passive-chart-produced-punctured-sector-measure-readout.md`.
Statement card:
`statement-card-a2-retained-passive-chart-produced-punctured-sector-measure-readout.md`.
Review:
`review-a2-retained-passive-chart-produced-punctured-sector-measure-readout.md`.

Lean now exposes:

```text
exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_eq_snd
```

and the selected-entry helper:

```text
SelectedEntrySignedBox.CenterCoord.measurable_preimageOfPivotNeZero
```

The theorem restricts an arbitrary coordinate-domain measure to the open
determinant-and-pivot-nonzero sector, pushes it forward by the retained-
passive source chart, and proves that the source-side inverse residual
readout pushes the resulting chart-produced measure back to the residual
coordinate marginal.  The same chart-produced pushforward is supported on the
retained-passive p.13 local source.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasure`
and full `DLNFibre` build passed via `scripts/lb`.  `scripts/sorries`,
`git diff --check`, the touched Lean-file forbidden-marker scan, and direct
axiom probes passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh
read-only review by `Hubble the 3rd` returned PASS.

Nonclaims: no determinant-chart Haar transport, raw/source Haar theorem,
external/original source-prior comparison, passive Jacobian formula,
selected-entry source-image equality, source-rank coverage, normal crossings,
pole order, or RLCT.

## 2026-06-29 A2 retained-passive open punctured-sector readout

Reproduction:
`reproduction-a2-retained-passive-open-punctured-sector-readout.md`.
Statement card:
`statement-card-a2-retained-passive-open-punctured-sector-readout.md`.
Review:
`review-a2-retained-passive-open-punctured-sector-readout.md`.

Lean now exposes:

```text
exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq_preimageOfPivotNeZero_residualReadout_eq
```

The theorem is the first Lean subtarget identified by the passive-variable
sector frontier.  It reuses the open determinant-domain source-readback
package, then proves that on the nonzero selected-pivot sector the
selected-entry inverse of the residual readout of `sourceReadback E` recovers
the original selected-entry residual coordinate vector `z.2`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySource` passed via
`scripts/lb`, and the full `DLNFibre` aggregator build also passed.  Only
pre-existing replay warnings from unrelated modules appeared.  Xhigh read-only
review by `Anscombe the 3rd` returned PASS.  `git diff --check`,
`scripts/sorries`, the touched Lean-file forbidden-marker scan, and the direct
axiom probe passed; the new theorem reports
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no measure equality, determinant-chart Haar transport,
external/original source-prior comparison, selected-entry source-image
equality, source-rank coverage, normal crossings, pole order, or RLCT.

## 2026-06-29 A2 retained-passive passive-variable sector transport frontier

Reproduction:
`reproduction-a2-retained-passive-passive-variable-sector-transport.md`.
Statement card:
`statement-card-a2-retained-passive-passive-variable-sector-transport.md`.
Review:
`review-a2-retained-passive-passive-variable-sector-transport.md`.

This is a reviewed frontier specification, not a new Lean theorem.  It
separates the passive-variable-explicit source-measure problem from the
reduced selected-entry chart-produced finite-integral lane.  The correct
coordinate domain is a product of retained passive variables and selected-entry
residual coordinates; the raw passive variables are typed over
`case2PostPivotTwoEdgeDomain ...` and are transported by endpoint equivalences
to the fixed-base endpoint complement indices.

The source check confirmed the Aoyagi pp. 10-13 formulas: Lemma 2 has
`F2 = -A1^{-1} A2`, `F3 = -A3 A1^{-1}`, and
`C4 = -A3 A1^{-1} A2 + A4`; Theorem 3 has the displayed induction formulas;
and the p.13 lower-right block is `prod_s C^(s) - F3 F2`.  The Lean/API check
confirmed the current inputs and sharpened the next subtarget: a combined
with-passive open punctured-sector inverse/readout package, using the open
source-readback theorem, the with-passive endpoint residual-factor chart-map
identity, the existing passive pointwise residual readout theorem, and
`SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero_chartMap`.

Nonclaims: no passive-sector Haar transport, determinant-chart Haar
comparison for the reduced selected-entry section, external/original
source-prior comparison, selected-entry source-image equality, source-rank
coverage, normal crossings, pole order, or RLCT.

## 2026-06-29 A2 retained-passive source-prior coordinate-domain frontier

Reproduction:
`reproduction-a2-retained-passive-source-prior-coordinate-domain.md`.
Review:
`review-a2-retained-passive-source-prior-coordinate-domain.md`
passed by xhigh read-only checker `Noether the 3rd`.

This is a frontier clarification, not a new Lean theorem.  The note separates
three statements that must not be conflated:

```text
full retained-passive determinant-chart COV
passive selected-entry chart-produced measure
external/original source-prior comparison
```

Aoyagi pp. 10-13 support the Schur/product algebra, retained-passive
coordinate inverse, and p.13 product-difference variables.  They do not by
themselves identify the reduced selected-entry signed-box measure with full
determinant-chart Haar measure or with an external DLN source prior.

The next Lean theorem in this lane should remove a named field or construct a
precise sector/source-prior comparison.  Acceptable shapes are a
passive-variable-explicit sector transport theorem, a mutually absolutely
continuous external-prior comparison with explicit density, or a downstream
consumer rewritten over the chart-produced passive sector measure without a
hidden `hmap`/Haar hypothesis.  Do not add another finite-integral wrapper
unless it removes one of those fields.

## 2026-06-29 A2 Case 2 passive Jacobian-weighted source-stratum bounds finite integral

Reproduction:
`reproduction-a2-case2-passive-jacobian-weighted-source-stratum-bounds-finite-integral.md`.
Statement card:
`statement-card-a2-case2-passive-jacobian-weighted-source-stratum-bounds-finite-integral.md`.

Lean now exposes:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass_sourceStratum_bounds
```

The theorem is the source-stratum-bound analogue of the banked passive
Jacobian-weighted local-source finite-integral handoff.  It constructs the
same source-domain determinant neighborhood `Udom`, forms the same
chart-produced Jacobian-weighted pushforward `muJ`, and proves a finite
regular-coordinate integral over
`(muJ.restrict (U ∩ sourceStratum)).prod ν`.  The three loss/density
comparison hypotheses now live on `nhdsWithin base sourceStratum`; residual
positivity and negative-power integrability remain supplied on the
retained-passive local source.

The proof consumes the residual-source theorem, derives `SFinite muJ` from
finite passive mass, gets the retained-passive local-source coverage open at
the fixed base, and applies the generic
source-stratum-bounds/local-source finite-integral consumer.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.  Full
`DLNFibre` aggregator build passed.  `git diff --check`, `scripts/sorries`,
and direct axiom probe passed with
`[propext, Classical.choice, Quot.sound]`.  Xhigh reviews by
`Bernoulli the 3rd` and `Kant the 3rd` returned PASS after a docstring
nonclaim-boundary repair.  Review:
`review-a2-case2-passive-jacobian-weighted-source-stratum-bounds-finite-integral.md`.

Nonclaims: no exact localized residual marginal, determinant-chart Haar
pushforward, raw/source Haar theorem, original source-prior transport,
source-prior Jacobian formula, source-image equality, source-rank coverage,
normal crossings, pole order, or RLCT.

## 2026-06-29 A2 Case 2 passive Jacobian-weighted local-source finite integral

Reproduction:
`reproduction-a2-case2-passive-jacobian-weighted-local-source-finite-integral.md`.
Statement card:
`statement-card-a2-case2-passive-jacobian-weighted-local-source-finite-integral.md`.
Review:
`review-a2-case2-passive-jacobian-weighted-local-source-finite-integral.md`.

Lean now exposes:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass
```

The theorem consumes the Jacobian-weighted residual-source theorem and the
generic retained-passive local-source finite-integral handoff.  It constructs
a source-domain determinant neighborhood `Udom`, defines the chart-produced
Jacobian-weighted pushforward `muJ`, and then obtains an edge-family open
neighborhood `U` with finite regular-coordinate integral over
`(muJ.restrict (U ∩ sourceStratum)).prod ν`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.  Full
`DLNFibre` aggregator build passed.  `git diff --check`, `scripts/sorries`,
and direct axiom probe passed with
`[propext, Classical.choice, Quot.sound]`.  Xhigh reviews by `Erdos the 3rd`
and `Lovelace the 3rd` returned PASS.

Nonclaims: no exact localized residual marginal, determinant-chart Haar
pushforward, raw/source Haar theorem, original source-prior transport,
source-prior Jacobian formula, source-image equality, local coverage, normal
crossings, pole order, or RLCT.

## 2026-06-29 A2 Case 2 passive Jacobian-weighted residual source hypotheses

Reproduction:
`reproduction-a2-case2-passive-jacobian-weighted-residual-source-hypotheses.md`.
Statement card:
`statement-card-a2-case2-passive-jacobian-weighted-residual-source-hypotheses.md`.
Review:
`review-a2-case2-passive-jacobian-weighted-residual-source-hypotheses.md`.

Lean now exposes:

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass
```

The theorem packages the already proved Jacobian-weighted passive residual
positivity and finite lintegral result into the retained-passive local-source
socket.  It reindexes the selected-entry `center` residual coordinate square
sum to the native fixed-base residual-coordinate square sum and rewrites
`muJ.restrict localSource = muJ` using chart-produced support.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.  Full
`DLNFibre` aggregator build passed.  `git diff --check`, `scripts/sorries`,
and direct axiom probe passed.  Xhigh reviews by `Dirac the 3rd` and
`Hegel the 3rd` returned PASS.

Nonclaims: no exact localized residual marginal, determinant-chart Haar
pushforward, raw/source Haar theorem, original source-prior transport,
source-prior Jacobian formula, source-image equality, local coverage, normal
crossings, pole order, or RLCT.

## 2026-06-29 A2 Case 2 passive selected-entry weighted local source support after open restriction

Reproduction:
`reproduction-a2-case2-passive-selected-entry-weighted-local-source-support-after-open-restriction.md`.
Statement card:
`statement-card-a2-case2-passive-selected-entry-weighted-local-source-support-after-open-restriction.md`.
Review:
`review-a2-case2-passive-selected-entry-weighted-local-source-support-after-open-restriction.md`.

Lean now exposes:

```text
exists_open_measure_map_case2EndpointTransport_withPassive_withDensity_restrict_retainedPassiveP13LocalSource_eq_self
```

The theorem reuses the open determinant-domain source/readback package.  For
any source-domain measure and any density, after restricting the measure to
the constructed open neighborhood `U` and then applying `withDensity`, the
fixed-base p.13 source-chart pushforward is supported on the retained-passive
p.13 local source.  The proof transfers a.e. measurability and a.e. local-
source membership from `sourceMeasure.restrict U` to the weighted measure via
`withDensity_absolutelyContinuous`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasure`
passed.  Full `DLNFibre` aggregator build passed.  `git diff --check`,
`scripts/sorries`, and direct axiom probe passed.  Xhigh reviews by
`Nietzsche the 3rd` and `Schrodinger the 3rd` returned PASS.

Nonclaims: no Jacobian identification, global determinant-chart membership,
selected-entry source-image equality, local coverage, source-rank support or
coverage, determinant-chart Haar pushforward, raw/source Haar transport,
source-prior comparison, exact localized residual marginal, normal crossings,
pole order, or RLCT.

## 2026-06-29 A2 Case 2 passive selected-entry local source support after open restriction

Reproduction:
`reproduction-a2-case2-passive-selected-entry-local-source-support-after-open-restriction.md`.
Statement card:
`statement-card-a2-case2-passive-selected-entry-local-source-support-after-open-restriction.md`.

Lean now exposes:

```text
exists_open_measure_map_case2EndpointTransport_withPassive_restrict_retainedPassiveP13LocalSource_eq_self
```

The theorem reuses the open determinant-domain source/readback package.  For
any source-domain measure, after restricting the measure to the constructed
open neighborhood `U`, the fixed-base p.13 source-chart pushforward is
supported on the retained-passive p.13 local source.  The proof derives
a.e. measurability of the source chart on `sourceMeasure.restrict U` via
`ContinuousOn` on the determinant-domain subtype; it is not assumed.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasure`
passed.  Full `DLNFibre` aggregator build passed.  `git diff --check`,
`scripts/sorries`, and direct axiom probe passed.  Xhigh reviews by
`Singer the 3rd` and `Descartes the 3rd` returned PASS after one stale
reproduction-note wording repair.  Review:
`review-a2-case2-passive-selected-entry-local-source-support-after-open-restriction.md`.

Nonclaims: no global determinant-chart membership, selected-entry source-image
equality, local coverage, source-rank support or coverage, determinant-chart
Haar pushforward, raw/source Haar transport, source-prior comparison, Jacobian
transport, exact localized residual marginal, normal crossings, pole order, or
RLCT.

## 2026-06-29 A2 Case 2 passive selected-entry local source-readback domain

Reproduction:
`reproduction-a2-case2-passive-selected-entry-local-source-readback-domain.md`.
Statement card:
`statement-card-a2-case2-passive-selected-entry-local-source-readback-domain.md`.

Lean now exposes:

```text
exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq
```

The theorem constructs an open neighborhood of a passive selected-entry
basepoint by pulling back the retained-passive topology-tuple determinant
chart.  On this neighborhood, the endpoint-transported fixed-base p.13 source
chart lies in the retained-passive local source and source readback recovers
the full transported retained-passive datum.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySource` passed.
Full `DLNFibre` aggregator build passed.  `git diff --check`,
`scripts/sorries`, and direct axiom probe passed.  Xhigh reviews by
`McClintock the 3rd` and `Galileo the 3rd` returned PASS.  Review:
`review-a2-case2-passive-selected-entry-local-source-readback-domain.md`.

Nonclaims: no selected-entry source-image equality, local coverage,
source-rank coverage, determinant-chart Haar pushforward, raw/source Haar
transport, source-prior comparison, Jacobian transport, exact localized
residual marginal, normal crossings, pole order, or RLCT.

## 2026-06-29 A2 Case 2 passive Jacobian-weighted residual integrability

Reproduction:
`reproduction-a2-case2-passive-jacobian-weighted-residual-integrability.md`.
Statement card:
`statement-card-a2-case2-passive-jacobian-weighted-residual-integrability.md`.
Review:
`review-a2-case2-passive-jacobian-weighted-residual-integrability.md`.

Lean now exposes:

```text
ae_of_measure_le_smul
lintegral_lt_top_of_measure_le_smul
map_le_smul_map_of_le_smul
measure_le_smul_of_le_smul_restrict
exists_open_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass
```

The Case 2 theorem combines the local Jacobian `withDensity` upper sandwich
with the global passive finite-mass residual theorem.  It proves residual
square-sum positivity a.e. and finite negative-power lintegral for

```text
Measure.map sourceChart
  ((sourceMeasure.restrict U).withDensity (fun z => ofReal (J z))).
```

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.
`git diff --check`, `scripts/sorries`, and direct axiom probes passed.
Archimedes the 3rd xhigh read-only review found only two stale module-doc
boundary comments; both were fixed.

Nonclaims: no exact localized residual marginal, determinant-chart Haar
pushforward, raw/source Haar transport, source-prior comparison,
source-image coverage, local inverse/coverage, normal crossings, pole order,
or RLCT.

## 2026-06-29 A2 Case 2 passive residual finite-mass integrability

Reproduction:
`reproduction-a2-case2-passive-residual-finite-mass-integrability.md`.
Statement card:
`statement-card-a2-case2-passive-residual-finite-mass-integrability.md`.

Lean now exposes:

```text
residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_finiteMass
```

This theorem transfers residual positivity a.e. and finite negative-power
lintegral from the selected-entry chart-image measure to the passive
chart-produced source measure.  It relies on the global residual marginal and
therefore assumes `passiveMeasure Set.univ < infinity`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.
Aristotle the 3rd xhigh read-only review returned PASS.  `git diff --check`,
`scripts/sorries`, and direct axiom probe passed.

Nonclaims: no determinant-chart Haar pushforward, raw/source Haar transport,
source-prior comparison, selected-entry image coverage, arbitrary-localized
residual marginal, local inverse/coverage, normal crossings, pole order, or
RLCT.

## 2026-06-29 A2 Case 2 passive Jacobian withDensity sandwich

Reproduction:
`reproduction-a2-case2-passive-jacobian-withdensity-sandwich.md`.
Statement card:
`statement-card-a2-case2-passive-jacobian-withdensity-sandwich.md`.

Lean now exposes:

```text
withDensity_ofReal_sandwich_of_ae_bounds
exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure
```

The generic helper turns a.e. real lower/upper density bounds into a
`withDensity` measure sandwich.  The Case 2 theorem applies it to the
retained-passive solved-`A1` product raw-order Jacobian density on the
restricted concrete passive product-domain measure.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.
Aristotle the 3rd xhigh read-only review returned PASS.  `git diff --check`,
`scripts/sorries`, and direct axiom probes passed.

Nonclaims: no determinant-chart Haar pushforward, raw/source Haar transport,
source-prior comparison, selected-entry image coverage, source-rank coverage,
local inverse/coverage, normal crossings, pole order, or RLCT.

## 2026-06-29 A2 Case 2 passive Jacobian product bounded-unit a.e. handoff

Reproduction:
`reproduction-a2-case2-passive-jacobian-product-bounded-unit-ae-handoff.md`.
Statement card:
`statement-card-a2-case2-passive-jacobian-product-bounded-unit-ae-handoff.md`.

Lean now exposes:

```text
exists_open_ae_restrict_of_eventually_nhds
exists_pos_open_ae_restrict_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure_bounds
```

The Case 2 theorem turns the previously banked local passive Jacobian
bounded-unit theorem into an a.e. statement for the concrete passive
product-domain measure restricted to a small open neighborhood of the base
point.  It makes no positive-mass, support, rank, source-image, or source-prior
transport claim.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.
Heisenberg the 3rd xhigh read-only review returned PASS.  `git diff --check`,
`scripts/sorries`, and direct axiom probes passed.

Nonclaims: no determinant-chart Haar pushforward, raw/source Haar transport,
source-prior comparison, selected-entry image coverage, source-rank coverage,
local inverse/coverage, positive-mass/support assertion, normal crossings,
pole order, or RLCT.

## 2026-06-29 A2 Case 2 passive Jacobian product bounded unit

Reproduction:
`reproduction-a2-case2-passive-jacobian-product-bounded-unit.md`.
Statement card:
`statement-card-a2-case2-passive-jacobian-product-bounded-unit.md`.
Review:
`review-a2-case2-passive-jacobian-product-bounded-unit.md`.

Lean now exposes:

```text
exists_pos_eventually_bounds_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive
```

This theorem composes the generic retained-passive determinant-chart
bounded-unit theorem with the endpoint-transported passive Case 2 selected-
entry coordinate map.  It needs continuity of the passive fields and basepoint
determinant-unit hypotheses for `Ctop` and passive `A1`; it concludes positive
lower and upper bounds eventually near the chosen point.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.
`git diff --check`, `scripts/sorries`, and direct axiom probe passed.
Leibniz the 3rd xhigh review returned PASS with no findings.

Nonclaims: no determinant-chart Haar pushforward, raw/source Haar transport,
source-prior comparison, selected-entry image coverage, source-rank coverage,
local inverse/coverage, normal crossings, pole order, or RLCT.

## 2026-06-29 A2 Case 2 passive residual-coordinate product-measure pushforward

Reproduction:
`reproduction-a2-case2-passive-residual-coordinate-product-measure-pushforward.md`.
Statement card:
`statement-card-a2-case2-passive-residual-coordinate-product-measure-pushforward.md`.
Review:
`review-a2-case2-passive-residual-coordinate-product-measure-pushforward.md`.

Lean now exposes:

```text
measure_map_residualBlockCoordinateMap_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_eq_smul_restrict_chartMap_image
```

This theorem maps the concrete passive product-domain chart-produced source
measure through the fixed-base residual-coordinate map.  The result is the
selected-entry chart-image measure scaled by `passiveMeasure Set.univ`.  The
scalar is required for arbitrary passive measures.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.
`git diff --check`, `scripts/sorries`, and direct axiom probe passed.
Faraday the 3rd and Dalton the 3rd xhigh read-only scouts returned PASS on
Lean feasibility and mathematical scope.

Nonclaims: no determinant-chart Haar pushforward, source-prior transport,
passive Jacobian/source-density accounting, source-rank coverage,
source-image equality, local inverse/coverage, normal crossings, pole order,
or RLCT.

## 2026-06-29 A2 Case 2 passive product-measure support

Reproduction:
`reproduction-a2-case2-passive-product-measure-support.md`.
Statement card:
`statement-card-a2-case2-passive-product-measure-support.md`.
Review:
`review-a2-case2-passive-product-measure-support.md`.

Lean now exposes:

```text
case2PassiveDomainProductMeasure_eq_prod_withDensity_sourceDensity
measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_restrict_retainedPassiveP13LocalSource_eq_self
measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_restrict_sourceRankStratum_eq_self
```

These theorems name the concrete passive-domain product measure
`passiveMeasure.prod weightedBox`, derive source-chart a.e. measurability from
the passive source-chart continuity theorem, and specialize the arbitrary
passive chart-produced support wrappers to that concrete measure.  The
source-rank sibling keeps the successor-rank equation explicit as an a.e.
hypothesis.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.
`git diff --check`, `scripts/sorries`, and direct axiom probes passed.

Nonclaims: no source-rank coverage, source-image equality, determinant-chart
pushforward, source-prior transport, normal crossings, pole order, or RLCT.

## 2026-06-29 A2 Case 2 passive source-chart continuity

Reproduction:
`reproduction-a2-case2-passive-source-chart-continuity.md`.
Statement card:
`statement-card-a2-case2-passive-source-chart-continuity.md`.

Lean now exposes:

```text
continuous_case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport_withPassive
```

These theorems prove continuity of the passive selected-entry finite datum and
of the endpoint-transported fixed-base source edge-family chart.  The passive
field families are required to be continuous in `theta`; the source-chart
theorem additionally needs pointwise determinant-unit hypotheses on `Ctop` and
`A1passive` to package values in the determinant-chart subtype.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.
`git diff --check`, `scripts/sorries`, and direct axiom probes passed.
Nash the 3rd xhigh read-only review returned PASS after two docstring wording
fixes:
`review-a2-case2-passive-source-chart-continuity.md`.

Nonclaims: no concrete passive product measure, source-rank coverage,
source-image equality, determinant-chart pushforward, source-prior transport,
normal crossings, pole order, or RLCT.

## 2026-06-29 A2 Case 2 passive chart-produced support

Reproduction:
`reproduction-a2-case2-passive-chart-produced-support.md`.
Statement card:
`statement-card-a2-case2-passive-chart-produced-support.md`.

Lean now exposes:

```text
measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_restrict_retainedPassiveP13LocalSource_eq_self
measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_restrict_sourceRankStratum_eq_self
```

These theorems lift the passive pointwise support lemmas to arbitrary
chart-produced measures on `eta x (center -> R)`, under an explicit
`AEMeasurable sourceChart sourceMeasure` hypothesis.  Source-rank support also
requires the successor rank equation a.e.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.
Direct axiom probes for both theorem names report
`[propext, Classical.choice, Quot.sound]`.
Peirce the 3rd xhigh read-only review returned PASS:
`review-a2-case2-passive-chart-produced-support.md`.

Nonclaims: no concrete passive product measure, source-rank coverage,
source-image equality, determinant-chart pushforward, source-prior transport,
normal crossings, pole order, or RLCT.

## 2026-06-29 A2 Case 2 passive-parameter pointwise support readout

Reproduction:
`reproduction-a2-case2-passive-parameter-pointwise-support-readout.md`.
Statement card:
`statement-card-a2-case2-passive-parameter-pointwise-support-readout.md`.

Lean now exposes:

```text
case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_mem_sourceRankStratum
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_mem_sourceRankStratum_and_localSource_and_residualBlockCoordinateMap_eq_chartMap
```

These theorems certify constructed passive-sector source points pointwise:
under explicit `Ctop`/`A1passive` determinant-unit hypotheses and supplied
rank equations `hprod`, `hr0`, and `hr1`, the source point lies in the named
source-rank stratum and retained-passive p.13 local source, and its residual
coordinate map is the selected-entry chart map.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.
Direct axiom probe reports `[propext, Classical.choice, Quot.sound]`.
Kuhn the 3rd xhigh read-only review returned PASS:
`review-a2-case2-passive-parameter-pointwise-support-readout.md`.

Nonclaims: no source-rank coverage, arbitrary-source local coverage,
source-image equality, measure pushforward, source-prior transport, normal
crossings, pole order, or RLCT.

## 2026-06-29 A2 Case 2 passive-parameter fixed-base source readback

Reproduction:
`reproduction-a2-case2-passive-parameter-fixed-base-source-readback.md`.
Statement card:
`statement-card-a2-case2-passive-parameter-fixed-base-source-readback.md`.

Lean now exposes:

```text
retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
```

This theorem turns passive parameters and selected-entry coordinates into a
fixed-base p.13 source edge family on `eta x (center -> R)`.  It proves
local-source landing and source-readback residual matrix equality under
explicit `Ctop` and `A1passive` determinant-unit hypotheses.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.
Direct axiom probe reports `[propext, Classical.choice, Quot.sound]`.
Controller review and xhigh `Ampere the 3rd` review passed with no findings:
`review-a2-case2-passive-parameter-fixed-base-source-readback.md`.

Nonclaims: no source-image equality, arbitrary-source local coverage, measure
pushforward, source-prior transport, normal crossings, pole order, or RLCT.

## 2026-06-29 A2 Case 2 selected-entry passive-parameter datum

Reproduction:
`reproduction-a2-case2-selected-entry-passive-parameter-datum.md`.
Statement card:
`statement-card-a2-case2-selected-entry-passive-parameter-datum.md`.
Review:
`review-a2-case2-selected-entry-passive-parameter-datum.md`.

Lean now exposes:

```text
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_detChart
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_detChart
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
```

This is the first finite passive-parameter bridge for the Case 2
selected-entry retained-passive datum.  It supplies `A1passive`, `F2`,
`A3passive`, `Ctop`, and `F3` independently while preserving the selected-
entry residual `C` family and its endpoint-transported residual-factor
readout.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge` passed.
The replayed warnings are in imported `ProductReductionStepRegularDensity.lean`.
Euclid the 3rd xhigh read-only review returned PASS.

Nonclaims: no source map, local inverse, image/coverage theorem, measure
pushforward, source-prior transport, normal crossings, pole order, or RLCT.

## 2026-06-29 A2 Case 2 source-rank-supported endpoint-basis original-loss finite-integral bridge

Reproduction:
`reproduction-a2-case2-original-loss-source-rank-supported-finite-integral-bridge.md`.
Statement card:
`statement-card-a2-case2-original-loss-source-rank-supported-finite-integral-bridge.md`.
Review:
`review-a2-case2-original-loss-source-rank-supported-finite-integral-bridge.md`.

Lean now exposes:

```text
exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_continuousAt_pos_density_restrict_open_of_sourceRankSupport
```

This wrapper uses the existing Case 2 source-rank support theorem to rewrite
the final measure restriction in the endpoint-basis original-loss finite-
integral bridge from `mu.restrict (U inter sourceStratum)` to `mu.restrict U`.
The support depends on explicit rank equations `hprod`, `hr0`, and `hr1`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.
`scripts/sorries`, `git diff --check`, touched-file forbidden-marker scan, and
direct axiom probe passed; the theorem reports only `[propext,
Classical.choice, Quot.sound]`.  Locke the 3rd xhigh read-only review
returned PASS.

Nonclaims: the rank equations are hypotheses, not source-rank coverage; no
selected-entry source/image equality, external source-prior transport,
Jacobian comparison for such a prior, normal crossings, pole order, or RLCT.

## 2026-06-29 A2 Case 2 endpoint-basis original-loss finite-integral bridge

Reproduction:
`reproduction-a2-case2-original-loss-finite-integral-bridge.md`.
Statement card:
`statement-card-a2-case2-original-loss-finite-integral-bridge.md`.
Review:
`review-a2-case2-original-loss-finite-integral-bridge.md`.

Lean now exposes:

```text
exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density
```

This is the source-stratum finite-integral bridge for endpoint-basis original
square-Frobenius `lossDLN` in the endpoint-transported continuing Case 2 chart.
It first shrinks the radius using positive continuous density, then applies
the self-base product-coordinate theorem to derive the adapted p.13 lower
bound, and composes that bound with the endpoint-basis comparison
`adapted Frobenius <= lossDLN` after rewriting adapted Frobenius loss to the
adapted square-sum.  The resulting lower constant is `c0 * cprod`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.
`scripts/sorries`, `git diff --check`, touched-file forbidden-marker scan, and
direct axiom probe passed; the theorem reports only `[propext,
Classical.choice, Quot.sound]`.  Wegener the 3rd xhigh read-only review
returned PASS after a stale statement-card status line was fixed.

Nonclaims: no reverse finite-integral implication, source-rank support
rewrite, selected-entry source/image equality, external source-prior
transport, Jacobian comparison for such a prior, normal crossings, pole order,
or RLCT.

## 2026-06-29 A2 Case 2 adapted product-difference finite-integral bridge

Reproduction:
`reproduction-a2-case2-adapted-product-difference-finite-integral-bridge.md`.
Statement card:
`statement-card-a2-case2-adapted-product-difference-finite-integral-bridge.md`.
Review:
`review-a2-case2-adapted-product-difference-finite-integral-bridge.md`.

Lean now exposes:

```text
exists_radius_open_lintegral_ofReal_adaptedProductDifferenceSquareSum_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density
```

This is the source-stratum finite-integral bridge for Aoyagi's adapted p.13
product-difference square-sum in the endpoint-transported continuing Case 2
chart.  It first shrinks the radius using positive continuous density, then
applies the self-base product-coordinate theorem to derive the lower bound

```text
c * (residualSq + regularSq) <= adaptedProductDifferenceSquareSum
```

at a second radius below the density radius.  The existing Case 2
chart-produced source-stratum finite-integral socket then gives finiteness over
`(mu.restrict (U inter sourceStratum)).prod nu`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.
`scripts/sorries`, `git diff --check`, touched-file forbidden-marker scan,
and direct axiom probe passed; the theorem reports only `[propext,
Classical.choice, Quot.sound]`.  Planck the 3rd xhigh read-only review
returned PASS.

Nonclaims: no original-loss identification, reverse implication, source-rank
support rewrite, selected-entry source/image equality, external source-prior
or Jacobian transport, normal crossings, pole order, or RLCT.

## 2026-06-29 A2 Case 2 source-stratum-supported continuous-density small-box two-sided iff

Reproduction:
`reproduction-a2-case2-source-stratum-supported-continuous-density-small-box-two-sided-iff.md`.
Statement card:
`statement-card-a2-case2-source-stratum-supported-continuous-density-small-box-two-sided-iff.md`.
Review:
`review-a2-case2-source-stratum-supported-continuous-density-small-box-two-sided-iff.md`.

Lean now exposes:

```text
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_continuousAt_pos_density_of_smallBox_restrict_open_of_sourceRankSupport
```

This composes the new Case 2 continuous-density small-box source-stratum iff
with the existing Case 2 source-stratum support theorem.  Under the explicit
rank equations `hprod`, `hr0`, and uniform `hr1`, the chart-produced measure
is supported on the source-rank stratum, so the returned iff is stated over
`mu.restrict U` and `residualNegPowerIntegrableOn ... U mu t`.

The source-stratum loss comparison hypotheses remain on `nhdsWithin base
sourceStratum`; support is used only to rewrite the final measure
restriction.  The theorem keeps the radius discipline from the small-box iff.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.
`scripts/sorries`, `git diff --check`, touched Lean-file forbidden-marker
scan, and direct axiom probe passed; the theorem reports only `[propext,
Classical.choice, Quot.sound]`.

Nonclaims: no source-rank coverage, no selected-entry source/image equality,
no exact-rank openness, no external source-prior or Jacobian transport, no
original-loss identification, no normal crossings, pole order, or RLCT.

## 2026-06-29 A2 Case 2 endpoint-transport continuous-density small-box two-sided iff

Reproduction:
`reproduction-a2-case2-endpoint-transport-continuous-density-small-box-two-sided-iff.md`.
Statement card:
`statement-card-a2-case2-endpoint-transport-continuous-density-small-box-two-sided-iff.md`.
Review:
`review-a2-case2-endpoint-transport-continuous-density-small-box-two-sided-iff.md`.

Lean now exposes:

```text
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density_of_smallBox
```

This is the explicit endpoint-transported continuing Case 2 wrapper around
the generic retained-passive continuous-density small-box two-sided iff.  It
builds the concrete retained-passive datum, determinant-chart proof,
residual-coordinate equivalence, residual-factor readout, and determinant-
chart a.e. measurability internally, then calls the generic theorem.

The statement keeps `[SFinite nu]`, `nu.IsAddHaarMeasure`, positive
`Rmax/cLreg/CLreg/t`, positive continuity of the density at `(base,0)`, and
both source-stratum loss comparison bounds at `Rmax` explicit.  It returns
`R dρ Dρ`, then quantifies `delta` and checks the selected-entry small-box
inequality at `R^2`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.
Poincare the 3rd xhigh read-only review returned PASS.
`scripts/sorries`, `git diff --check`, touched Lean-file forbidden-marker
scan, and direct axiom probe passed; the theorem reports only `[propext,
Classical.choice, Quot.sound]`.

Nonclaims: no positive signed-box radius hypothesis, no selected-entry
critical inequality, no source-rank coverage, no source/image equality, no
external source-prior or Jacobian transport, no original-loss identification,
no normal crossings, pole order, or RLCT.

## 2026-06-29 A2 continuous-density small-box residual discharge

Reproduction:
`reproduction-a2-retained-passive-small-box-chart-produced-residual-bound.md`.
Statement card:
`statement-card-a2-retained-passive-small-box-chart-produced-residual-bound.md`.
Review:
`review-a2-retained-passive-small-box-chart-produced-residual-bound.md`.

Lean now exposes:

```text
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure_continuousAt_pos_density_of_smallBox
```

The theorem wraps the existing positive continuous-density two-sided theorem
and discharges its residual boundedness premise using the small-box residual
bound.  It returns `R dρ Dρ` with `0 < R` and `R <= Rmax`, then quantifies
`delta` and requires the selected-entry scalar smallness inequality at `R^2`.
This preserves the fixed-radius discipline: a bound at `Rmax` is not used as a
bound at the produced radius.

Focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure` passed.
Huygens the 3rd xhigh read-only review returned PASS.  `scripts/sorries`,
`git diff --check`, touched-file marker scan, and direct axiom probe passed;
the theorem reports only `[propext, Classical.choice, Quot.sound]`.

Nonclaims: no choice of `Rres` or `delta`, no loss comparison proof, no
source-rank coverage, no source/image equality, no external transport theorem,
no original-loss identification, no normal crossings, pole order, or RLCT.

## 2026-06-29 A2 selected-entry residual upper bound on small signed boxes

Reproduction:
`reproduction-a2-selected-entry-center-residual-upper-bound-small-signed-box.md`.
Statement card:
`statement-card-a2-selected-entry-center-residual-upper-bound-small-signed-box.md`.
Review:
`review-a2-selected-entry-center-residual-upper-bound-small-signed-box.md`.

Lean now exposes:

```text
SelectedEntrySignedBox.CenterCoord.residual_le_sq_of_abs_le
SelectedEntrySignedBox.CenterCoord.residual_le_sq_of_mem_signedBoxSet
SelectedEntrySignedBox.CenterCoord.residual_le_sq_ae_signedBox_of_smallBox
SelectedEntrySignedBox.CenterCoord.residual_le_sq_ae_withDensity_sourceDensity_of_smallBox
```

These prove the finite selected-entry residual upper bound on small center
signed boxes and its unweighted/weighted signed-box a.e. forms.  The layer is
source-side only: it does not yet push the a.e. bound through a retained-
passive chart-produced measure.  Focused build of
`DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure` passed.  Euclid the 2nd
xhigh read-only review passed.  Hygiene gates passed: `scripts/sorries`,
`git diff --check`, touched-file marker scan, and direct axiom probe with
`[propext, Classical.choice, Quot.sound]`.

## 2026-06-29 A2 retained-passive source-edge-family chart-produced source-stratum continuous-density two-sided iff

Reproduction:
`reproduction-a2-retained-passive-source-edge-family-chart-produced-source-stratum-two-sided-continuous-density-iff.md`.
Statement card:
`statement-card-a2-retained-passive-source-edge-family-chart-produced-source-stratum-continuous-density-two-sided-iff.md`.
Review:
`review-a2-retained-passive-source-edge-family-chart-produced-source-stratum-continuous-density-two-sided-iff.md`.

Lean now exposes:

```text
exists_pos_radius_le_eventually_nhdsWithin_density_two_sided_bounds_of_continuousAt_pos
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure_continuousAt_pos_density
```

The helper proves positive lower and finite upper local bounds for a positive
continuous density after shrinking the regular-coordinate radius.  The
retained-passive wrapper uses those bounds to call the banked source-edge-
family chart-produced source-stratum two-sided iff.  It keeps residual
boundedness explicit at the produced radius `R`; the two source-stratum loss
bounds are supplied at `Rmax` and restricted to `R`.

Focused builds passed for
`DLNFibre.DLN.Aoyagi.LocalMeasureHandoff` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure`.  Goodall the 2nd xhigh
read-only review passed.  Hygiene gates passed: `scripts/sorries`,
`git diff --check`, touched-file marker scan, and direct axiom probe with
`[propext, Classical.choice, Quot.sound]`.
Nonclaims remain: no residual boundedness or loss comparison proof, no
selected-entry critical integrability, no signed-box source/image equality, no
source-rank coverage proof, no external transport theorem, no original-loss
identification, no normal crossings, pole order, or RLCT.

## 2026-06-29 A2 retained-passive source-edge-family chart-produced source-stratum two-sided iff

Reproduction:
`reproduction-a2-retained-passive-source-edge-family-chart-produced-source-stratum-two-sided-iff.md`.
Statement card:
`statement-card-a2-retained-passive-source-edge-family-chart-produced-source-stratum-two-sided-iff.md`.
Review:
`review-a2-retained-passive-source-edge-family-chart-produced-source-stratum-two-sided-iff.md`.

Lean now exposes:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure
```

It constructs the concrete retained-passive source-edge-family chart from
retained data, proves the chart a.e. measurable from retained-data
a.e. measurability and continuity of the retained-passive p.13 source chart,
gets local-source landing and source-readback matrix equality from the
source-edge-family readback theorem, and gets the selected-entry residual
readout from the square-sum bridge.  Residual boundedness and the four
source-stratum comparison bounds remain explicit.

Focused `scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure` passed.
Schrodinger the 2nd xhigh read-only review passed.  Hygiene gates passed:
`scripts/sorries`, `git diff --check`, touched-file marker scan, and direct
axiom probe with `[propext, Classical.choice, Quot.sound]`.  Nonclaims remain:
no selected-entry critical inequality, no residual integrability proof, no
signed-box source/image equality, no source-rank coverage proof, no external
transport theorem, no original-loss identification, no normal crossings, pole
order, or RLCT.

## 2026-06-29 A2 retained-passive source-stratum chart-produced selected-entry two-sided loss-density iff

Reproduction:
`reproduction-a2-retained-passive-source-stratum-chart-produced-selected-entry-two-sided-loss-density-iff.md`.
Statement card:
`statement-card-a2-retained-passive-source-stratum-chart-produced-selected-entry-two-sided-loss-density-iff.md`.
Review:
`review-a2-retained-passive-source-stratum-chart-produced-selected-entry-two-sided-loss-density-iff.md`.

Lean now exposes:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure
```

It defines `mu` as the selected-entry weighted signed-box pushforward and
derives the retained-passive local-source restriction equality from pointwise
chart landing, then calls the banked source-stratum-bound selected-entry
two-sided theorem.  Residual readout, residual boundedness over the
chart-produced measure restricted to `localSource`, and the four
source-stratum comparison bounds remain explicit.

Focused `scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure` passed.
Helmholtz the 2nd xhigh read-only review passed.  Hygiene gates passed:
`scripts/sorries`, `git diff --check`, touched-file marker scan, and direct
axiom probe with `[propext, Classical.choice, Quot.sound]`.  Nonclaims remain:
no proof of chart landing, no selected-entry critical inequality, no residual
integrability proof, no signed-box source/image equality, no source-rank
coverage proof, no external transport theorem, no original-loss
identification, no normal crossings, pole order, or RLCT.

## 2026-06-29 A2 retained-passive source-stratum selected-entry two-sided loss-density iff

Reproduction:
`reproduction-a2-retained-passive-source-stratum-selected-entry-two-sided-loss-density-iff.md`.
Statement card:
`statement-card-a2-retained-passive-source-stratum-selected-entry-two-sided-loss-density-iff.md`.
Review:
`review-a2-retained-passive-source-stratum-selected-entry-two-sided-loss-density-iff.md`.

Lean now exposes:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds
```

It derives residual measurability and residual positivity on the retained-
passive local source, uses the retained-passive self-base local coverage
theorem to relate the source-rank stratum to that local source, and returns the
source-stratum two-sided loss-density iff.  Residual boundedness and the four
source-stratum comparison bounds remain explicit.

Focused `scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure` passed.
Cicero the 2nd xhigh read-only review passed.  Hygiene gates passed:
`scripts/sorries`, `git diff --check`, touched-file marker scan, and direct
axiom probe with `[propext, Classical.choice, Quot.sound]`.  Nonclaims remain:
no selected-entry critical inequality, no residual integrability proof, no
signed-box source/image equality, no source-rank coverage proof, no external
transport theorem, no original-loss identification, no normal crossings, pole
order, or RLCT.

## 2026-06-29 A2 retained-passive chart-produced selected-entry two-sided loss-density iff

Reproduction:
`reproduction-a2-retained-passive-chart-produced-selected-entry-two-sided-loss-density-iff.md`.
Statement card:
`statement-card-a2-retained-passive-chart-produced-selected-entry-two-sided-loss-density-iff.md`.
Review:
`review-a2-retained-passive-chart-produced-selected-entry-two-sided-loss-density-iff.md`.

Lean now exposes:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure
```

It defines `mu` as the selected-entry weighted signed-box pushforward and
derives the retained-passive local-source restriction equality from pointwise
chart landing.  Residual readout, residual boundedness, and four two-sided
p.13 loss/density comparisons remain explicit.

Focused `scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure` passed.
Carver the 2nd xhigh read-only review passed.  Hygiene gates passed:
`scripts/sorries`, `git diff --check`, touched-file marker scan, and direct
axiom probe with `[propext, Classical.choice, Quot.sound]`.  Nonclaims remain:
no proof of chart landing, no selected-entry critical inequality, no residual
integrability proof, no source coverage or source/image equality, no external
transport theorem, no original-loss identification, no normal crossings, pole
order, or RLCT.

## 2026-06-29 A2 retained-passive local-source selected-entry two-sided loss-density iff

Reproduction:
`reproduction-a2-retained-passive-local-source-selected-entry-two-sided-loss-density-iff.md`.
Statement card:
`statement-card-a2-retained-passive-local-source-selected-entry-two-sided-loss-density-iff.md`.
Review:
`review-a2-retained-passive-local-source-selected-entry-two-sided-loss-density-iff.md`.

Lean now exposes:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity
```

It specializes the selected-entry local-source two-sided iff to the
retained-passive p.13 local source.  The retained-passive layer only proves
local-source measurability and edge-matrix measurability from
`Continuous Cedge`; the signed-box pushforward, residual readout, residual
boundedness, and four two-sided p.13 loss/density comparisons remain explicit.

Focused `scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure` passed.
Halley the 2nd xhigh read-only review passed.  Hygiene gates passed:
`scripts/sorries`, `git diff --check`, touched-file marker scan, and direct
axiom probe with `[propext, Classical.choice, Quot.sound]`.  Nonclaims remain:
no selected-entry critical inequality, no residual integrability proof, no
source coverage or source/image equality, no transport theorem, no
original-loss identification, no normal crossings, pole order, or RLCT.

## 2026-06-29 A2 local-source selected-entry signed-box two-sided loss-density iff

Reproduction:
`reproduction-a2-local-source-selected-entry-signed-box-two-sided-loss-density-iff.md`.
Statement card:
`statement-card-a2-local-source-selected-entry-signed-box-two-sided-loss-density-iff.md`.
Review:
`review-a2-local-source-selected-entry-signed-box-two-sided-loss-density-iff.md`.

Lean now exposes:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_localSource_selectedEntryCenter_signedBox_withDensity_edgeMatrix
```

It uses the selected-entry residual-unit lower bound to discharge only the
monomial residual lower bound for the local-source signed-box two-sided
theorem.  It does not assume selected-entry critical inequalities,
source-density bounds, or positive signed-box radii.  Residual boundedness and
the four two-sided p.13 loss/density comparisons remain explicit.

Focused `scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxLocalMeasure`
passed.  Boole xhigh read-only review passed.  Hygiene gates passed:
`scripts/sorries`, `git diff --check`, touched-file marker scan, and direct
axiom probe with `[propext, Classical.choice, Quot.sound]`.  Nonclaims remain:
no selected-entry chart construction, no source coverage or source/image
equality, no pushforward proof, no comparison-bound or residual-boundedness
proof, no transport theorem, no original-loss identification, no normal
crossings, pole order, or RLCT.

## 2026-06-29 A2 open-source-stratum signed-box two-sided loss-density iff

Reproduction:
`reproduction-a2-open-source-stratum-signed-box-two-sided-loss-density-iff.md`.
Statement card:
`statement-card-a2-open-source-stratum-signed-box-two-sided-loss-density-iff.md`.
Review:
`review-a2-open-source-stratum-signed-box-two-sided-loss-density-iff.md`.

Lean now exposes:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_openSourceStratum_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
```

It applies the local-source signed-box two-sided theorem to the exact local
piece `Ulocal inter sourceStratum`, assuming the weighted signed-box
pushforward identity for `mu.restrict (Ulocal inter sourceStratum)`.  The
comparison bounds remain stated on `nhdsWithin x0 sourceStratum` and are
transported to the local piece using `Ulocal` open and `x0 in Ulocal`.

Focused `scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure` passed.
Volta xhigh read-only review passed.  Hygiene gates passed:
`scripts/sorries`, `git diff --check`, touched-file marker scan, and direct
axiom probe with `[propext, Classical.choice, Quot.sound]`.  Nonclaims remain:
no signed-box chart construction, no restriction theorem for larger
pushforwards, no source-stratum coverage theorem, no comparison-bound or
residual-boundedness proof, no transport theorem, no original-loss
identification, no normal crossings, pole order, or RLCT.

## 2026-06-29 A2 source-stratum signed-box two-sided loss-density iff

Reproduction:
`reproduction-a2-source-stratum-signed-box-two-sided-loss-density-iff.md`.
Statement card:
`statement-card-a2-source-stratum-signed-box-two-sided-loss-density-iff.md`.
Review:
`review-a2-source-stratum-signed-box-two-sided-loss-density-iff.md`.

Lean now exposes:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
```

It specializes the local-source signed-box two-sided theorem to
`paperEndpointFixedBaseSourceRankStratum`.  It assumes source-stratum
measurability, measurable fixed-basis edge matrices, the source-stratum
weighted signed-box pushforward, `0 < cres`, the residual monomial lower bound,
explicit residual boundedness `residualSquareSum <= Rreg^2`, and four supplied
two-sided source-stratum comparison bounds.  It returns an open `U` where
actual loss-density finiteness over `(mu.restrict (U inter sourceStratum)).prod
nu` is equivalent to `residualNegPowerIntegrableOn Cedge (U inter
sourceStratum) mu t`.

Focused `scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure` passed.
Anscombe xhigh read-only review passed.  Hygiene gates passed
(`scripts/sorries`, `git diff --check`, touched-file marker scan, direct axiom
probe with `[propext, Classical.choice, Quot.sound]`).  Nonclaims remain: no
signed-box chart construction, no pushforward or source-stratum coverage proof,
no comparison-bound or residual-boundedness proof, no residual integrability
proof from signed-box critical inequalities, no transport theorem, no
original-loss identification, no normal crossings, pole order, or RLCT.

## 2026-06-29 A2 local-source signed-box two-sided loss-density iff

Reproduction:
`reproduction-a2-local-source-signed-box-two-sided-loss-density-iff.md`.
Statement card:
`statement-card-a2-local-source-signed-box-two-sided-loss-density-iff.md`.
Review:
`review-a2-local-source-signed-box-two-sided-loss-density-iff.md`.

Lean now exposes:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
```

It derives residual square-sum measurability from the measurable fixed-basis
edge matrices and residual positivity from the positivity-only weighted
signed-box monomial-lower helper, then applies the local-source two-sided
loss-density iff with explicit residual boundedness
`residualSquareSum <= Rreg^2` and four supplied two-sided comparison bounds.
The result returns an open `U` where actual loss-density finiteness over
`(mu.restrict (U inter source)).prod nu` is equivalent to
`residualNegPowerIntegrableOn Cedge (U inter source) mu t`.

Focused `scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure` passed
after the positivity-only weakening.  Mencius' follow-up xhigh review passed;
hygiene gates passed (`scripts/sorries`, `git diff --check`, touched-file
marker scan, direct axiom probes with `[propext, Classical.choice,
Quot.sound]`).  Nonclaims remain: no signed-box chart construction, no
pushforward or
local-coverage proof, no comparison-bound or residual-boundedness proof, no
residual-integrability proof from signed-box critical inequalities, no
transport theorem, no original-loss identification, no normal crossings, pole
order, or RLCT.

## 2026-06-29 A2 source-stratum/local-source two-sided loss-density iff

Reproduction:
`reproduction-a2-source-stratum-local-source-two-sided-loss-density-iff.md`.
Statement card:
`statement-card-a2-source-stratum-local-source-two-sided-loss-density-iff.md`.
Review:
`review-a2-source-stratum-local-source-two-sided-loss-density-iff.md`.

Lean now exposes:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_sourceStratum_bounds_locally_subset_localSource_two_sided_bounds
```

It applies the local-source two-sided iff to
`Ulocal inter sourceStratum`, using the supplied inclusion
`Ulocal inter sourceStratum subset Ulocal inter localSource` to restrict
residual hypotheses from `localSource`.  The result returns an open `U` where
actual loss-density finiteness over `(mu.restrict (U inter sourceStratum)).prod
nu` is equivalent to `residualNegPowerIntegrableOn Cedge (U inter
sourceStratum) mu t`.

Focused `scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure` passed.
`scripts/sorries`, `git diff --check`, touched Lean-file forbidden-marker scan,
and direct axiom probe passed.  The axiom footprint is
`[propext, Classical.choice, Quot.sound]`.  Nonclaims remain: no comparison or
residual-hypothesis proof, no local coverage proof, no chart
construction/coverage, no transport theorem, no original-loss identification,
no normal crossings, pole order, or RLCT.

## 2026-06-29 A2 source-stratum two-sided loss-density iff

Reproduction:
`reproduction-a2-source-stratum-two-sided-loss-density-iff.md`.
Statement card:
`statement-card-a2-source-stratum-two-sided-loss-density-iff.md`.
Review:
`review-a2-source-stratum-two-sided-loss-density-iff.md`.

Lean now exposes:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_sourceStratum_two_sided_bounds
```

It specializes the local-source two-sided loss-density iff to
`paperEndpointFixedBaseSourceRankStratum`.  Under explicit residual hypotheses
on the source stratum, constant positivity, Haar/SFinite regular measure, and
four supplied source-stratum-filter comparison bounds, it returns an open `U`
where actual loss-density finiteness over
`(mu.restrict (U inter sourceStratum)).prod nu` is equivalent to
`residualNegPowerIntegrableOn Cedge (U inter sourceStratum) mu t`.

Focused `scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure` passed.
`scripts/sorries`, `git diff --check`, touched Lean-file forbidden-marker scan,
and direct axiom probe passed.  The axiom footprint is
`[propext, Classical.choice, Quot.sound]`.  Xhigh read-only scouts Bohr and
Dirac accepted the statement scope and proof shape.  Nonclaims remain: no
comparison or residual-hypothesis proof, no chart construction/coverage, no
transport theorem, no original-loss identification, no normal crossings, pole
order, or RLCT.

## 2026-06-29 A2 local-source two-sided loss-density iff

Reproduction:
`reproduction-a2-local-source-two-sided-loss-density-iff.md`.
Statement card:
`statement-card-a2-local-source-two-sided-loss-density-iff.md`.
Review:
`review-a2-local-source-two-sided-loss-density-iff.md`.

Lean now exposes:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_localSource_two_sided_bounds
```

It combines the local-source two-sided a.e. handoff with the p.13 two-sided
comparison iff.  Under explicit residual measurability, positivity, and
`<=R^2` hypotheses on `source`, constant positivity, Haar/SFinite regular
measure, and four supplied source-filter bounds, it returns an open `U` where
actual loss-density finiteness over `(mu.restrict (U inter source)).prod nu`
is equivalent to `residualNegPowerIntegrableOn Cedge (U inter source) mu t`.

Focused `scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure`,
`scripts/sorries`, `git diff --check`, touched Lean-file forbidden-marker
scan, and direct axiom probe passed.  The axiom footprint is
`[propext, Classical.choice, Quot.sound]`.  Xhigh read-only scouts Jason and
Mendel accepted the statement scope and proof shape; xhigh reviewer Ohm passed
the final diff.  Nonclaims remain: no comparison or residual-hypothesis proof,
no chart construction/coverage, no transport theorem, no original-loss
identification, no normal crossings, pole order, or RLCT.

## 2026-06-29 A2 source-stratum two-sided loss-density handoff

Reproduction:
`reproduction-a2-source-stratum-two-sided-loss-density-handoff.md`.
Statement card:
`statement-card-a2-source-stratum-two-sided-loss-density-handoff.md`.
Review:
`review-a2-source-stratum-two-sided-loss-density-handoff.md`.

Lean now exposes:

```text
exists_open_ae_restrict_source_prod_p13RegularCoordinates_two_sided_loss_density_bounds
```

It specializes the local-source two-sided handoff to
`paperEndpointFixedBaseSourceRankStratum`, giving four a.e. bounds over
`(mu.restrict (U inter sourceStratum)).prod nu`.  The proof calls the
local-source theorem with `source := sourceStratum` and rewrites back by the
local abbreviation.  It proves no comparison bounds, constant positivity,
source-rank-stratum openness/coverage/image statement, transport theorem,
residual hypotheses, finite integral, integrability iff, normal crossings,
pole order, or RLCT.

Focused `scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure`,
`scripts/sorries`, `git diff --check`, touched Lean-file forbidden-marker
scan, and direct axiom probe passed.  The axiom footprint is
`[propext, Classical.choice, Quot.sound]`.  Xhigh read-only scouts Darwin and
Peirce accepted the wrapper scope and proof shape; xhigh reviewer Singer
passed the final diff.

## 2026-06-29 A2 local-source two-sided loss-density handoff

Reproduction:
`reproduction-a2-local-source-two-sided-loss-density-handoff.md`.
Statement card:
`statement-card-a2-local-source-two-sided-loss-density-handoff.md`.
Review:
`review-a2-local-source-two-sided-loss-density-handoff.md`.

Lean now exposes:

```text
exists_open_ae_restrict_localSource_prod_p13RegularCoordinates_two_sided_loss_density_bounds
```

The theorem takes four supplied `nhdsWithin x0 source` bounds, uniform in the
p.13 regular-coordinate ball, and transports them to four a.e. facts over one
common restricted product measure `(mu.restrict (U inter source)).prod nu`
after shrinking to an open base neighborhood `U`.  It is only
filter-to-measure plumbing; it does not prove positivity of constants, the
comparison hypotheses, chart construction or transport, residual hypotheses,
integrability, normal crossings, pole order, or RLCT.

Focused `scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure`,
`scripts/sorries`, `git diff --check`, touched Lean-file forbidden-marker
scan, direct axiom probe, and xhigh review passed.  The axiom footprint is
`[propext, Classical.choice, Quot.sound]`.

## 2026-06-28 A2 direct-chart positive-set measurability hardening

Reproduction:
`reproduction-a2-retained-passive-direct-chart-positive-set-measurability.md`.
Statement card:
`statement-card-a2-retained-passive-direct-chart-positive-set-measurability.md`.
Review:
`review-a2-retained-passive-direct-chart-positive-set-measurability.md`.

Lean now exposes:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.measurableSet_residualSquareSum_pos_retainedPassiveP13Canonical_directChart
```

and uses it to remove the explicit direct-chart target positive-set
measurability hypothesis from the Case 2 determinant-chart selected-entry
residual theorem and the two Case 2 raw-order inverse-Jacobian consumers.  The
determinant-chart pushforward identity remains explicit; the finite-integral
consumer still keeps the local loss and density hypotheses explicit.

Focused builds passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology`,
`DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure`, and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` via the
worktree-local `scripts/lb` command.  Kant gave an xhigh read-only PASS on the
pen-and-paper note, with the Lean-surface caveat addressed by proving the
helper on the `TopologyTuple` surface and using only a local Borel structure on
retained-passive data.

This is only finite coordinate measurability.  It is not residual positivity,
residual integrability, determinant-chart pushforward, chart coverage,
original external prior transport, local loss or density bounds, source-rank
coverage, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 Case 2 inverse-Jacobian residual-source handoff

Reproduction:
`reproduction-a2-case2-inverse-jacobian-residual-source-handoff.md`.
Statement card:
`statement-card-a2-case2-inverse-jacobian-residual-source-handoff.md`.
Review:
`review-a2-case2-inverse-jacobian-residual-source-handoff.md`.

Lean now exposes:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_case2EndpointTransport_selectedEntrySignedBox_map
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_case2EndpointTransport_selectedEntrySignedBox_map
```

These compose the Case 2 selected-entry determinant-chart residual theorem with
the raw-order inverse-Jacobian `_of_chartSide` sockets.  After the direct-chart
positive-set measurability hardening, the determinant-chart pushforward
identity remains explicit, while target positive-set measurability is
discharged internally; the finite-integral theorem also keeps local loss and
density hypotheses explicit.

Focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`
passed via the worktree-local `scripts/lb` command.  `scripts/sorries`,
`git diff --check`, touched-file forbidden-marker search, direct dependency
probes, and xhigh read-only review by Godel passed; both declarations report
only `[propext, Classical.choice, Quot.sound]`.

This is not proof of the determinant-chart pushforward identity, chart
coverage, original external prior transport, local loss or density bounds,
source-rank coverage, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 retained-passive inverse-Jacobian chart-side measurability wrapper

Reproduction:
`reproduction-a2-retained-passive-inverse-jacobian-chartside-measurability-wrapper.md`.
Statement card:
`statement-card-a2-retained-passive-inverse-jacobian-chartside-measurability-wrapper.md`.
Review:
`review-a2-retained-passive-inverse-jacobian-chartside-measurability-wrapper.md`.

Lean now exposes:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_chartSide
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_chartSide
```

The wrappers discharge only the source-space residual positive-set
measurability field by reusing the existing identity-source measurability
lemma.  The determinant-chart residual positivity and finite residual
negative-power integral remain explicit, and the finite-integral wrapper keeps
local loss and density hypotheses explicit.

Focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure`
passed via the worktree-local `scripts/lb` command.  `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker search, direct theorem
axiom probes, and xhigh read-only review by Franklin passed.

This is not proof of determinant-chart residual positivity/integrability,
local loss or density bounds, selected-entry residual integrability,
source-rank coverage, original external prior transport, normal crossings,
pole order, or RLCT.

## 2026-06-28 A2 retained-passive inverse-Jacobian finite-integral handoff

Reproduction:
`reproduction-a2-retained-passive-inverse-jacobian-finite-integral-handoff.md`.
Statement card:
`statement-card-a2-retained-passive-inverse-jacobian-finite-integral-handoff.md`.
Review:
`review-a2-retained-passive-inverse-jacobian-finite-integral-handoff.md`.

Lean now exposes:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian
```

It composes the retained-passive inverse-Jacobian residual-source handoff with
the p.13 local finite-integral socket for the identity retained-passive local
source.  The proof uses the raw-order source measure

```text
Measure.map rawChart ((m.restrict T).withDensity invJacDensity)
```

and applies the socket with `Cedge := fun E => E`, the base identity by `rfl`,
and continuity by `continuous_id`.

Focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure`
passed via the worktree-local `scripts/lb` command.  `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker search, direct theorem
axiom probe, and xhigh review passed; the theorem reports only
`[propext, Classical.choice, Quot.sound]`.

This is a retained-passive chart-layer finite-integral handoff.  It does not
prove source-space residual positive-set measurability, determinant-chart
residual positivity/integrability, selected-entry residual integrability,
source-rank coverage, original external DLN-prior transport, normal crossings,
pole order, or RLCT extraction.

## 2026-06-28 A2 retained-passive direct source-chart inverse-Jacobian measure

Reproduction:
`reproduction-a2-retained-passive-direct-source-chart-inverse-jacobian-measure.md`.
Statement card:
`statement-card-a2-retained-passive-direct-source-chart-inverse-jacobian-measure.md`.
Review:
`review-a2-retained-passive-direct-source-chart-inverse-jacobian-measure.md`.

Lean now exposes:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.measure_map_paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_restrict_detChart_eq_map_rawOrderSourceChart_withDensity_inverseJacobian
```

It proves that the direct fixed-base retained-passive p.13 source-edge-family
pushforward of determinant-chart Haar measure equals the public raw-order p.13
source-chart pushforward of the raw-order determinant-chart measure weighted
by `topologyTupleEdgeRawOrderInverseJacobianDensity`.

Focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure`
passed via the worktree-local `scripts/lb` command.  `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker search, direct theorem
axiom probe, and xhigh review passed; the theorem reports only
`[propext, Classical.choice, Quot.sound]`.

This is retained-passive chart-layer source-measure/Jacobian transport only.
It is not original external DLN-prior identification, source-rank coverage,
selected-entry residual positivity/integrability, normal crossings, pole
order, or RLCT extraction.

## 2026-06-28 A2 retained-passive source-edge-family density continuous-at finite integral

Reproduction:
`reproduction-a2-retained-passive-source-edge-family-density-continuousat-finite-integral.md`.
Statement card:
`statement-card-a2-retained-passive-source-edge-family-density-continuousat-finite-integral.md`.
Review:
`review-a2-retained-passive-source-edge-family-density-continuousat-finite-integral.md`.

Lean now exposes:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceEdgeFamilyOfData_chartProducedMeasure_continuousAt_pos_density
```

For the generic retained-passive source-edge-family chart-produced measure, a
positive continuous density at `(base,0)` supplies local density
nonnegativity and boundedness after shrinking the regular-coordinate radius.
The theorem removes supplied `Rreg`, `Creg`, `0 <= Creg`, eventual density
nonnegativity, and eventual density boundedness, and returns `R`, `C`, and an
open neighborhood `U`.

Focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure` passed via
the worktree-local `scripts/lb` command.  `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker search, direct theorem
axiom probe, and xhigh review passed; the theorem reports only
`[propext, Classical.choice, Quot.sound]`.

This is not endpoint-equivalence construction, endpoint provenance, original
source-prior identification, Jacobian comparison for an external prior,
source-rank coverage, normal crossings, pole order, or RLCT extraction.

## 2026-06-28 A2 retained-passive source-edge-family chart-produced measure

Reproduction:
`reproduction-a2-retained-passive-source-edge-family-chart-produced-measure.md`.
Statement card:
`statement-card-a2-retained-passive-source-edge-family-chart-produced-measure.md`.
Review:
`review-a2-retained-passive-source-edge-family-chart-produced-measure.md`.

Lean now exposes:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceEdgeFamilyOfData_chartProducedMeasure
```

For a retained-passive determinant-chart data path, the theorem fixes the
source chart to the concrete fixed-base p.13 source edge-family map
`paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData`.  It removes
the separate chart-produced handoff hypotheses `hsourceChart`, `hchart_mem`,
and `hfactor`: `hsourceChart` comes from `hretainedData` composed with the
continuous p.13 source chart, while `hchart_mem` and `hfactor` come from
`hdet` and `hdataFactor` via the source-edge-family helper.

Focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure` passed via
the worktree-local `scripts/lb` command.  `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker search, direct theorem
axiom probe, and xhigh review passed; the theorem reports only
`[propext, Classical.choice, Quot.sound]`.

This is not endpoint-equivalence construction, endpoint provenance, original
source-prior identification, Jacobian comparison for an external prior,
source-rank coverage, normal crossings, pole order, or RLCT extraction.

## 2026-06-28 A2 Case 2 fixed-pivot source-readback readout

Reproduction:
`reproduction-a2-case2-fixed-pivot-source-readback-readout.md`.
Statement card:
`statement-card-a2-case2-fixed-pivot-source-readback-readout.md`.
Review:
`review-a2-case2-fixed-pivot-source-readback-readout.md`.

Lean now exposes:

```text
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_fixedPivot_entry_eq_yNext
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_fixedPivot_entry_ne_zero_of_yNext_pivot_ne_zero
PaperEndpointFixedBaseRegularCoordinateSourceData.sourceReadback_residualFactorProduct_fixedPivot_entry_eq_yNext_of_case2EndpointTransport_sourceEdgeFamilyOfData
PaperEndpointFixedBaseRegularCoordinateSourceData.sourceReadback_residualFactorProduct_fixedPivot_entry_ne_zero_of_case2EndpointTransport_sourceEdgeFamilyOfData_yNext_pivot_ne_zero
```

The first theorem evaluates the endpoint-transported selected-entry matrix
identity at the coordinate corresponding to the displayed successor pivot
`(J+2,J+2)` and proves the product entry is `yNext pivotNext`.  The nonzero
corollary consumes `hyNext`.  The fixed-base theorems lift this pointwise
readout through the p.13 source edge family by rewriting the source readback to
the endpoint-transported datum.

Focused builds of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed with
only the known imported warning profile.  `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker search, and direct axiom
probes passed; the new declarations report only `[propext, Classical.choice,
Quot.sound]`.

This removes the all-pivot existential ambiguity for the constructed
endpoint-transported source-readback branch.  It does not construct `tau`,
prove `hTau`, prove canonical endpoint labelling, identify arbitrary
`ofTopologyTuple` data, transport source priors, compare Jacobians, prove
normal crossings, compute pole order, or extract RLCT.

## 2026-06-28 A2 Case 2 self-endpoint transport

Reproduction:
`reproduction-a2-case2-self-endpoint-transport.md`.
Statement card:
`statement-card-a2-case2-self-endpoint-transport.md`.
Review:
`review-a2-case2-self-endpoint-transport.md`.

Lean now exposes:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_selfEndpoint_sourceEdgeFamilyOfData
```

This is the self-endpoint specialization of the supplied-equivalence
endpoint-transport source-family theorem.  It fixes
`tau := Case2ResidualColIndex n S (J + 1)` and uses `Equiv.refl _` for the
former `eNext` argument.  The endpoint-family equivalences `e` are still
supplied.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed via the
worktree-local `scripts/lb` command.  `scripts/sorries`, `git diff --check`,
touched Lean-file forbidden-marker search, and direct theorem axiom probe
passed; the theorem reports only `[propext, Classical.choice, Quot.sound]`.
Independent xhigh review passed.

This is not proof of `hTau`, construction of the endpoint-family equivalences,
label-preserving endpoint provenance, selected-entry preservation, source-prior
transport, Jacobian comparison, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 Case 2 residual endpoint scalar cardinalities

Reproduction:
`reproduction-a2-case2-residual-endpoint-scalar-cardinalities.md`.
Statement card:
`statement-card-a2-case2-residual-endpoint-scalar-cardinalities.md`.
Review:
`review-a2-case2-residual-endpoint-scalar-cardinalities.md`.

Lean now exposes:

```text
case2ResidualEndpoint_card_eqs_of_width_rank
case2PostPivotTwoEdgeDomain_card_eq_endpointComplementIndex_of_sourceData_width_rank
```

The first theorem proves the successor residual column and row cardinalities
from the explicit equalities `H 2 = n (S + 1)`, `H 1 = prefixMinNat n S`, and
`r = J + 1`, using `Fintype.card_coe` and the finite interval-cardinality lemmas.
The second theorem feeds those two scalar equalities into the source-data
endpoint-cardinality theorem and leaves `hTau : card tau = H 3 - r` explicit.

Focused build of `DLNFibre.DLN.Aoyagi.Case2ResidualFactorProduct` passed via
the worktree-local `scripts/lb` command.
`scripts/sorries`, `git diff --check`, touched Lean-file forbidden-marker
search, direct theorem axiom probes, and xhigh review passed.

This is not proof of those width/rank equalities, proof of `hTau`,
construction of `tau`, canonical endpoint labelling, selected-entry
preservation, measure transport, Jacobian comparison, normal crossings, pole
order, or RLCT.

## 2026-06-28 A2 Case 2 endpoint cardinalities from source data

Reproduction:
`reproduction-a2-case2-endpoint-cardinalities-from-source-data.md`.
Statement card:
`statement-card-a2-case2-endpoint-cardinalities-from-source-data.md`.

Lean now exposes:

```text
case2PostPivotTwoEdgeDomain_card_eq_endpointComplementIndex_of_sourceData
```

The theorem derives the pointwise `hEndpoints` cardinality family by unfolding
the three endpoints of `case2PostPivotTwoEdgeDomain` and comparing them with
the fixed-base source-data endpoint complement counts.  It still requires
explicit scalar equalities for `tau`, the successor residual-column type, and
the successor residual-row type.

Focused build of `DLNFibre.DLN.Aoyagi.Case2ResidualFactorProduct` passed via
the worktree-local `scripts/lb` command.

This is not proof of those scalar equalities, construction of `tau`, canonical
endpoint labelling, selected-entry preservation, measure transport, Jacobian
comparison, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 endpoint equivalences from cardinalities

Reproduction:
`reproduction-a2-case2-endpoint-equivalences-from-cardinalities.md`.
Statement card:
`statement-card-a2-case2-endpoint-equivalences-from-cardinalities.md`.

Lean now exposes:

```text
case2EndpointTransportEquivs_of_card_eq
PaperEndpointFixedBaseRegularCoordinateSourceData.endpointComplementIndex_card_eq_H_rev_sub_rank
```

The first declaration is a `noncomputable def` producing arbitrary finite
equivalence data from explicit cardinality equalities.  The second computes the
fixed-base endpoint complement cardinalities from source data as
`H (q.rev.val + 1) - r`.

Focused build of `DLNFibre.DLN.Aoyagi.Case2ResidualFactorProduct` passed via
the worktree-local `scripts/lb` command, rebuilding `RegularSuspensionCoordinates`.
`scripts/sorries`, `git diff --check`, touched-Lean-file forbidden-marker
search, and direct axiom-footprint probes passed with the expected footprint.

This is not canonical endpoint labelling, geometric provenance for `tau`,
selected-entry preservation, chart/source membership, measure transport,
Jacobian comparison, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 Case 2 pre-measure from cardinalities

Reproduction:
`reproduction-a2-case2-endpoint-transport-premeasure-from-cardinalities.md`.
Statement card:
`statement-card-a2-case2-endpoint-transport-premeasure-from-cardinalities.md`.
Review:
`review-a2-case2-endpoint-transport-premeasure-from-cardinalities.md`.

Lean now exposes:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData_card_eq
```

It constructs the endpoint equivalences with
`case2EndpointTransportEquivs_of_card_eq` and then applies the existing
supplied-equivalence pre-measure theorem.  Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed via the
worktree-local `scripts/lb` command.  `scripts/sorries`, `git diff --check`,
touched-Lean-file forbidden-marker search, direct axiom probe, and xhigh
review passed.

This is not proof of the cardinality equalities, canonical endpoint labels,
selected-entry preservation, measure transport, Jacobian comparison,
integrability, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 Case 2 endpoint-transport chart-produced finite integral

Reproduction:
`reproduction-a2-case2-endpoint-transport-chart-produced-finite-integral.md`.
Statement card:
`statement-card-a2-case2-endpoint-transport-chart-produced-finite-integral.md`.

Lean now exposes endpoint-transport continuity and the Case 2
chart-produced finite-integral handoff:

```text
ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_endpointTransport
ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_endpointTransport_detChart_subtype
PaperEndpointFixedBaseRegularCoordinateSourceData.continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure
```

The continuity layer removes the separate `hsourceChart` hypothesis for the
exact endpoint-transported Case 2 source chart.  The finite-integral theorem is
still chart-produced only: the measure is the selected-entry signed-box
pushforward by `sourceChart`, and the theorem keeps local loss/density
hypotheses, source-data, positive radii, exponent inequality, endpoint
equivalences, and source-edge-family measurable/Borel structure explicit.

Focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`
passed with only the existing imported warning profile.

This does not identify an original source prior, compare Jacobians for an
external prior, prove source-rank coverage, normal crossings, pole order, or
RLCT.

## 2026-06-28 A2 fixed-base retained-passive pre-measure inputs

Reproduction:
`reproduction-a2-retained-passive-fixed-base-premeasure-inputs.md`.
Statement card:
`statement-card-a2-retained-passive-fixed-base-premeasure-inputs.md`.

Lean now packages the fixed-base retained-passive source-side inputs:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_retainedPassiveCoordinateData_edgeMatrix
```

From `hdet`, `hedge`, and `hdataFactor`, it returns both local-source
membership of `sourceChart y` and the source-readback residual-factor matrix
identity.  This is the consumer-shaped socket for an endpoint-transported Case
2 fixed-base source theorem.

Focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure` passed with
the existing imported warning profile.

This does not prove the edge-matrix realization hypothesis `hedge`, endpoint
transport of `edgeMatrix` or `sourceReadback`, measure transport, normal
crossings, pole order, or RLCT.

## 2026-06-28 A2 retained-passive endpoint transport

Reproduction:
`reproduction-a2-retained-passive-endpoint-transport.md`.
Statement card:
`statement-card-a2-retained-passive-endpoint-transport.md`.

Lean now exposes a retained-passive endpoint-transport layer:

```text
ChartLocalSuffixState.residualFactorProduct_endpointTransport
RetainedPassiveNonredundantCoordinateData.endpointTransport
RetainedPassiveNonredundantCoordinateData.endpointTransport_detChart
RetainedPassiveNonredundantCoordinateData.residualFactorProduct_C_endpointTransport
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
```

The generic theorem proves that an explicit residual-factor product commutes
with endpoint reindexing.  The retained-passive wrapper transports the
endpoint-dependent fields, preserves `detChart`, and transports the stored `C`
product.  The Case 2 specialization applies this to the explicit
selected-entry datum and rewrites the transported residual-coordinate readout
using `(e last).symm` and `(e 0).symm.trans eNext`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge` passed with
only the existing imported warning profile.

This is not `edgeMatrix` transport, source-recursive determinant-chart
transport, source-readback transport, fixed-base source-chart realization,
local-source membership, measure transport, normal crossings, pole order, or
RLCT.

## 2026-06-28 A2 Case 2 source-readback square-sum prehandoff

Reproduction:
`reproduction-a2-case2-source-readback-square-sum-prehandoff.md`.
Statement card:
`statement-card-a2-case2-source-readback-square-sum-prehandoff.md`.

Lean now exposes the square-sum of the explicit Case 2 source family's actual
source-readback product:

```text
aoyagiCoordinateSquareSum_case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryCenter_residual
```

This uses the source-readback center-matrix theorem, the
`AoyagiResidualBlockCoordinateIndex.value_matrix` inverse, square-sum reindexing
by `aoyagiCoordinateSquareSum_comp_equiv`, and the selected-entry residual
identity.  Xhigh `Beauvoir` identified this as the smallest useful pre-handoff
readout for local-measure consumers.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge` passed with
the existing imported warning profile.

This is not a finite-integral theorem.  It does not identify the explicit Case
2 source family with a fixed-base p.13 source chart and does not prove
local-source membership, source-prior pushforward, chart-image membership,
Jacobian density comparison, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 Case 2 retained-passive datum selected-entry center-matrix handoff

Reproduction:
`reproduction-a2-case2-retained-passive-data-center-matrix-handoff.md`.
Statement card:
`statement-card-a2-case2-retained-passive-data-center-matrix-handoff.md`.

Lean now exposes the explicit Case 2 selected-entry retained-passive datum's
stored `C` product in the selected-entry center-coordinate matrix shape:

```text
case2PostPivotSelectedEntryRetainedPassiveData_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
```

This is the datum-level analogue of the source-readback handoff.  It unfolds
the explicit datum and uses the finite constructed two-edge product equality.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge` passed with
the existing imported warning profile.

Xhigh fixed-base inspection by `Newton` found the next real blocker: fixed-base
retained-passive local-source and canonical chart-measure infrastructure is
indexed by `throughSubspaceEndpointComplementIndex`, while the explicit Case 2
datum is indexed by `case2PostPivotTwoEdgeDomain`.  A transport/reindex API for
retained-passive data, edge matrices, source readback, and residual products
along endpoint equivalences is still needed before claiming a fixed-base
local-source or measure theorem.

This is only a finite retained-passive datum equality.  It does not prove
fixed-base endpoint transport, local-source membership, source-prior
pushforward, chart-image membership, Jacobian density comparison, coverage,
normal crossings, pole order, or RLCT.

## 2026-06-28 A2 Case 2 source-readback selected-entry center-matrix handoff

Reproduction:
`reproduction-a2-case2-source-readback-selected-entry-center-matrix-handoff.md`.
Statement card:
`statement-card-a2-case2-source-readback-selected-entry-center-matrix-handoff.md`.

Lean now exposes the explicit Case 2 source family's actual source-readback
product in the selected-entry center-coordinate matrix shape:

```text
case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
```

This is the existing equality to `case2SuccessorSelectedEntryMatrix` with that
matrix unfolded.  It is intended as an exact `hfactor`-shape theorem for later
local-measure consumers.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge` passed with
the existing imported warning profile.
Xhigh review by `Galileo` passed:
`review-a2-case2-source-readback-selected-entry-center-matrix-handoff.md`.
`scripts/sorries`, `git diff --check`, touched-Lean-file forbidden-marker
search, and direct axiom-footprint probe passed; the new endpoint reports
`[propext, Classical.choice, Quot.sound]`.

This is only a finite readback equality.  It does not apply the family to a
fixed-base retained-passive local source, prove source-prior pushforward,
chart-image membership, Jacobian density comparison, arbitrary retained-passive
coverage, source-rank coverage, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 Case 2 explicit selected-entry source-family regularity

Reproduction:
`reproduction-a2-case2-explicit-selected-entry-source-family-regularity.md`.
Statement card:
`statement-card-a2-case2-explicit-selected-entry-source-family-regularity.md`.

Lean now proves finite-coordinate regularity of the explicit source family:

```text
continuous_case2SuccessorSelectedEntryMatrix
continuous_case2PostPivotSelectedEntryRetainedPassiveData
continuous_case2PostPivotSelectedEntryRetainedPassiveData_detChart_subtype
continuous_case2PostPivotSelectedEntrySourceEdgeFamily
measurable_case2PostPivotSelectedEntrySourceEdgeFamily
```

The successor selected-entry matrix is continuous entrywise because each entry
is a selected-entry chart-map coordinate.  The constructed retained-passive
datum has tuple `(1,0,0,C,1,0)`: the first `C` edge is constant and the second
is the submatrix recovered from the successor residual zero-extension.  The
source-family continuity is the determinant-chart subtype map composed with
the existing retained-passive `edgeMatrix` continuity theorem.  Measurability
follows from continuity.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge` passed with
the existing imported warning profile.
Xhigh review by `Gibbs` passed:
`review-a2-case2-explicit-selected-entry-source-family-regularity.md`.
Full `DLNFibre` build, `scripts/sorries`, `git diff --check`,
touched-Lean-file forbidden-marker search, and direct axiom-footprint probes
passed; the new endpoints report `[propext, Classical.choice, Quot.sound]`.

This is finite regularity only.  It does not prove source-prior pushforward,
Jacobian density comparison, arbitrary retained-passive coverage, source-rank
coverage, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 Case 2 explicit selected-entry source chart

Reproduction:
`reproduction-a2-case2-explicit-selected-entry-source-chart.md`.
Statement card:
`statement-card-a2-case2-explicit-selected-entry-source-chart.md`.

Lean now exposes the constructed Case 2 source-production map as explicit
functions of successor selected-entry coordinates, instead of only through
existential witnesses.  New product-side names:

```text
case2DisplayedPostPivotSourceResidualOfMatrix
case2DisplayedPostPivotFreeCprimeOfMatrix
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_sourceResidualOfMatrix_freeCprimeOfMatrix
```

New successor selected-entry names:

```text
case2SuccessorSelectedEntrySourceResidual
case2SuccessorSelectedEntrySourceCprime
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_successorSelectedEntrySource_eq
residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_successorSelectedEntrySource_eq
residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_successorSelectedEntrySource_ne_zero_of_yNext_pivot_ne_zero
```

New retained-passive source/readback names:

```text
case2PostPivotSelectedEntryRetainedPassiveData
case2PostPivotSelectedEntryRetainedPassiveData_detChart
case2PostPivotSelectedEntrySourceEdgeFamily
case2PostPivotSelectedEntrySourceEdgeFamily_sourceRecursiveDetChart
case2PostPivotSelectedEntrySourceReadback_eq_retainedPassiveData
case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix
case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_ne_zero_of_yNext_pivot_ne_zero
```

The construction sends `yNext` to the target successor selected-entry matrix,
zero-extends the right-reindexed target into the old residual data, uses the
reindexed identity as the free following factor, packages the result as
`case2PostPivotRetainedPassiveData`, and then takes its `edgeMatrix`.  The
source-recursive determinant-chart proof and readback equality are inherited
from the retained-passive determinant-chart inverse theorem.

The main equality theorem holds for all `yNext`; the nonzero theorem adds only
the expected displayed successor pivot nonzero hypothesis.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge` passed with
only pre-existing imported warning noise.  Full `DLNFibre` build passed with
the existing warning profile.  `scripts/sorries`, `git diff --check`,
touched-Lean-file forbidden-marker search, and direct axiom-footprint audit
passed; the new endpoints report `[propext, Classical.choice, Quot.sound]`.
Xhigh reproduction check by `Zeno` passed.  Implementation review by `Hypatia` passed.

This is a parametric constructed source family, not arbitrary retained-passive
coverage.  It does not prove continuity/measurability of the selected-entry to
source map, Jacobian or source-prior pushforward, source-rank coverage, normal
crossings, pole order, or RLCT.

## 2026-06-28 A2 Case 2 constructed source-readback production

Reproduction:
`reproduction-a2-case2-constructed-source-readback-production.md`.
Statement card:
`statement-card-a2-case2-constructed-source-readback-production.md`.

Lean now pushes the finite constructed Case 2 product through the actual
retained-passive source map/readback pair:

```text
exists_sourceRecursive_case2PostPivot_sourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero
exists_sourceRecursiveEdgeFamily_case2PostPivot_sourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero
```

From successor selected-entry coordinates with nonzero displayed successor
pivot coordinate, the theorem constructs a two-edge source family `E` in the
source-recursive determinant chart such that the actual `sourceReadback E`
residual-factor product is exactly the successor selected-entry matrix and is
nonzero.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge` passed with
only pre-existing imported warning noise.  Xhigh review by `Boole` passed:
`review-a2-case2-constructed-source-readback-production.md`.
Full `DLNFibre` build passed with pre-existing warning noise.  `scripts/sorries`,
`git diff --check`, changed-Lean-file forbidden-marker search, and direct
axiom-footprint audit passed; the new endpoints report
`[propext, Classical.choice, Quot.sound]`.

This is constructed source production only.  It does not prove arbitrary
retained-passive `sourceReadback E` factor alignment, source/prior measure
transport, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 Case 2 displayed product nonzero source production

Reproduction:
`reproduction-a2-case2-displayed-product-nonzero-source-production.md`.
Statement card:
`statement-card-a2-case2-displayed-product-nonzero-source-production.md`.

Lean now proves a finite constructed-data source-production theorem for the
continuing Case 2 displayed product.  New product-side names:

```text
case2SourceResidualBlockExtension
case2DisplayedPostPivotResidualBlock_sourceResidualBlockExtension
case2DisplayedPostPivotFreeCprimeOfFollowingFactor
exists_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_matrix_of_colEquiv
```

New selected-entry names:

```text
case2SuccessorSelectedEntryMatrix
case2SuccessorSelectedEntryMatrix_ne_zero_of_yNext_pivot_ne_zero
exists_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero
exists_residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero
```

Given successor selected-entry coordinates `yNext` and a nonzero displayed
successor pivot coordinate at `(J+2,J+2)`, the construction zero-extends the
target matrix reindexed to successor residual columns, so the old displayed
Schur complement is the target matrix.  It chooses the free following factor
as the reindexed identity.  Therefore the post-pivot free two-edge product is
the successor selected-entry matrix and is nonzero.

Focused builds of `DLNFibre.DLN.Aoyagi.Case2ResidualFactorProduct` and
`DLNFibre.DLN.Aoyagi.Case2ResidualSelectedEntryChartBridge` passed with only
pre-existing imported warning noise.  Xhigh review by `Wegener` passed:
`review-a2-case2-displayed-product-nonzero-source-production.md`.
Full `DLNFibre` build passed with pre-existing warning noise.  `scripts/sorries`,
`git diff --check`, changed-Lean-file forbidden-marker search, and direct
axiom-footprint audit passed; the new public endpoints report
`[propext, Classical.choice, Quot.sound]`.

This is constructed finite data only.  It does not prove displayed-product
nonzeroness for an arbitrary retained-passive `sourceReadback` point, factor
alignment, measure transport, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 retained-passive Case 2 all-pivot selected-entry adapter

Statement card:
`statement-card-a2-retained-passive-case2-all-pivot-selected-entry-adapter.md`.

Lean now has all-pivot retained-passive Case 2 adapters:

```text
exists_pivot_residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_of_ne_zero
exists_pivot_residualFactorProduct_ofTopologyTuple_eq_selectedEntryCenter_matrix_of_case2PostPivot_of_ne_zero
exists_pivot_aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_case2PostPivot_of_ne_zero
```

These replace a supplied selected pivot and `hpivot` by the single hypothesis
that the displayed post-pivot two-edge product matrix is nonzero.  The proof
uses the existing finite all-pivot selected-entry inverse
`SelectedEntrySignedBox.CenterCoord.exists_pivot_matrix_eq_chartMap_of_ne_zero`
to choose a nonzero displayed matrix entry as the pivot, then feeds the
resulting entrywise chart readout into the already banked Case 2 bridges.

No fresh Aoyagi source reproduction was needed: this is a specialization of
the already reproduced finite all-pivot selected-entry calculation.  Focused
builds of `DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge`
and `DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed with
only pre-existing imported warning noise.  `scripts/sorries`,
`git diff --check`, touched-file forbidden-marker search, direct
axiom-footprint audit, and xhigh review by `Halley` passed.  Review:
`review-a2-retained-passive-case2-all-pivot-selected-entry-adapter.md`.

This removes fixed-pivot selection after displayed-product nonzeroness is
known.  It does not prove displayed-product nonzeroness, actual retained-passive
source/readback factor alignment, source/prior transport, normal crossings,
pole order, or RLCT.

## 2026-06-28 A2 retained-passive raw-order source-chart composition

Reproduction:
`reproduction-a2-retained-passive-raw-order-source-chart-composition.md`.
Statement card:
`statement-card-a2-retained-passive-raw-order-source-chart-composition.md`.

Lean now exposes the direct determinant-chart source presentation:

```text
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_eq_sourceEdgeFamilyOfData
```

For `z ∈ topologyTupleDetChartSet`, the public raw-order source chart applied
to `topologyTupleEdgeRawOrder z` is exactly the direct fixed-base source family
realized from `ofTopologyTuple z`.  The proof is the existing inverse theorem
`topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder` plus unfolding of
the raw-order source chart.

Focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalSource` passed.
Xhigh review by `Godel the 3rd` passed:
`review-a2-retained-passive-raw-order-source-chart-composition.md`.  Direct
axiom-footprint check reports `[propext, Classical.choice, Quot.sound]`.
This is not retained-passive-to-selected-entry factor alignment, pivot
provenance, all-pivot coverage, original source-rank coverage, measure/prior
transport, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 selected-entry all-pivot nonzero coverage

Reproduction:
`reproduction-a2-selected-entry-all-pivot-nonzero-coverage.md`.
Statement card:
`statement-card-a2-selected-entry-all-pivot-nonzero-coverage.md`.

Lean now has the finite all-pivot selected-entry inverse:

```text
SelectedEntrySignedBox.CenterCoord.exists_pivot_chartMap_eq_value_of_ne_zero
SelectedEntrySignedBox.CenterCoord.exists_pivot_matrix_eq_chartMap_of_ne_zero
```

The center-coordinate theorem chooses a nonzero coordinate of a nonzero center
value and applies the existing fixed-pivot inverse.  The matrix theorem chooses
a nonzero residual-matrix entry, sends it through the supplied
residual-coordinate equivalence as the pivot, and applies the fixed-pivot
matrix inverse.

Focused build of `DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure` passed
with pre-existing imported linter warning noise.  Xhigh review by
`Boyle the 3rd` passed:
`review-a2-selected-entry-all-pivot-nonzero-coverage.md`.  Direct
axiom-footprint check reports `[propext, Classical.choice, Quot.sound]`.

This removes fixed-pivot provenance only at the finite selected-entry layer
once nonzeroness is known.  It does not prove retained-passive source/readback
nonzero production, Aoyagi displayed-factor alignment, source/prior transport,
normal crossings, pole order, or RLCT.

## 2026-06-28 post-interruption source-readout frontier

Reproduction:
`reproduction-a2-retained-passive-to-selected-entry-fixed-pivot-boundary.md`.

The worktree was rechecked after interruption: branch
`expedition/aoyagi-rlct` is clean at `86894b6a` and aligned with
`origin/expedition/aoyagi-rlct`; `origin/dev` is already an ancestor of this
branch.  `scripts/sorries` reported zero forbidden markers and
`git diff --check` was clean before new documentation edits.

Xhigh read-only scouts and the controller PDF check agree that the current
A2 retained-passive-to-selected-entry source-readout frontier is not another
wrapper around `sourceReadback`.  Existing Lean already has source-readback
recovery and residual readout.  The missing source-moving fields are:

- factor alignment for an actual retained-passive source/readback point:
  `(sourceReadback E).C 1` is the displayed post-pivot residual block and
  `(sourceReadback E).C 0` is the following free factor;
- pivot provenance, or an all-pivot finite selected-entry cover;
- later source/prior transport if the route needs an original source measure.

Aoyagi pp. 10-13 support the retained-passive signs and product order:
`F2 = -A1^-1 A2`, `F3 = -A3 A1^-1`, and
`C4 = A4 - A3 A1^-1 A2`.  The p.13 literal product-difference lower-right
block is `product C - F3 F2`, so identifying the literal square sum with the
cleaned residual square sum is overclaiming without a comparison/generator
argument.  Aoyagi pp. 19-22 support the fixed selected-pivot Case 2 chart and
the two-edge order "post-pivot residual block then following factor"; they do
not prove that this fixed pivot is nonzero globally.

Controller decision: do not add a theorem that only sets
`retainedData y := sourceReadback E_y` while keeping `hD`, `hF`, and `hpivot`.
The next Lean move must remove one of those fields or expose a direct
source-chart identity needed by such a construction.

## 2026-06-28 A2 retained-passive Case 2 pivot-nonzero selected-entry hardening

Existing reproduction/card updated:
`reproduction-a2-retained-passive-case2-pivot-nonzero-source-readout.md`,
`statement-card-a2-retained-passive-case2-pivot-nonzero-source-readout.md`.

Lean now has a matrix-level fixed-pivot selected-entry inverse:

```text
SelectedEntrySignedBox.CenterCoord.exists_matrix_eq_chartMap_of_pivot_ne_zero
```

and retained-passive two-edge Case 2 consumers:

```text
exists_residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_pivot_ne_zero
exists_residualFactorProduct_ofTopologyTuple_eq_selectedEntryCenter_matrix_of_case2PostPivot_pivot_ne_zero
exists_aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_case2PostPivot_pivot_ne_zero
```

These replace a full entrywise selected-entry readout by a single supplied
nonzero entry of the displayed post-pivot two-edge product, after the explicit
product-coordinate equivalence.  Focused builds of
`SelectedEntrySignedBoxMeasure`, `RetainedPassiveCase2SelectedEntryChartBridge`,
and `RetainedPassiveCase2LocalJacobianMeasure` passed; the full `DLNFibre`
build, `scripts/sorries`, `git diff --check`, diff-only forbidden-marker
search, and direct logical-footprint audit also passed.  The new theorem
endpoints depend only on `[propext, Classical.choice, Quot.sound]`.  This is
still finite
selected-entry inverse algebra only: the nonzero pivot, retained-passive source
production, original measure transport, normal crossings, pole order, and RLCT
remain unproved.

## 2026-06-28 A2 selected-entry target-image residual hypotheses

Reproduction:
`reproduction-a2-selected-entry-target-image-residual-hypotheses.md`.
Statement card:
`statement-card-a2-selected-entry-target-image-residual-hypotheses.md`.

Lean now pushes the selected-entry weighted source-box theorem through the
finite selected-entry chart map:

```text
SelectedEntrySignedBox.CenterCoord.
  aoyagiCoordinateSquareSum_pos_ae_and_lintegral_rpow_neg_restrict_chartMap_image
```

For positive signed-box radii, `t >= 0`, and
`2 * t < ((center.erase pivot.1).card : ℝ) + 1`, the theorem proves target
square-sum positivity almost everywhere and finite lower integral of
`ofReal ((aoyagiCoordinateSquareSum x)^(-t))` under
`volume.restrict (chartMap pivot '' signedBoxSet R)`.

The proof uses the selected-entry chart pushforward, the identity
`residual pivot y = aoyagiCoordinateSquareSum (chartMap pivot y)`, and the
landed weighted source-box theorem.  Positivity transfers by `ae_map_iff`;
finite integrability transfers by `lintegral_map_le`.

Focused build of `DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure` passed
with pre-existing imported warning noise.  Xhigh review by `Lagrange the 3rd`
passed after a statement-card cast typo fix:
`review-a2-selected-entry-target-image-residual-hypotheses.md`.
Post-recovery full `DLNFibre` build, `scripts/sorries`, `git diff --check`,
diff-only forbidden-marker search, and theorem logical-footprint audit passed.
The new theorem depends only on `[propext, Classical.choice, Quot.sound]`.

Nonclaims: no retained-passive determinant-chart source production, no
retained-passive-to-selected-entry pushforward, no original prior transport,
no normal crossings, no pole order, and no RLCT.

## 2026-06-28 A2 selected-entry weighted signed-box residual hypotheses

Reproduction:
`reproduction-a2-selected-entry-weighted-box-residual-hypotheses.md`.
Statement card:
`statement-card-a2-selected-entry-weighted-box-residual-hypotheses.md`.

Lean now proves the selected-entry model's own weighted signed-box residual
field in `SelectedEntrySignedBoxMeasure.lean`:

```text
SelectedEntrySignedBox.CenterCoord.
  residual_pos_ae_and_lintegral_rpow_neg_withDensity_sourceDensity
```

For positive signed-box radii, `t >= 0`, and
`2 * t < ((center.erase pivot.1).card : ℝ) + 1`, the theorem proves residual
positivity almost everywhere and finite lower integral of
`ofReal ((residual pivot y)^(-t))` under the signed-box product measure
weighted by `ofReal (sourceDensity pivot y)`.

The pen-and-paper calculation is the selected-entry identity
`residual = |pivot|^2 * unit` with `unit >= 1`, and
`sourceDensity = |pivot|^(card(center.erase pivot.1))`.  Thus only the pivot
coordinate contributes a nontrivial integrability inequality.

Focused build of `DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure` passed
with pre-existing imported warning noise.  Full `DLNFibre` build passed with
pre-existing warning noise.  Xhigh review by `Maxwell the 3rd` passed:
`review-a2-selected-entry-weighted-box-residual-hypotheses.md`.  The new
theorem's logical footprint is `[propext, Classical.choice, Quot.sound]`.

Nonclaims: no retained-passive determinant-chart source production, no
pushforward from retained-passive coordinates to selected-entry signed-box
coordinates, no original prior transport, no normal crossings, no pole order,
and no RLCT.

## 2026-06-28 A2 retained-passive raw-order source-chart homeomorphism

Reproduction:
`reproduction-a2-retained-passive-raw-order-source-chart-homeomorph.md`.
Statement card:
`statement-card-a2-retained-passive-raw-order-source-chart-homeomorph.md`.

Lean now packages the reduced fixed-base raw-order retained-passive source
chart as an actual homeomorphism:

```text
detChart_topologyTupleDetChartSet_homeomorph
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph_apply
```

The first helper identifies determinant-chart retained-passive data with
determinant-chart topology tuples.  The second composes that with the existing
raw-order chart homeomorphism and the existing fixed-base source-edge-family
homeomorphism.  The apply theorem exposes the `toFun` as the public canonical
raw-order source chart.

Focused builds of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalSource` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure` passed.  Full
`DLNFibre` build passed with pre-existing warning noise.  `scripts/sorries`,
`git diff --check`, and touched-file forbidden-marker search passed.  Xhigh
review by `Raman the 3rd` passed:
`review-a2-retained-passive-raw-order-source-chart-homeomorph.md`.

Nonclaims: no original DLN source-rank coverage, no rank-stratum coverage, no
original source prior or measure transport, no new Jacobian theorem, no
residual positivity/integrability, no normal crossings, no pole order, and no
RLCT.

## 2026-06-28 A2 retained-passive raw-order source-chart image

Reproduction:
`reproduction-a2-retained-passive-raw-order-source-chart-image.md`.
Statement card:
`statement-card-a2-retained-passive-raw-order-source-chart-image.md`.

Lean now exposes the canonical raw-order retained-passive source map and its
image theorem in `RetainedPassiveLocalSource.lean`:

```text
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13RawOrderSourceChart_eq
image_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_eq_sourceEdgeFamilySet
```

The readout theorem proves that, on
`topologyTupleRawOrderSourceRecursiveDetChartSet`, the fixed-base edge matrices
of the canonical raw-order source chart are exactly
`edgeFamilyOfRawOrderTuple y`.  The image theorem proves that this source chart
maps the raw-order source-recursive determinant chart onto exactly
`paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U0 hU0`.
The older private canonical realization helper in
`RetainedPassiveLocalJacobianMeasure.lean` now delegates to this public theorem.

Focused builds of
`DLNFibre.DLN.Aoyagi.RetainedPassiveLocalSource` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure` passed.
`scripts/sorries`, `git diff --check`, and the touched Lean file
forbidden-marker search passed.  Full `DLNFibre` build passed with
pre-existing warning noise.  Xhigh review by `Aristotle the 3rd` passed:
`review-a2-retained-passive-raw-order-source-chart-image.md`.

Nonclaims: no original DLN source-rank coverage, no original source prior or
measure transport, no Jacobian theorem beyond existing chart densities, no
residual zero-locus/nullity, no chart-side a.e. positivity, no finite
negative-power integrability, no normal crossings, no pole order, and no RLCT.

## 2026-06-28 A2 retained-passive Case 2 canonical chart selected-entry square-sum

Reproduction:
`reproduction-a2-retained-passive-case2-canonical-chart-selected-entry-square-sum.md`.
Statement card:
`statement-card-a2-retained-passive-case2-canonical-chart-selected-entry-square-sum.md`.

Lean target:

```text
aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_case2PostPivot_entrywise
```

The theorem lives in the new leaf module
`RetainedPassiveCase2LocalJacobianMeasure.lean`.  It composes the two-edge
`ofTopologyTuple` Case 2 selected-entry residual-factor product theorem with
the canonical chart selected-entry square-sum bridge.  The previous supplied
matrix hypothesis

```text
residualFactorProduct (ofTopologyTuple z).C (Fin.last 2) 0
  = matrix (fun c => CenterCoord.chartMap pivot y (residualCoordEquiv c))
```

is replaced by the displayed Case 2 factor identities for `(ofTopologyTuple
z).C 1` and `(ofTopologyTuple z).C 0`, plus the displayed two-edge product
entrywise readout.  The theorem is specialized to `M = 1`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.
Full `DLNFibre` build passed with pre-existing warning noise.  `scripts/sorries`,
`git diff --check`, and the touched Lean file forbidden-marker search passed.
Xhigh review by `Lorentz the 3rd` found no Lean/formal issue and one stale
documentation-status issue, corrected.  Review:
`review-a2-retained-passive-case2-canonical-chart-selected-entry-square-sum.md`.

Nonclaims: no arbitrary full-suffix selected-entry matrix identity, no outside
factor absorption, no residual zero-locus nullity, no chart-side a.e.
positivity, no finite negative-power integrability, no source-density/prior
transport, no normal crossings, no pole order, and no RLCT.

## 2026-06-28 A2 retained-passive two-edge `ofTopologyTuple` selected-entry product adapter

Reproduction:
`reproduction-a2-retained-passive-two-edge-ofTopologyTuple-selected-entry-product.md`.
Statement card:
`statement-card-a2-retained-passive-two-edge-ofTopologyTuple-selected-entry-product.md`.

Lean target:

```text
residualFactorProduct_ofTopologyTuple_eq_selectedEntryCenter_matrix_of_case2PostPivot_entrywise
```

This is a narrow adapter from the retained-passive topology tuple wrapper to
the existing two-edge data-level Case 2 selected-entry product theorem.  The
scope is exactly the whole suffix when the suffix has two edges (`M = 1`).
It must not be used to collapse an arbitrary longer canonical suffix product;
outside factors in longer suffixes remain explicit.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge` passed.
`scripts/sorries`, `git diff --check`, and the touched Lean file
forbidden-marker search passed.  Xhigh review by `Noether the 3rd` passed.
Review:
`review-a2-retained-passive-two-edge-ofTopologyTuple-selected-entry-product.md`.

## 2026-06-28 A2 canonical retained-passive chart residual readout

Lean now identifies the canonical retained-passive chart-side residual
expression on the determinant chart:

```text
paperEndpointFixedBaseResidualBlockCoordinateMap_retainedPassiveP13Canonical_chart_eq_residualProduct
paperEndpointFixedBaseResidualBlockCoordinateMap_retainedPassiveP13Canonical_chart_eq_residualFactorProduct
```

The first theorem rewrites

```text
paperEndpointFixedBaseResidualBlockCoordinateMap W B U0 hU0 id
  (sourceChart (topologyTupleEdgeRawOrder z))
```

as the coordinate readout of
`ChartLocalSuffixState.residualProduct (topologyTupleEdgeMatrix z) last 0`.
The second theorem rewrites it further to the residual-factor product of the
stored retained-passive chart blocks `(ofTopologyTuple z).C`.

The proof uses the determinant-chart map into the raw-order source-recursive
chart, the canonical source-chart realisation theorem, raw-order tuple readout,
the fixed-base residual readout theorem, and determinant-chart source-readback
recovery.

Focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure`
and full `DLNFibre` build passed, the latter with pre-existing warning noise.
`scripts/sorries`, `git diff --check`, and the touched-file forbidden-marker
search passed.  Xhigh review by `Zeno the 3rd` passed.

Nonclaims: no residual zero-locus nullity, no chart-side a.e. positivity, no
finite residual negative-power integrability, no monomial lower bound, no
source-density/prior transport, no normal crossings, no pole order, and no
RLCT.

## 2026-06-28 A2 canonical retained-passive chart selected-entry square-sum bridge

Lean now has the pointwise square-sum bridge from the canonical
retained-passive chart residual readout to the selected-entry center residual:

```text
aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_residualFactorProduct_eq_matrix
```

The theorem assumes the genuinely missing matrix identity:

```text
residualFactorProduct (ofTopologyTuple z).C last 0
  = matrix (fun c => CenterCoord.chartMap pivot y (residualCoordEquiv c)).
```

Under that hypothesis and `z ∈ topologyTupleDetChartSet`, the canonical
chart-side residual square-sum equals `CenterCoord.residual pivot y`.  The
proof combines the banked canonical residual-factor readout with
`value_matrix`, finite reindexing by `residualCoordEquiv`, and the
selected-entry residual square-sum lemma.

Focused `RetainedPassiveLocalJacobianMeasure` build passed.  `scripts/sorries`,
`git diff --check`, and Lean touched-file forbidden-marker search passed.
Xhigh review by `Dirac the 3rd` passed after a statement-card status
correction.

Nonclaims: no full suffix selected-entry matrix identity, residual zero-locus
nullity, chart-side a.e. positivity, finite negative-power integrability,
source-density/prior transport, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 canonical retained-passive local Jacobian measure handoffs

After the retained-passive formal/product-density change of variables, Lean
landed the canonical local-source COV and product-density residual/finite
integral chain in `RetainedPassiveLocalJacobianMeasure.lean`.

Key landed names:

```text
retainedPassiveP13CanonicalSourceChart_realize
measure_map_restrict_retainedPassiveP13CanonicalLocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet
measure_map_restrict_retainedPassiveP13CanonicalLocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet
residualSourceHypotheses_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_continuousAt_pos_density
measurableSet_residualSquareSum_pos_retainedPassiveP13Canonical_id
residualSourceHypotheses_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_of_chartSide
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_of_chartSide
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_continuousAt_pos_density_of_chartSide
```

The canonical source-measure and product-density transport are now internal to
these handoffs, and source-side residual positive-set measurability is
discharged for the identity edge-family source.  Chart-side residual a.e.
positivity and finite negative-power integrability remain explicit hypotheses.

Focused local builds, full `DLNFibre`, `scripts/sorries`, `git diff --check`,
forbidden-marker searches, and xhigh reviews passed for the handoffs through
`81b097a2`.

## 2026-06-28 A2 retained-passive formal-density change of variables

Lean now has a retained-passive formal/product-density specialization of the
raw-order change-of-variables theorem in
`RetainedPassiveCoordinatesJacobianMeasure.lean`:

```text
retainedPassiveFormalRawOrderJacobianProductAbsDetAt
map_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_eq_restrict_rawSourceChart_posTail
map_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_eq_restrict_rawSourceChart_zeroTail
map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart_posTail
map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart_zeroTail
```

These theorems replace the abstract `topologyTupleEdgeRawOrderFDerivAbsDet`
density a.e. on the determinant chart by the formal determinant, or by its
solved-`A1` product formula, then reuse the existing retained-passive
change-of-variables theorem.

Focused build of the new module passed.  The top-level `DLNFibre` build also
passed, with only pre-existing warning noise.  `scripts/sorries`,
`git diff --check`, and code-only forbidden-marker search passed.

Nonclaims: no original-source prior, no signed-box source-density
identification, no normal crossings, no pole order, and no RLCT.

## 2026-06-28 A2 full target normaliser determinant bridge

Lean now has the full raw-tuple target-normaliser equality in the zero-tail and
positive-tail cases:

```text
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3PosShear_fderiv_eq_formalRawOrderJacobianAt
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3ZeroShear_fderiv_eq_formalRawOrderJacobianAt
```

The proof assembles the existing component bridges for `A1passive`, `(F2,C)`,
`A3passive`, `Ctop`, and `F3`; the final `F3` shear preserves all earlier
components.  A small private helper records that the `Ctop` stage preserves
`A3passive`.

The conditional determinant bridge is now instantiated:

```text
topologyTupleEdgeRawOrderFDerivAbsDet_eq_formalRawOrderAbsDetAt_posTail
topologyTupleEdgeRawOrderFDerivAbsDet_eq_formalRawOrderAbsDetAt_zeroTail
topologyTupleEdgeRawOrderFDerivAbsDet_product_eq_posTail
topologyTupleEdgeRawOrderFDerivAbsDet_product_eq_zeroTail
```

Focused
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` build passed.
`scripts/sorries`, `git diff --check`, and code-only forbidden-marker search
passed.

Nonclaims: no measure transport, normal crossings, pole order, or RLCT.  The
zero-tail and positive-tail theorems remain separate statements.

## 2026-06-28 A2 positive-tail post-`Ctop` `F3` shear

Lean now has the positive-tail `F3` raw-tuple shear after the edge-pair,
`A1passive`, and `Ctop` stages:

```text
retainedPassivePostCtopF3PosShearRawTupleLinearEquivAt
retainedPassivePostCtopF3PosShearRawTupleLinearEquivAt_apply
retainedPassivePostCtopF3PosShearRawTupleLinearEquivAt_det_eq_one
retainedPassivePostCtopF3PosShearRawTupleLinearEquivAt_abs_det_eq_one
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3PosShearRawTupleLinearEquivAt
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3PosShearRawTupleLinearEquivAt_apply
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3PosShearRawTupleLinearEquivAt_abs_det_eq_one
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3PosShear_fderiv_F3_eq_formalRawOrderJacobianAt
```

The correction uses the post-`Ctop` recursive `dEarly` map and the terminal
staged passive `A1` coordinate.  The determinant is one by the `F3 × rest`
upper-shear calculation, and the component bridge reduces to the existing
target-only positive-tail `F3` theorem.

Focused
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` build passed.
`scripts/sorries`, `git diff --check`, and code-only forbidden-marker search
passed.

Nonclaims: no single full raw-tuple equality yet, no actual Frechet determinant
equality, no measure transport, no normal crossings, no pole order, and no
RLCT.

## 2026-06-28 A2 post-`Ctop` recursive `dEarly` comparison

Lean now has the private comparison chain from the post-`Ctop` lower-left
early-tail recursion on the `F3`-focused rest tuple to the existing target-only
recursion:

```text
retainedPassivePostCtopCnextFDerivLinearMapAt_after_T123_eq_targetStaged
retainedPassivePostCtopLowerLeftTailStepCoreLinearMapAt_apply
retainedPassivePostCtopLowerLeftTailStepCoreLinearMapAt_after_T123_eq_targetOnly
retainedPassivePostCtopLowerLeftProductTailFDerivLinearMapAt_after_T123_eq_targetOnly
```

The recursive bridge proves, for every `m ≤ M + 1`, that evaluating
`retainedPassivePostCtopLowerLeftProductTailFDerivLinearMapAt hz m hm` on the
rest of `T123 ((fderiv raw z) v)` gives
`retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt hz ((fderiv raw z) v) m hm`.

Focused
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` build passed.
`scripts/sorries`, `git diff --check`, and code-only forbidden-marker search
passed.

Nonclaims: no positive-tail `F3` shear yet, no determinant-one package for it,
no full target normalisation, no actual Frechet determinant equality, no
measure transport, no normal crossings, no pole order, and no RLCT.

## 2026-06-28 A2 post-`Ctop` suffix comparison bridges

Lean now has three further private post-`Ctop` comparison lemmas in
`RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassivePostCtopSolvedA1TangentLinearMapAt_after_T123_eq_targetStaged
retainedPassivePostCtopSolvedA1SuffixFDerivLinearMapAt_after_T123_eq_targetStaged
retainedPassivePostCtopCSuffixFDerivLinearMapAt_after_T123_eq_targetStaged
```

These compare the post-`Ctop` rest tuple after `T123 ((fderiv raw z) v)` with
the existing target-staged solved-`A1` tangent, solved-`A1` suffix derivative,
and stored-`C` suffix derivative on `(fderiv raw z) v`.

Focused
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` build passed.
`scripts/sorries`, `git diff --check`, and code-only forbidden-marker search
passed.

Nonclaims: no `Cnext` comparison, no lower-left one-step comparison, no
recursive `dEarly_postC` comparison, no positive-tail `F3` shear, no determinant
equality, measure transport, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 post-`Ctop` first comparison bridges

Lean now has the first private comparison slice for the post-`Ctop`
positive-tail bridge in `RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassiveTargetEdgePairThenA1passiveThenCtopShearRawTupleLinearEquivAt_F2C
rawEdgeTupleA3_retainedPassiveTargetEdgePairThenA1passiveThenCtopShearRawTupleLinearEquivAt
retainedPassivePostCtopSourceCAtLinearMapAt_after_T123_eq_targetRecovered
retainedPassivePostCtopCurrentSolvedA1TangentLinearMapAt_after_T123_eq_targetOnly
```

These bridge the basic readout layer and the current solved-`A1` tangent on
actual derivative targets.  Focused
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` build passed.

Nonclaims: solved-`A1` suffix comparison, `C` suffix/`Cnext` comparison,
lower-left one-step comparison, recursive `dEarly_postC` comparison, positive
tail `F3`, determinant equality, measure transport, normal crossings, pole
order, and RLCT remain open.

## 2026-06-28 A2 post-`Ctop` lower-left recursion scaffolding

Lean now has the private post-`Ctop` `C` suffix, `Cnext`, lower-left one-step
core, and recursive lower-left product-tail linear-map package in
`RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassivePostCtopCSuffixFDerivLinearMapAt
retainedPassivePostCtopCSuffixFDerivLinearMapAt_self
retainedPassivePostCtopCSuffixFDerivLinearMapAt_step_apply
retainedPassivePostCtopCnextFDerivLinearMapAt
retainedPassivePostCtopLowerLeftTailStepCoreLinearMapAt
retainedPassivePostCtopLowerLeftProductTailFDerivLinearMapAt
retainedPassivePostCtopLowerLeftProductTailFDerivLinearMapAt_self
retainedPassivePostCtopLowerLeftProductTailFDerivLinearMapAt_step
```

This package reads source `C` by formal inverse on post-`Ctop` `(F2,C)` fields
and uses only post-`Ctop` rest-tuple readers for variable slots.  Static product
factors are frozen at `z`.

Focused `DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` build passed.
`scripts/sorries`, `git diff --check`, and code-only forbidden-marker search
passed.  Xhigh review of the preceding solved-`A1` suffix checkpoint by
`Darwin the 2nd` passed.

Nonclaims: no bridge yet from this recursion on `T123(Dzv)` to the existing
target-only lower-left recursion on `Dzv`; no positive-tail `F3` shear; no
determinant equality, measure transport, normal crossings, pole order, or
RLCT.

## 2026-06-28 A2 post-`Ctop` solved-`A1` suffix scaffolding

Lean now has a private post-`Ctop` solved-`A1` tangent and suffix derivative
package in `RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassivePostCtopSolvedA1TangentLinearMapAt
retainedPassivePostCtopSolvedA1TangentLinearMapAt_zero_apply
retainedPassivePostCtopSolvedA1TangentLinearMapAt_succ_apply
retainedPassivePostCtopSolvedA1SuffixFDerivLinearMapAt
retainedPassivePostCtopSolvedA1SuffixFDerivLinearMapAt_self
retainedPassivePostCtopSolvedA1SuffixFDerivLinearMapAt_step_apply
```

The zero solved-`A1` tangent reads the post-`Ctop` target coordinate directly,
and successor tangents read staged passive `A1`.  The suffix recursion includes
the terminal solved factor for later `dPsucc` use.

Focused `DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` build passed.
`scripts/sorries`, `git diff --check`, and code-only forbidden-marker search
passed.

Nonclaims: no comparison bridge for the suffix package yet; no `Cnext`, one-step
lower-left core, recursive `dEarly_postC`, positive-tail `F3` shear, determinant
equality, measure transport, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 post-`Ctop` positive-tail readout scaffolding

Lean now has the first private post-`Ctop` positive-tail helper layer in
`RetainedPassiveCoordinatesJacobian.lean`.  This is scaffolding for
`dEarly_postC`, not a positive-tail `F3` bridge.

New private helpers:

```text
retainedPassiveRawF3RestA1passiveLinearMapAt
retainedPassiveRawF3RestF2CProjectionLinearMapAt
retainedPassiveRawF3RestA3passiveLinearMapAt
retainedPassiveRawF3RestA3passiveLinearMapAt_apply_rawTupleRest
retainedPassivePostCtopTailFDerivLinearMapAt
retainedPassivePostCtopTailFDerivLinearMapAt_self
retainedPassivePostCtopTailFDerivLinearMapAt_step_apply
retainedPassivePostCtopTailFDerivLinearMapAt_fderiv_after_T123_eq_targetStaged
retainedPassivePostCtopSourcePairLinearMapAt
retainedPassivePostCtopSourceCLinearMapAt
retainedPassivePostCtopSourceCLinearMapAt_apply
retainedPassivePostCtopSourceCAtLinearMapAt
retainedPassivePostCtopSourceCAtLinearMapAt_apply
retainedPassivePostCtopCurrentSolvedA1TangentLinearMapAt
retainedPassivePostCtopCurrentSolvedA1TangentLinearMapAt_zero_apply
retainedPassivePostCtopCurrentSolvedA1TangentLinearMapAt_succ_apply
```

The source `C` readout is the formal inverse of the already normalised
post-edge `(F2,C)` fields.  The zero-index solved-`A1` tangent reads the
post-`Ctop` target coordinate itself:

```text
Ctop - Tail⁻¹ * dTail_postC * Tail⁻¹ * coord.Ctop.
```

Focused `DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` build passed.
`scripts/sorries`, `git diff --check`, and code-only forbidden-marker search
passed.

Nonclaims: no recursive `dEarly_postC`, no positive-tail `F3` shear, no full
raw-tuple target normalisation, no actual Frechet determinant equality, no
measure transport, no normal crossings, no pole order, and no RLCT.

## 2026-06-28 A2 post-`Ctop` `F3` zero-tail bridge

Reproduction:
`reproduction-a2-retained-passive-post-ctop-f3-shear.md`.
Statement card:
`statement-card-a2-retained-passive-post-ctop-f3-zero-shear.md`.
Review:
`review-a2-retained-passive-post-ctop-f3-zero-shear.md`,
PASS by xhigh `Nietzsche the 2nd`.

Lean now proves in `RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassivePostCtopF3ZeroShearRawTupleLinearEquivAt
retainedPassivePostCtopF3ZeroShearRawTupleLinearEquivAt_apply
retainedPassivePostCtopF3ZeroShearRawTupleLinearEquivAt_det_eq_one
retainedPassivePostCtopF3ZeroShearRawTupleLinearEquivAt_abs_det_eq_one
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3ZeroShearRawTupleLinearEquivAt
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3ZeroShearRawTupleLinearEquivAt_apply
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3ZeroShearRawTupleLinearEquivAt_abs_det_eq_one
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3ZeroShear_fderiv_F3_eq_formalRawOrderJacobianAt
```

The single-edge post-`Ctop` `F3` shear changes only `F3` by
`coord.F3 * Ctop`.  It is determinant one after regrouping the raw tuple as
`F3 × rest` and applying the upper-shear determinant calculation.  Composed
after the first three target-side stages, it proves zero-tail `F3` component
agreement with the formal raw-order Jacobian.

Focused `DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` build passed.
The full `DLNFibre` build passed with pre-existing warning noise.
`scripts/sorries`, `git diff --check`, direct axiom audit, and xhigh review
passed; the new public theorem names have axiom footprint
`[propext, Classical.choice, Quot.sound]`.

This is not the positive-tail `F3` bridge, full target normalisation, full
raw-tuple equality, actual Frechet determinant equality, measure transport,
normal crossings, pole order, or RLCT.

## 2026-06-28 A2 edge-pair, `A1passive`, then `Ctop` component bridge

Reproduction:
`reproduction-a2-retained-passive-post-a1passive-ctop-shear.md`.
Statement card:
`statement-card-a2-retained-passive-edge-pair-a1passive-ctop-bridge.md`.
Review:
`review-a2-retained-passive-edge-pair-a1passive-ctop-bridge.md`,
PASS by xhigh `Popper the 2nd`.

Lean now proves in `RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassivePostA1passiveCtopShearRawTupleLinearEquivAt
retainedPassivePostA1passiveCtopShearRawTupleLinearEquivAt_apply
retainedPassivePostA1passiveCtopShearRawTupleLinearEquivAt_det_eq_one
retainedPassivePostA1passiveCtopShearRawTupleLinearEquivAt_abs_det_eq_one
retainedPassiveTargetEdgePairThenA1passiveThenCtopShearRawTupleLinearEquivAt
retainedPassiveTargetEdgePairThenA1passiveThenCtopShearRawTupleLinearEquivAt_apply
retainedPassiveTargetEdgePairThenA1passiveThenCtopShearRawTupleLinearEquivAt_abs_det_eq_one
retainedPassiveTargetEdgePairThenA1passiveThenCtopShear_fderiv_Ctop_eq_formalRawOrderJacobianAt
```

The new post-`A1passive` `Ctop` shear changes only the `Ctop` raw-tuple field.
It reads the successor `F2` family from the formal inverse of the already
normalised `(F2,C)` fields, reads `rawEdgeTupleA3` from the unchanged
lower-left raw tuple, and uses the post-`A1passive` passive-tail derivative
directly from the staged `A1passive` field.  The determinant is one by
regrouping the raw tuple as `Ctop × rest` and applying the upper-shear
determinant calculation.

Composed after the previous edge-pair and `A1passive` stages, the map has
absolute determinant one and proves `Ctop` component agreement with the formal
raw-order Jacobian on actual raw-order derivative targets.

Focused `DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` build passed.
The full `DLNFibre` build passed with pre-existing warning noise.
`scripts/sorries`, `git diff --check`, code-only forbidden-marker search, and
direct axiom audit passed; the new public theorems have axiom footprint
`[propext, Classical.choice, Quot.sound]`.

This is not full target normalisation: `F3` remains open.  It also does not
prove full raw-tuple equality, actual Frechet determinant equality, measure
transport, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 edge-pair then `A1passive` component bridge

Reproduction:
`reproduction-a2-retained-passive-edge-pair-then-a1passive-bridge.md`.
Statement card:
`statement-card-a2-retained-passive-edge-pair-then-a1passive-bridge.md`.
Review:
`review-a2-retained-passive-edge-pair-then-a1passive-bridge.md`,
PASS by xhigh `Pasteur the 2nd`.

Lean now proves in `RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassiveTargetEdgePairThenA1passiveShearRawTupleLinearEquivAt
retainedPassiveTargetEdgePairThenA1passiveShearRawTupleLinearEquivAt_apply
retainedPassiveTargetEdgePairThenA1passiveShearRawTupleLinearEquivAt_abs_det_eq_one
retainedPassiveTargetEdgePairThenA1passiveShear_fderiv_A1passive_eq_formalRawOrderJacobianAt
retainedPassiveTargetEdgePairThenA1passiveShear_fderiv_F2C_eq_formalRawOrderJacobianAt
retainedPassiveTargetEdgePairThenA1passiveShear_fderiv_A3passive_eq_formalRawOrderJacobianAt
```

The composition applies the target edge-pair shear first and the
post-edge-pair `A1passive` shear second.  Its absolute determinant is one.  On
actual raw-order derivative targets it gives componentwise agreement with the
formal raw-order Jacobian for `A1passive`, `(F2,C)`, and `A3passive`.

Focused `DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` build passed.
`scripts/sorries`, `git diff --check`, code-only forbidden-marker search, and
direct axiom audit passed; the new composed theorems have axiom footprint
`[propext, Classical.choice, Quot.sound]`.

This is not full target normalisation, full raw-tuple equality, actual Frechet
determinant equality, measure transport, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 post-edge-pair `A1passive` raw-tuple shear

Reproduction:
`reproduction-a2-retained-passive-post-edge-pair-a1passive-raw-tuple-shear.md`.
Statement card:
`statement-card-a2-retained-passive-post-edge-pair-a1passive-raw-tuple-shear.md`.
Review:
`review-a2-retained-passive-post-edge-pair-a1passive-raw-tuple-shear.md`,
PASS by xhigh `James the 2nd`.

Lean now proves in `RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt
retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt_apply
retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt_symm_apply
retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt_det_eq_one
retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt_abs_det_eq_one
```

and in `MatrixLinearDeterminant.lean`:

```text
linearEquivUpperShear_symm_apply
```

The map is explicitly post-edge-pair: it computes the source `F2` successor
family from the formal inverse of the already-normalised `(F2,C)` pair, not
from the pre-edge-pair target recovery recurrence.  It fixes
`(F2,A3passive,C,Ctop,F3)` and changes only `A1passive`, so the determinant is
the determinant of an upper product shear on `A1passive × rest`, hence one.

Focused builds of
`DLNFibre.DLN.Aoyagi.MatrixLinearDeterminant` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed.
The full `DLNFibre` build passed with pre-existing warning noise.
`scripts/sorries`, `git diff --check`, and code-only forbidden-marker search
passed.
Direct axiom audit reported `[propext, Classical.choice, Quot.sound]` for
the new public post-edge-pair shear theorems, and `[propext, Quot.sound]` for
`linearEquivUpperShear_symm_apply`.

This does not yet compose the edge-pair and `A1passive` shears, prove the
partial actual-derivative bridge, prove actual Frechet determinant equality,
or prove measure transport, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 target edge-pair raw-tuple determinant

Reproduction:
`reproduction-a2-retained-passive-target-edge-pair-raw-tuple-determinant.md`.
Statement card:
`statement-card-a2-retained-passive-target-edge-pair-raw-tuple-determinant.md`.
Review:
`review-a2-retained-passive-target-edge-pair-raw-tuple-determinant.md`,
PASS by xhigh `Lorentz the 2nd`.

Lean now proves in `RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_det_eq_one
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_symm_det_eq_one
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_det_eq_one
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_abs_det_eq_one
```

and in `MatrixLinearDeterminant.lean`:

```text
linearMap_det_finSuccUpperTriangular_eq_prod
linearMap_det_finSuccUpperUnitriangular_eq_one
finSuccUpperUnitriangularLinearMap_det_eq_one
```

The proof conjugates the inverse full raw-tuple shear by the edge-block
regrouping `(A1_q,A3_q,F_q,C_q)`, proves the transported map is
successor-upper-triangular, reduces the determinant to same-edge diagonal
block shears, and transports the determinant back.  The forward determinant
and absolute determinant wrappers are consequences of the inverse determinant.

Focused builds of
`DLNFibre.DLN.Aoyagi.MatrixLinearDeterminant` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed;
`scripts/sorries`, `git diff --check`, and code-only forbidden-marker search
passed.  Lorentz also checked the seven determinant theorem axiom footprints:
`[propext, Classical.choice, Quot.sound]`.

This does not prove determinant one for the formal separated `(F2,C)`
equivalence, determinant equality for the actual raw-order Frechet derivative,
measure transport, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 target edge-pair raw-tuple linear equivalence

Reproduction:
`reproduction-a2-retained-passive-target-edge-pair-raw-tuple-equivalence.md`.
Statement card:
`statement-card-a2-retained-passive-target-edge-pair-raw-tuple-equivalence.md`.
Review:
`review-a2-retained-passive-target-edge-pair-raw-tuple-linear-inverse.md`,
PASS by xhigh `Mendel the 2nd`.
Final equivalence review:
`review-a2-retained-passive-target-edge-pair-raw-tuple-linear-equivalence.md`,
PASS by xhigh `Gauss the 2nd`.

Lean now proves in `RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassiveTargetEdgePairShearRawTupleLinearMapAt
retainedPassiveTargetEdgePairShearRawTupleLinearMapAt_apply
retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_apply
retainedPassiveFormalRawF2CLinearEquivAt_symm_targetEdgePairShearAt_fst
retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_leftInverse
retainedPassiveTargetRecoveredF2At_rawTupleInverse
retainedPassiveTargetEdgePairShearRawTupleLinearMapAt_rightInverse
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_apply
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_symm_apply
```

The forward map is the full raw-tuple lift of the target edge-pair shear:
`A1passive`, `A3passive`, `Ctop`, and `F3` are fixed, while `(F2,C)` is
replaced by `retainedPassiveTargetEdgePairShearAt z w`.  The inverse map fixes
the same side fields, uses only the first formal-inverse component as the
recovered `X`, and explicitly cancels the raw side-field terms in `F2` and
`C`.  The two maps are now proved inverse to each other and packaged with
`LinearEquiv.ofLinear`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed;
`scripts/sorries`, `git diff --check`, code-only forbidden-marker search, and
direct axiom audits for the new proof surface also passed.  This does not yet
prove determinant one, determinant equality, measure transport, normal
crossings, pole order, or RLCT.  The next frontier is determinant control only
after an actual unitriangular factorization or direct determinant proof.

## 2026-06-28 A2 target edge-pair linear map

Reproduction:
`reproduction-a2-retained-passive-target-edge-pair-linear-map.md`.
Statement card:
`statement-card-a2-retained-passive-target-edge-pair-linear-map.md`.
Review:
`review-a2-retained-passive-target-edge-pair-linear-map.md`, PASS by xhigh
`Lovelace the 2nd`.

Lean now proves in `RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassiveTargetRecoveredF2LinearMapAt
retainedPassiveTargetRecoveredF2LinearMapAt_apply
retainedPassiveTargetRecoveredSuccessorF2LinearMapAt
retainedPassiveTargetRecoveredSuccessorF2LinearMapAt_apply
retainedPassiveTargetEdgePairShearLinearMapAt
retainedPassiveTargetEdgePairShearLinearMapAt_apply
```

For fixed retained-passive `z`, the backward target-recovered `F2` recurrence
is now a `LinearMap` in the target raw tuple `w`; the target-recovered
successor family is also a `LinearMap`; and the all-edge target-side normalized
`(F2,C)` pair agrees with `retainedPassiveTargetEdgePairShearAt z w`.

The terminal zero branch, nonterminal `Fin.succ_castSucc` cast, and
noncommutative `Xsucc * coord.C q` term are preserved.  Implementation helpers
for matrix multiplication, raw projections, and recurrence branches are
private; this checkpoint exposes only the six component linear-map names above.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed; full
`DLNFibre` build passed with pre-existing warning noise; `scripts/sorries`,
`git diff --check`, forbidden-marker search, and direct axiom audits passed.

This does not construct a target-side `LinearEquiv`, whole raw-tuple
normalizer, determinant-one theorem, determinant equality, source-prior
transport, normal crossings, pole order, or RLCT.

Next frontier: reproduce and package an explicit inverse/equivalence for this
narrow edge-pair component, or lift it to a whole raw-tuple component shear
without claiming determinant control prematurely.

## 2026-06-28 A2 generic shear/product abs-det wrappers

Reproduction:
`reproduction-a2-generic-shear-product-abs-det-wrappers.md`.
Statement card:
`statement-card-a2-generic-shear-product-abs-det-wrappers.md`.
Review:
`review-a2-generic-shear-product-abs-det-wrappers.md`, PASS by xhigh
`Avicenna the 2nd`.

Lean now proves in `MatrixLinearDeterminant.lean`:

```text
linearEquiv_prodCongr_abs_det_eq_one
linearEquiv_skewProd_refl_refl_det_eq_one
linearEquiv_skewProd_refl_refl_abs_det_eq_one
linearEquivUpperShear_abs_det_eq_one
```

The product wrapper requires absolute-determinant-one hypotheses on both
factors.  The skew and upper wrappers are determinant-one/abs-det-one
specializations of existing shear determinant lemmas.  The absolute-value
statements use `[CommRing R] [LinearOrder R] [IsOrderedRing R]`.

Focused build of `DLNFibre.DLN.Aoyagi.MatrixLinearDeterminant` passed;
`scripts/sorries`, `git diff --check`, forbidden-marker search, and direct
axiom audits passed.

This does not construct the retained-passive target normalizer, prove
determinant equality, source-prior transport, normal crossings, pole order, or
RLCT.

Next frontier: package actual retained-passive target-side component shears as
linear equivalences, then compose them with the generic abs-det wrappers.

## 2026-06-28 A2 positive-tail `F3` target-only `dEarly`

Reproduction:
`reproduction-a2-retained-passive-f3-positive-tail-target-only-dearly.md`.
Statement card:
`statement-card-a2-retained-passive-f3-positive-tail-target-only-dearly.md`.
Review:
`review-a2-retained-passive-f3-positive-tail-target-only-dearly.md`, PASS by
xhigh `Poincare the 2nd`.

Lean now proves in `RetainedPassiveCoordinatesJacobian.lean`:

```text
F3_tail_pos_targetOnly_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_targetOnly_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

The positive-tail tuple parameter is `M := M+1`, and the early lower-left slot
is the target-only recursive lower-left derivative with parameter `(M := M)` at
index `0`.  The proof rewrites that value to the already-proved source-staged
recursive expression and reuses the existing recursive `F3` bridge.  The
terminal `dLast#` factor is unchanged, and the matrix order remains
`- dEarly * coord.solvedA1 (Fin.last (M+1))`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed; full
`DLNFibre` build passed with only pre-existing warning noise; `scripts/sorries`,
`git diff --check`, forbidden-marker search, and direct axiom audits passed.

This does not construct the determinant-one target normalizer, prove
determinant equality, source-prior transport, normal crossings, pole order, or
RLCT.

Next frontier: assemble the target-side normalizer/shear package and determinant
control from the staged target-side derivative pieces.

## 2026-06-27 A2 recursive target-only lower-left tail

Reproduction:
`reproduction-a2-retained-passive-recursive-target-only-lower-left-tail.md`.
Statement card:
`statement-card-a2-retained-passive-recursive-target-only-lower-left-tail.md`.
Review:
`review-a2-retained-passive-recursive-target-only-lower-left-tail.md`, PASS by
xhigh `Meitner the 2nd`.

Lean now proves in `RetainedPassiveCoordinates.lean`:

```text
retainedPassiveSolvedA1_residualFactorProduct_eq_A1seed_of_pos
```

and in `RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassiveSolvedA1TargetStagedTangentAt
retainedPassiveSolvedA1TargetStagedTangentAt_zero
retainedPassiveSolvedA1TargetStagedTangentAt_succ
retainedPassiveSolvedA1TargetStagedTangentAt_fderiv_eq_source
retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
retainedPassiveSolvedA1SuffixTargetStagedFDerivAt_self
retainedPassiveSolvedA1SuffixTargetStagedFDerivAt_step
retainedPassiveSolvedA1SuffixProductAt
fderiv_retainedPassive_solvedA1_residualFactorProduct_targetStaged_apply
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_self
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_step
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_zero
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_succ
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_fderiv_eq_sourceStaged
fderiv_retainedPassiveLowerLeftProductTailSum_targetOnly_apply
```

The solved-`A1` suffix derivative is target-staged across the whole solved
family, including the terminal factor.  The lower-left recursion has terminal
value `0` at `M+1`; each step uses the target-only current solved-`A1` tangent,
the staged `Cnext` suffix beginning at `r.succ`, the solved-`A1` suffix tangent
beginning at `p.succ.val`, and the successor lower-left derivative.

On actual raw-order derivative targets, Lean proves the target-only recursion
equals the existing source-staged recursion, and then proves the Frechet
derivative of the zeroed-final lower-left product tail is this target-only
recursive expression.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed; full
`DLNFibre` build passed with only pre-existing warning noise; `scripts/sorries`,
`git diff --check`, forbidden-marker search, and direct axiom audits passed.

This does not construct the determinant-one target normalizer, prove
determinant equality, source-prior transport, normal crossings, pole order, or
RLCT.

Next frontier: assemble the target-side normalizer/shear package and determinant
control from the staged target-side derivative pieces.

## 2026-06-27 A2 target-staged `C` suffix derivative

Reproduction:
`reproduction-a2-retained-passive-target-staged-c-suffix.md`.
Statement card:
`statement-card-a2-retained-passive-target-staged-c-suffix.md`.
Review:
`review-a2-retained-passive-target-staged-c-suffix.md`, PASS by xhigh
`Maxwell the 2nd`.

Lean now proves in `RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassiveCTailTargetOnlyStepAt
retainedPassiveCTailTargetOnlyStepAt_fderiv_eq_sourceStep
retainedPassiveCSuffixTargetStagedFDerivAt
retainedPassiveCSuffixTargetStagedFDerivAt_self
retainedPassiveCSuffixTargetStagedFDerivAt_step
retainedPassiveCSuffixProductAt
fderiv_retainedPassive_C_residualFactorProduct_targetStaged_apply
retainedPassiveCnextTargetStagedFDerivAt
retainedPassiveCnextTargetStagedFDerivAt_fderiv_eq_source
retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt
retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt_fderiv_eq_sourceStepCore
```

The one-step helper packages the stored-`C` suffix product rule.  The recursive
target-staged suffix derivative has terminal value zero and unfolds through
that one-step helper.  On actual raw-order derivative targets, Lean proves it
equals the Frechet derivative of the stored `C` suffix product.

The `Cnext` specialization stages the remaining `dCnext` slot in the
positive-tail lower-left step, where `Cnext` begins at `r.succ`.  The new
step-core wrapper feeds this staged `dCnext` into the already-landed
target-only lower-left step core while keeping `dAcur`, `dPsucc`, and `dNext`
explicit.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed; full
`DLNFibre` build passed with only pre-existing warning noise; `scripts/sorries`,
`git diff --check`, forbidden-marker search, and direct axiom audits passed.
This does not construct the full target-only lower-left recurrence,
determinant-one normalizer, determinant equality, source-prior transport,
normal crossings, pole order, or RLCT.

Next frontier: build the recursive target-only lower-left derivative by using
the target-staged `Cnext`, current solved-`A1`, `dPsucc`, and successor
lower-left derivative replacements.

## 2026-06-27 A2 target-only lower-left step core

Reproduction:
`reproduction-a2-retained-passive-target-only-lower-left-step-core.md`.
Statement card:
`statement-card-a2-retained-passive-target-only-lower-left-step-core.md`.
Review:
`review-a2-retained-passive-target-only-lower-left-step-core.md`, PASS by
xhigh `Halley the 2nd`.

Lean now proves in `RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassiveTargetRecoveredSourceCtopAt
retainedPassiveTargetRecoveredSourceCtopAt_fderiv_eq_sourceCtop
retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt
retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt_zero
retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt_succ
retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt_fderiv_eq_source
retainedPassiveLowerLeftTailTargetOnlyStepCoreAt
retainedPassiveLowerLeftTailTargetOnlyStepCoreAt_fderiv_eq_sourceStepCore
```

The `Ctop` helper recovers the source `Ctop` tangent from an arbitrary target
tuple by the recursive target-staged first top-left branch.  The current
solved-`A1` helper is target-only: zero branch uses recovered `Ctop` and the
target-staged passive `A1` tail derivative; successor branch uses
`retainedPassiveTargetStagedA1passiveTangentAt z w s.castSucc`.

The target-only lower-left step core preserves the existing source one-step
matrix order and replaces only `v.C(r)` and `v.A3free(q)` by target-side
readouts.  It keeps `dCnext`, `dAcur`, `dPsucc`, and `dNext` explicit.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed, and the full
`DLNFibre` build passed with only pre-existing warning noise.  `scripts/sorries`,
`git diff --check`, forbidden-marker search, and direct axiom audits passed.

This does not construct the full target-only lower-left recurrence, does not
target-stage `dCnext`, and does not prove determinant equality, source-prior
transport, normal crossings, pole order, or RLCT.

Next frontier: target-stage the remaining `dCnext` suffix-product derivative
or build the recursive target-only lower-left derivative once that `C`-suffix
replacement is available.

## 2026-06-27 A2 target-recovered source pair and determinant helper

Reproduction:
`reproduction-a2-retained-passive-target-recovered-source-pair-det-helper.md`.
Statement card:
`statement-card-a2-retained-passive-target-recovered-source-pair-det-helper.md`.
Review:
`review-a2-retained-passive-target-recovered-source-pair-det-helper.md`, PASS
by xhigh `Epicurus the 2nd`.

Lean now proves in `MatrixLinearDeterminant.lean`:

```text
linearEquiv_prodCongr_det_eq_mul
```

and in `RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassiveTargetRecoveredSourcePairAt
retainedPassiveTargetRecoveredSourcePairAt_fderiv_eq_sourcePair
retainedPassiveTargetRecoveredSourceCAt
retainedPassiveTargetRecoveredSourceCAt_fderiv_eq_sourceC
```

The source pair definition first forms the target-side normalized `(F2,C)`
pair and then applies the point-specialized inverse formal edge-pair
equivalence.  On an actual raw-order derivative target it recovers
`(v.F2,v.C)`, and its `C` projection recovers `v.C(q)`.  This supplies one of
the source-direction replacements needed by the future target-only lower-left
recurrence.

The determinant helper packages the determinant of `eM.prodCongr eN` as the
product of the two factor determinants, using the existing product-map
determinant lemma.

Focused builds of `DLNFibre.DLN.Aoyagi.MatrixLinearDeterminant` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed, and the full
`DLNFibre` build passed with only pre-existing warning noise.  `scripts/sorries`,
`git diff --check`, and forbidden-marker search on the touched Lean files
passed.

This does not construct the target normalizer, prove determinant equality, or
target-stage the positive-tail lower-left recurrence.

## 2026-06-27 A2 recursive passive A1-tail Ctop plug-in

Reproduction:
`reproduction-a2-retained-passive-recursive-target-staged-a1-tail.md`.
Statement card:
`statement-card-a2-retained-passive-recursive-a1-tail-ctop-plugin.md`.
Review:
`review-a2-retained-passive-recursive-a1-tail-ctop-plugin.md`, PASS by xhigh
`Dirac the 2nd`.

Lean now proves in `RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassiveTargetStagedA1passiveTangentAt
retainedPassiveTargetStagedA1passiveTangentAt_fderiv_eq_source
retainedPassiveA1TailTargetStagedFDerivAt
retainedPassiveA1TailTargetStagedFDerivAt_self
retainedPassiveA1TailTargetStagedFDerivAt_step
retainedPassiveA1TailTargetStagedFDerivAt_zero
retainedPassiveA1seedTailProductAt
fderiv_retainedPassive_A1seed_residualFactorProduct_targetStaged_apply
fderiv_retainedPassive_A1TailAfterFirst_targetStaged_apply
Ctop_tail_recursive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_recursive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
```

The recursive target-only passive top-left derivative has base `D_M#=0` and
step

```text
D_m# =
  D_{m+1}# * data.A1seed(p)
  + P_{m+1}(z) * targetA1(q),
```

where `q : Fin M := <m,m<M>` and `p : Fin (M+1) := q.succ`.  On an actual
raw-order derivative target, Lean proves that this recursion equals the
Frechet derivative of the seed-product suffix `P_m`.  The full
`retainedPassiveA1TailAfterFirst` derivative is the `m=0` case.

The `Ctop` bridge then uses this recursive `dTail`:

```text
Dzv.Ctop
  - XsuccF2(0) * coord.solvedA3(0)
  - coord.F2((0 : Fin (M+1)).succ) * rawEdgeTupleA3(Dzv,0)
  + Tail^-1 * dTail * Tail^-1 * coord.Ctop
= formal.Ctop.
```

The recovery theorem multiplies the same staged branch by `Tail` and recovers
the source `Ctop` tangent.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed, and the full
`DLNFibre` build passed with only pre-existing warning noise.  `scripts/sorries`
reported zero forbidden markers, `git diff --check` passed, forbidden-marker
search on the touched file was clean, and direct `#print axioms` audits for the
two derivative bridges and two `Ctop` theorems reported only
`[propext, Classical.choice, Quot.sound]`.

This does not construct the determinant-one target normalizer, prove
determinant equality, source-prior transport, inverse-density pushforward,
normal crossings, pole order, or RLCT.

Next frontier: construct the determinant-one target normalizer from the
recursive `F3` plug-in, this recursive `Ctop` plug-in, and the passive
`A1` target-staging.

## 2026-06-27 A2 positive-tail F3 recursive dEarly plug-in

Reproduction/design:
`reproduction-a2-retained-passive-recursive-target-staged-lower-left-tail.md`.
Statement card:
`statement-card-a2-retained-passive-f3-recursive-dearly-plugin.md`.
Review:
`review-a2-retained-passive-f3-recursive-dearly-plugin.md`, PASS by xhigh
`Franklin the 2nd`.

Lean now proves in `RetainedPassiveCoordinatesJacobian.lean`:

```text
F3_tail_pos_recursive_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_recursive_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

For a positive retained-passive tail written as `M+1`, the `F3` bridge now
uses the recursive target-staged lower-left derivative at index `0`:

```text
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt
  (M := M) (ρ := ρ) (κ' := κ') z v 0 (Nat.zero_le (M+1)).
```

The proof starts from the existing terminal-target-staged positive-tail `F3`
bridge at `qLast : Fin (M+1) := Fin.last M`, with
`qLast.succ = Fin.last (M+1)` by `rfl`, and rewrites only
`(fderiv Earlyfun z) v` by
`fderiv_retainedPassiveLowerLeftProductTailSum_targetStaged_apply`.  The
recovery companion uses the same staged expression and right-multiplies by
`(-(coord.solvedA1 (Fin.last (M+1))))^-1`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed, and the full
`DLNFibre` build passed with only pre-existing warning noise.  `scripts/sorries`
reported zero forbidden markers, `git diff --check` passed, forbidden-marker
search on the touched file was clean, and direct `#print axioms` audits for the
two new theorems reported only `[propext, Classical.choice, Quot.sound]`.

This does not construct the determinant-one target normalizer, prove
determinant equality, source-prior transport, inverse-density pushforward,
normal crossings, pole order, or RLCT.  The older finite-unroll `F3` theorems
remain compatibility lemmas for now.

Next frontier: construct the determinant-one target normalizer using this
recursive `F3` plug-in rather than extending the finite-unroll chain.

## 2026-06-27 A2 lower-left target-staged actual derivative bridge

Reproduction/design:
`reproduction-a2-retained-passive-recursive-target-staged-lower-left-tail.md`.
Statement card:
`statement-card-a2-retained-passive-lower-left-target-staged-actual-derivative-bridge.md`.
Review:
`review-a2-retained-passive-lower-left-target-staged-actual-derivative-bridge.md`,
PASS by xhigh `Erdos the 2nd`.

Lean now proves in `RetainedPassiveCoordinatesDerivative.lean`:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_targetStaged_apply
```

On the determinant chart, the actual Frechet derivative of the zeroed-final
retained-passive lower-left product tail agrees with the recursive
target-staged expression
`retainedPassiveLowerLeftProductTailTargetStagedFDerivAt`.  The theorem is
stated for the staged tail index `m <= M+1`; the explicit product-tail call on
the actual side uses the widened proof `m <= M+2` because that tail has one
extra zeroed-final slot.

The proof is decreasing induction on `m`.  The base is the zeroed-final tail at
`m = M+1`.  The zero-current step uses the solved top-left tangent
`Tail^-1 * v.Ctop - Tail^-1 * dTail * Tail^-1 * coord.Ctop`; successor steps
use `v.1 s.castSucc`.  In both step cases the induction hypothesis replaces
only the recursive `dNext` slot of `retainedPassiveLowerLeftTailStepCoreAt`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` passed, and the full
`DLNFibre` build passed with only pre-existing warning noise.  `scripts/sorries`
reported zero forbidden markers, `git diff --check` passed, forbidden-marker
search on the touched file was clean, and the new theorem axiom audit reported
only `[propext, Classical.choice, Quot.sound]`.

At that checkpoint this did not plug the recursive derivative into `F3`,
construct the determinant-one target normalizer, prove determinant equality, or
prove source-prior transport, inverse-density pushforward, normal crossings,
pole order, or RLCT.

That frontier is now closed by the newer positive-tail recursive `F3` plug-in
checkpoint above.

## 2026-06-27 A2 recursive target-staged lower-left tail API

Reproduction/design:
`reproduction-a2-retained-passive-recursive-target-staged-lower-left-tail.md`.
Statement card:
`statement-card-a2-retained-passive-recursive-target-staged-lower-left-tail.md`.
Review:
`review-a2-retained-passive-recursive-target-staged-lower-left-tail.md`,
PASS by xhigh `Turing the 2nd`.

Lean now proves in `RetainedPassiveCoordinatesDerivative.lean`:

```text
retainedPassiveLowerLeftTailCurrentTargetSolvedA1TangentAt
retainedPassiveLowerLeftTailCurrentTargetSolvedA1TangentAt_zero
retainedPassiveLowerLeftTailCurrentTargetSolvedA1TangentAt_succ
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_self
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_step
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_zero
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_succ
```

The recursive expression has base value zero at `m=M+1`, the zeroed-final tail.
The generic step unfolds by `retainedPassiveLowerLeftTailStepCoreAt` and passes
the recursive successor value as `dNext`.  The current solved-`A1` target
tangent unfolds to the zero branch at index `0` and to `v.1 s.castSucc` at
successor index `s.val+1`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` passed, and the full
`DLNFibre` build passed with only pre-existing warning noise.  `scripts/sorries`
reported zero forbidden markers, `git diff --check` passed, and all eight new
axiom audits reported only `[propext, Classical.choice, Quot.sound]`.

This API by itself is only the recursive expression/unfold layer; the actual
Frechet-derivative bridge and the positive-tail `F3` plug-in are now recorded
in newer checkpoints above.  It still does not construct the determinant-one
target normalizer, and does not prove determinant equality, measure transport,
normal crossings, pole order, or RLCT.

Next frontier from this older checkpoint was the actual-derivative bridge; it
is now proved, and the later recursive `F3` plug-in is also now proved.

## 2026-06-27 A2 lower-left step core

Reproduction/design:
`reproduction-a2-retained-passive-recursive-target-staged-lower-left-tail.md`.
Statement card:
`statement-card-a2-retained-passive-lower-left-step-core.md`.
Review:
`review-a2-retained-passive-lower-left-step-core.md`, PASS by xhigh
`Averroes the 2nd`.

Lean now proves in `RetainedPassiveCoordinatesDerivative.lean`:

```text
retainedPassiveLowerLeftTailStepCoreAt
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_dPcast_stepCore_apply
fderiv_retainedPassiveLowerLeftProductTailSum_zero_product_dCprod_dG_dPcast_stepCore_apply
fderiv_retainedPassiveLowerLeftProductTailSum_succ_product_dCprod_dG_dPcast_stepCore_apply
```

The helper packages the one-step retained-passive lower-left tail derivative
RHS after the existing `dCprod`, `dG`, and `dPcast` staging.  It keeps
`dAcur`, `dPsucc`, and `dNext` explicit.  The generic, zero-current, and
successor-current wrappers are definitional restatements of already-proved
recurrence theorems through this helper.

The zero-current wrapper supplies

```text
Tail^-1 * v.Ctop - Tail^-1 * dTail * Tail^-1 * coord.Ctop
```

as `dAcur`.  The successor-current wrapper supplies `v.1 s.castSucc`, not
`v.1 s.succ` or `v.1 q`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` passed, and the full
`DLNFibre` build passed with only pre-existing warning noise.  `scripts/sorries`
reported zero forbidden markers, `git diff --check` passed, and all four
new axiom audits reported only `[propext, Classical.choice, Quot.sound]`.

This does not define the full Nat-recursive target-staged lower-left
derivative, construct the determinant-one target linear equivalence, prove
determinant equality, or prove source-prior transport, inverse-density
pushforward, normal crossings, pole order, or RLCT.

Next frontier: define the recursive staged derivative object with base at the
zeroed-final tail, then use it as the `dEarly` term in the positive-tail `F3`
bridge.

## 2026-06-27 A2 conditional determinant/Jacobian bridge

Reproduction:
`reproduction-a2-retained-passive-conditional-determinant-jacobian-bridge.md`.
Statement card:
`statement-card-a2-retained-passive-conditional-determinant-jacobian-bridge.md`.
Review:
`review-a2-retained-passive-conditional-determinant-jacobian-bridge.md`,
PASS by xhigh `Noether the 2nd`.

Lean now proves in `RetainedPassiveCoordinatesJacobian.lean`:

```text
topologyTupleEdgeRawOrderFDerivAbsDet_eq_formalRawOrderAbsDetAt_of_target_linearEquiv
topologyTupleEdgeRawOrderFDerivAbsDet_product_eq_of_target_linearEquiv
```

The first theorem assumes a supplied retained-passive raw tuple linear
equivalence `T`, the pointwise comparison

```text
T ((fderiv topologyTupleEdgeRawOrder z) v)
  = retainedPassiveFormalRawOrderJacobianAt z v,
```

and `|det T| = 1`; it proves equality of the actual raw-order forward absolute
Jacobian determinant and the formal raw-order absolute determinant.  The
product theorem only rewrites the formal side using
`retainedPassiveFormalRawOrderJacobianAbsDetAt_eq`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed with no
focused-module warnings, and the full `DLNFibre` build passed with only
pre-existing warning noise.  `scripts/sorries` reported zero forbidden markers,
`git diff --check` passed, and `#print axioms` for both new theorem names
reported only `[propext, Classical.choice, Quot.sound]`.

This does not construct the target-side determinant-one equivalence, does not
claim the existing componentwise sheared derivative packaging is already such
an equivalence, and does not prove source-prior transport, inverse-density
pushforward, normal crossings, pole order, or RLCT.

Next frontier: construct the target-side determinant-one normalization.  For
the positive-tail `F3` branch, the better route is a recursive target-staged
lower-left-tail derivative object, not another unconstrained finite unroll.

## 2026-06-27 A2 F3 three-positive-tail next-next successor substitution

Reproduction:
`reproduction-a2-retained-passive-f3-three-positive-tail-nextnext-succ-substitution.md`.
Statement card:
`statement-card-a2-retained-passive-f3-three-positive-tail-nextnext-succ-substitution.md`.
Review:
`review-a2-retained-passive-f3-three-positive-tail-nextnext-succ-substitution.md`,
PASS by xhigh `Parfit the 2nd` and xhigh `Carson the 2nd`.

Lean now proves in `RetainedPassiveCoordinatesJacobian.lean`:

```text
F3_tail_pos_pos_pos_dEarly_zero_next_succ_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_pos_pos_dEarly_zero_next_succ_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

This is the second recursive consumer of the remaining `NextNextfun` term in
the positive-tail `F3` bridge.  It writes the tail length as
`((M+1)+1)+1`, starts from the landed two-positive-tail theorem with
`M := M+1`, and rewrites only the residual `(fderiv NextNextfun z) v` by
instantiating the successor-index `dEarly` theorem at
`s1 := (0 : Fin (M+1)).succ`.

The third-step indices are

```text
t0 = 0 : Fin (M+1),
s1 = t0.succ,
q2 = s1.succ,
u2 = s1.castSucc,
p2 = q2.castSucc,
r2 = q2.succ.
```

The successor tangent is `v.1 u2`, not `v.1 q2`.  The theorem leaves
`dPsucc`, `dPsucc1`, `dPsucc2`, `Psucc*`, and the next recursive derivative
explicit.  It does not recurse into `dNext2`, terminal-clean, or claim full
positive-tail `F3` target staging.

The recovery companion uses the same staged expression and the formal raw-order
recovery theorem to prove that right-multiplication by
`(-(coord.solvedA1 (Fin.last (((M+1)+1)+1))))^-1` recovers the source `F3`
tangent.  It performs no additional recurrence expansion.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed, and the full
`DLNFibre` build passed with only pre-existing style warnings.  `scripts/sorries`
reported zero forbidden markers, `git diff --check` was clean, and both
theorem axiom audits reported only
`[propext, Classical.choice, Quot.sound]`.

## 2026-06-27 A2 Ctop two-positive-tail second A1 target staging

Reproduction:
`reproduction-a2-retained-passive-ctop-two-positive-tail-second-a1-target-staging.md`.
Statement card:
`statement-card-a2-retained-passive-ctop-two-positive-tail-second-a1-target-staging.md`.
Review:
`review-a2-retained-passive-ctop-two-positive-tail-second-a1-target-staging.md`,
PASS by xhigh `Schrodinger the 2nd`.

Lean now proves in `RetainedPassiveCoordinatesJacobian.lean`:

```text
Ctop_tail_pos_pos_firstA1_nextA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_pos_pos_firstA1_nextA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
```

The theorem writes the passive tail length as `(M+1)+1`, starts from the
first-passive `Ctop` theorem, and rewrites only the remaining suffix derivative
`(fderiv Psucc z) v` by the generic passive `A1seed` suffix helper at the
second passive source coordinate.  The indices are:

```text
q0 = 0 : Fin ((M+1)+1)
p0 = q0.succ
s0 = 0 : Fin (M+1)
q1 = s0.succ : Fin ((M+1)+1)
p1 = q1.succ
```

`Psucc` starts at `p0.succ` and `Psucc1` starts at `p1.succ`.  The second
passive target replacement uses `Dzv.1 q1`; it does not use the `F3` successor
`castSucc` tangent pattern.  The theorem leaves `(fderiv Psucc1 z) v` explicit
and preserves the noncommutative order

```text
Tail⁻¹ * (((...) * data.A1seed p0) + ...) * Tail⁻¹ * coord.Ctop.
```

The recovery companion applies the same equality and the formal raw-order
`Ctop` recovery after left multiplication by `Tail`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed, and the full
`DLNFibre` build passed with only pre-existing style warnings.  `scripts/sorries`
reported zero forbidden markers, `git diff --check` was clean, and both new
theorem axiom audits reported only `[propext, Classical.choice, Quot.sound]`.
This does not simplify the `M=0` terminal second-stage suffix, terminal-clean,
claim full recursive `Ctop`/`F3` target staging, determinant equality, measure
transport, normal crossings, pole order, or RLCT.

## 2026-06-27 A2 Ctop first passive A1 target staging

Reproduction:
`reproduction-a2-retained-passive-a1-tail-target-staged-first-passive.md`.
Statement card:
`statement-card-a2-retained-passive-a1-tail-target-staged-first-passive.md`.
Review:
`review-a2-retained-passive-a1-tail-target-staged-first-passive.md`, PASS by
xhigh `Banach the 2nd`.

Lean now proves in `RetainedPassiveCoordinatesJacobian.lean`:

```text
fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_target_staged_apply
fderiv_retainedPassive_A1TailAfterFirst_pos_target_staged_apply
Ctop_tail_pos_firstA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_pos_firstA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
```

The generic helper starts from the passive seed-product suffix product rule and
replaces only the current passive tangent `v.1 q` using the target-staged
passive `A1` recovery.  The positive-tail wrapper specializes this to
`q : Fin M := ⟨0,hM⟩` and `p := q.succ`.  The Ctop consumer starts from the
existing positive-tail target-staged Ctop equality and rewrites only

```text
Psucc z * v.1 q
```

inside the explicit first suffix-derivative recurrence.  It keeps
`(fderiv Psucc z) v` explicit and preserves the noncommutative order

```text
Tail⁻¹ * (...) * Tail⁻¹ * coord.Ctop.
```

The passive replacement uses `q.succ`, not the separate Ctop endpoint edge
index `0 : Fin (M+1)`.  The recovery companion applies the same equality and
the formal raw-order `Ctop` recovery after left multiplication by `Tail`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed, and the full
`DLNFibre` build passed with only pre-existing style warnings.  `scripts/sorries`
reported zero forbidden markers, `git diff --check` was clean, and all four
new theorem axiom audits reported only `[propext, Classical.choice,
Quot.sound]`.  This does not simplify the `M=1` empty suffix, terminal-clean,
expand the remaining suffix derivative, claim full `Ctop`/`F3` target staging,
determinant equality, measure transport, normal crossings, pole order, or RLCT.

## 2026-06-27 A2 F3 two-positive-tail next-successor substitution

Reproduction:
`reproduction-a2-retained-passive-f3-two-positive-tail-next-succ-substitution.md`.
Statement card:
`statement-card-a2-retained-passive-f3-two-positive-tail-next-succ-substitution.md`.
Review:
`review-a2-retained-passive-f3-two-positive-tail-next-succ-substitution.md`,
PASS by xhigh `Dirac`.

Lean now proves in `RetainedPassiveCoordinatesJacobian.lean`:

```text
F3_tail_pos_pos_dEarly_zero_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_pos_dEarly_zero_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

This is the first recursive consumer of the remaining `Nextfun` term in the
positive-tail `F3` bridge.  It writes the tail length as `(M+1)+1`, starts from
the landed first-index `dEarly` substitution theorem with `M := M+1`, and
rewrites only the residual `(fderiv Nextfun z) v` by instantiating the
successor-index `dEarly` theorem with `s0 := 0 : Fin (M+1)`.

The second-step indices are

```text
s0 = 0 : Fin (M+1),
q1 = s0.succ,
u1 = s0.castSucc,
p1 = q1.castSucc,
r1 = q1.succ.
```

The successor tangent is `v.1 u1`, not `v.1 q1`.  The theorem leaves
`dPsucc1`, `Psucc1`, and the next recursive derivative explicit.  It does not
rewrite the first-level `dPsucc`, does not terminal-clean, and does not claim
full positive-tail `F3` target staging.

The recovery companion uses the same staged expression and the formal
raw-order recovery theorem to prove that right-multiplication by
`(-(coord.solvedA1 (Fin.last ((M+1)+1))))^-1` recovers the source `F3`
tangent.  It performs no additional recurrence expansion.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed, and the full
`DLNFibre` build passed with only pre-existing unrelated style warnings.
`scripts/sorries` reported zero forbidden markers, `git diff --check` was
clean, the recovery theorem axiom audit reported only
`[propext, Classical.choice, Quot.sound]`, and Jason's xhigh recovery review
passed.

## 2026-06-27 A2 F3 positive-tail dEarly substitution

Reproduction:
`reproduction-a2-retained-passive-f3-positive-tail-dearly-substitution.md`.
Statement card:
`statement-card-a2-retained-passive-f3-positive-tail-dearly-substitution.md`.
Review:
`review-a2-retained-passive-f3-positive-tail-dearly-substitution.md`, PASS by
xhigh `Sartre`.

Lean now proves in `RetainedPassiveCoordinatesJacobian.lean`:

```text
F3_tail_pos_dEarly_zero_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_dEarly_zero_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

For positive tail length written as `M+1`, the theorem keeps the terminal
`dLast` target-staged expression and substitutes the first-index
zero-current `dEarly` formula into the remaining earlier-tail derivative:

```text
Dzv.F3
  - dEarly * coord.solvedA1(Fin.last (M+1))
  + (coord.F3 - Earlyfun z) * dLast_target
  = formal.F3.
```

The indexing is

```text
q0 = 0 : Fin (M+1),
p0 = q0.castSucc,
r0 = q0.succ,
qLast = Fin.last M : Fin (M+1).
```

The theorem leaves `dPsucc`, `dTail`, `dCnext`, and `(fderiv Nextfun z) v`
explicit.  It does not recurse through the full earlier-tail derivative and
does not claim full positive-tail `F3` target staging.  The recovery theorem
uses the formal raw-order `F3` recovery and right-multiplies the same staged
expression by `(-(coord.solvedA1(Fin.last (M+1))))^-1`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed.  The
`scripts/sorries` audit, `git diff --check`, and both theorem axiom audits also
passed; both theorems have only the standard
`[propext, Classical.choice, Quot.sound]` footprint.

Next frontier: recurse once into `Nextfun` using the successor-index `dEarly`
theorem, or target-stage one of the remaining explicit pieces.

## 2026-06-27 A2 dEarly successor dPcast substitution

Reproduction:
`reproduction-a2-retained-passive-dearly-succ-dpcast-substitution.md`.
Statement card:
`statement-card-a2-retained-passive-dearly-succ-dpcast-substitution.md`.
Review:
`review-a2-retained-passive-dearly-succ-dpcast-substitution.md`, PASS by
xhigh `Kierkegaard`.

Lean now proves in `RetainedPassiveCoordinatesDerivative.lean`:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_succ_product_dCprod_dG_dPcast_apply
```

For `s : Fin M`, the theorem sets

```text
q = s.succ,
u = s.castSucc,
p = q.castSucc,
r = q.succ.
```

It instantiates the existing nonterminal `dEarly` wrapper with `M := M+1`,
uses `Fin.succ_castSucc` to identify `u.succ = p`, and substitutes the
successor-current solved-`A1` residual-product derivative into the explicit
`dPcast` contribution:

```text
Cprod(z) * A3p(z) * Pcast(z)^-1
  * (dPsucc_z(v) * solvedA1_z(p) + Psucc(z) * v.1 u)
  * Pcast(z)^-1.
```

The tangent is exactly `v.1 s.castSucc`.  The theorem leaves `dPsucc`,
`Psucc`, and `solvedA1_z(p)` explicit.  It does not introduce `dTail`, does
not expand `dPsucc`, and does not terminal-clean.

Focused builds of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed.  The
`scripts/sorries` audit, `git diff --check`, and theorem axiom audit also
passed; the theorem has only the standard
`[propext, Classical.choice, Quot.sound]` footprint.

Next frontier: reassess the remaining `dEarly` source-staging boundary now
that the nonterminal current factor is split into zero and successor slices.

## 2026-06-27 A2 dEarly zero dPcast substitution

Reproduction:
`reproduction-a2-retained-passive-dearly-zero-dpcast-substitution.md`.
Statement card:
`statement-card-a2-retained-passive-dearly-zero-dpcast-substitution.md`.
Review:
`review-a2-retained-passive-dearly-zero-dpcast-substitution.md`, PASS by
xhigh `Pasteur`.

Lean now proves in `RetainedPassiveCoordinatesDerivative.lean`:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_zero_product_dCprod_dG_dPcast_apply
```

For the first-index nonterminal slice, the theorem sets

```text
q = 0 : Fin (M+1),
p = q.castSucc,
r = q.succ.
```

It instantiates the existing nonterminal `dEarly` wrapper with `M := M+1` and
substitutes the zero-current solved-`A1` residual-product derivative into the
explicit `dPcast` contribution:

```text
Cprod(z) * A3p(z) * Pcast(z)^-1
  * (dPsucc_z(v) * solvedA1_z(p)
      + Psucc(z) *
          (Tail^-1 * v.Ctop - Tail^-1 * dTail * Tail^-1 * data.Ctop))
  * Pcast(z)^-1.
```

The theorem leaves `dPsucc`, `Psucc`, `solvedA1_z(p)`, and `dTail` explicit.
It does not claim `Psucc = Tail`, does not expand `dTail`, and does not
terminal-clean the `M=0` case.

Focused builds of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed.  The
`scripts/sorries` audit, `git diff --check`, and theorem axiom audit also
passed; the theorem has only the standard
`[propext, Classical.choice, Quot.sound]` footprint.

Next frontier: prove the successor-current downstream `dEarly` source-staging
slice.  The indexing issue is that the wrapper's current factor is
`p = q.castSucc`; the next slice should expose a non-first current factor and
reindex it as a successor before applying the successor `dPcast` helper.

## 2026-06-27 A2 dPcast successor solved-A1 substitution

Reproduction:
`reproduction-a2-retained-passive-dpcast-succ-solveda1-substitution.md`.
Statement card:
`statement-card-a2-retained-passive-dpcast-succ-solveda1-substitution.md`.
Review:
`review-a2-retained-passive-dpcast-succ-solveda1-substitution.md`, PASS by
xhigh `Banach`.

Lean now proves in `RetainedPassiveCoordinatesDerivative.lean`:

```text
fderiv_retainedPassive_solvedA1_residualFactorProduct_succ_castSucc_apply
```

For `q : Fin M` and `p : Fin (M+1) := q.succ`, it specializes the solved-`A1`
residual product derivative and substitutes only the successor solved-`A1`
derivative:

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(p)
    + Psucc(z) * v.1 q.
```

The theorem leaves `dPsucc` and `solvedA1_z(p)` explicit.  The tangent is
exactly `v.1 q`, not a successor-indexed tangent.  It does not specialize a
downstream `dEarly` wrapper and does not claim terminal `Psucc` cleanup.

Focused builds of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed.  The
`scripts/sorries` audit, `git diff --check`, and theorem axiom audit also
passed; the theorem has only the standard
`[propext, Classical.choice, Quot.sound]` footprint.

Next frontier: consume the zero/successor current-factor split in the
downstream `dEarly` recurrence, explicitly handling the local current factor
`q.castSucc`.

## 2026-06-27 A2 dPcast zero solved-A1 substitution

Reproduction:
`reproduction-a2-retained-passive-dpcast-zero-solveda1-substitution.md`.
Statement card:
`statement-card-a2-retained-passive-dpcast-zero-solveda1-substitution.md`.
Review:
`review-a2-retained-passive-dpcast-zero-solveda1-substitution.md`, PASS by
xhigh `Hypatia`.

Lean now proves in `RetainedPassiveCoordinatesDerivative.lean`:

```text
fderiv_retainedPassive_solvedA1_residualFactorProduct_zero_castSucc_apply
```

For `p : Fin (M+1) := 0`, the theorem specializes the solved-`A1` residual
product derivative

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(p)
    + Psucc(z) * d(solvedA1 p)_z(v)
```

and substitutes only the zero solved-`A1` derivative:

```text
d(solvedA1 0)_z(v)
  = Tail^-1 * v.Ctop - Tail^-1 * dTail * Tail^-1 * data.Ctop.
```

Thus the proved result has the staged shape

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(0)
    + Psucc(z) *
        (Tail^-1 * v.Ctop - Tail^-1 * dTail * Tail^-1 * data.Ctop).
```

The theorem leaves `dPsucc` and `dTail` explicit, and also leaves the
first-summand pointwise factor `solvedA1_z(0)` explicit.  It does not assert
`Psucc = Tail`, does not expand `dTail`, and does not specialize a downstream
`dEarly` wrapper.

Focused builds of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed.  The
`scripts/sorries` audit, `git diff --check`, and theorem axiom audit also
passed; the theorem has only the standard
`[propext, Classical.choice, Quot.sound]` footprint.

Next frontier: prove the matching successor-current-factor residual-product
helper before consuming the split in a downstream `dEarly` wrapper.

## 2026-06-27 A2 solved-A1 zero derivative

Reproduction:
`reproduction-a2-retained-passive-solved-a1-zero-fderiv.md`.
Statement card:
`statement-card-a2-retained-passive-solved-a1-zero-fderiv.md`.
Review:
`review-a2-retained-passive-solved-a1-zero-fderiv.md`, PASS by xhigh
`Feynman`.

Lean now proves upstream in `RetainedPassiveCoordinatesDerivative.lean`:

```text
fderiv_retainedPassive_A1TailAfterFirst_inv_eq_tail_fderiv
fderiv_retainedPassive_toCoordinateData_solvedA1_zero_apply
```

For the zero solved top-left block, with

```text
Tfun(y) = retainedPassiveA1TailAfterFirst (ofTopologyTuple y).A1seed,
Tail    = Tfun(z),
dTail   = (fderiv Tfun z) v,
```

the theorem proves

```text
d_z(solvedA1(0))(v)
  = Tail^-1 * v.2.2.2.2.1
    - Tail^-1 * dTail * Tail^-1 * data.Ctop.
```

The determinant-chart hypothesis is required for the inverse-tail derivative.
The theorem leaves `dTail` as the actual Frechet derivative of the passive
tail map; it does not expand it recursively.  The inverse-tail theorem is now
stated over `TopologyTuple`, not over `RetainedPassiveRawTopologyTuple`, and
the duplicate downstream body was removed from
`RetainedPassiveCoordinatesJacobian.lean`.

Focused builds of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed.  The
`scripts/sorries` audit, `git diff --check`, full `DLNFibre` build, and
theorem axiom audits also passed; both theorem names have only the standard
`[propext, Classical.choice, Quot.sound]` footprint.

Nonclaims: no recursive `dTail` formula, no complete `dPcast` source-staging,
no target staging, no determinant theorem, no measure theorem, no normal
crossings, no pole order, and no RLCT.

Next frontier: substitute the solved-`A1` derivative split into the
retained-passive `dPcast`/`dEarly` source-staging theorems, keeping `dTail`
explicit until the tail recursion is intentionally opened.

## 2026-06-27 A2 solved-A1 successor derivative

Reproduction:
`reproduction-a2-retained-passive-solved-a1-successor-fderiv.md`.
Statement card:
`statement-card-a2-retained-passive-solved-a1-successor-fderiv.md`.
Review:
`review-a2-retained-passive-solved-a1-successor-fderiv.md`, PASS by xhigh
`Sagan` with statement adjustment to use `TopologyTuple`.

Lean now proves upstream in `RetainedPassiveCoordinatesDerivative.lean`:

```text
fderiv_retainedPassive_toCoordinateData_solvedA1_succ_apply
```

For `p : Fin M`, it identifies the successor branch of the solved top-left
family as the passive source tangent:

```text
d_z(solvedA1(p.succ))(v) = v.1 p.
```

The theorem has no determinant-chart hypothesis.  It is stated over
`TopologyTuple ρ κ' R`, not over the downstream
`RetainedPassiveRawTopologyTuple` abbreviation, so the derivative file remains
independent of `RetainedPassiveFormalRawOrder.lean`.  The duplicate theorem
body was removed from `RetainedPassiveCoordinatesJacobian.lean`; downstream
uses now import it from the derivative layer.

Focused builds of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed.  The
`scripts/sorries` audit, `git diff --check`, and theorem axiom audit passed;
the theorem has only the standard `[propext, Classical.choice, Quot.sound]`
footprint.

Nonclaims: no zero-branch formula, no inverse-tail derivative expansion, no
`dTail` recursive product formula, no complete `dPcast` source-staging, no
target staging, no determinant theorem, no measure theorem, no normal
crossings, no pole order, and no RLCT.

Next frontier: the zero solved-`A1` derivative branch

```text
d(solvedA1 0) = Tail^-1*dCtop - Tail^-1*dTail*Tail^-1*Ctop.
```

## 2026-06-27 A2 terminal Psucc cleanup obstruction

Obstruction note:
`obstruction-a2-retained-passive-dearly-terminal-psucc-not-empty.md`.

Xhigh reviewer `Meitner` ruled out the proposed terminal cleanup
`Psucc = 1`, `(fderiv Psucc) = 0`.  In the terminal `dPcast` theorem,
`q = Fin.last M` and `p = q.castSucc`, but the solved-`A1` successor product
starts at `p.succ = r.castSucc`, not at the final endpoint `r.succ`.  Thus
`Psucc` is a one-edge solved-`A1` suffix, not the empty product.

Do not retry this cleanup.  The correct next frontier is the solved-`A1`
derivative split: successor branch `d(solvedA1 q.succ)=v.1 q`; zero branch
`Tail^-1*dCtop - Tail^-1*dTail*Tail^-1*Ctop`, with determinant-chart
hypothesis and noncommutative order preserved.

## 2026-06-27 A2 dEarly terminal dPcast substitution

Reproduction:
`reproduction-a2-retained-passive-dearly-terminal-dpcast-substitution.md`.
Statement card:
`statement-card-a2-retained-passive-dearly-terminal-dpcast-substitution.md`.
Review:
`review-a2-retained-passive-dearly-terminal-dpcast-substitution.md`, PASS by
xhigh `Volta`.

Lean now proves:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_last_product_dCprod_dG_dPcast_apply
```

This is the terminal counterpart to the nonterminal `dPcast` substitution.  At
`q = Fin.last M`, with `p = q.castSucc`, it rewrites the terminal explicit
`dPcast` term as

```text
Cprod(z) * A3p(z) * Pcast(z)^-1
  * (dPsucc_z(v) * solvedA1_z(p)
      + Psucc(z) * d(solvedA1 p)_z(v))
  * Pcast(z)^-1.
```

The theorem leaves terminal `Psucc` and `d(solvedA1 p)` explicit.  The focused
module build for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` passed.  The
`scripts/sorries` audit, `git diff --check`, full `DLNFibre` build, and
theorem axiom audit also passed; the theorem has only the standard
`[propext, Classical.choice, Quot.sound]` footprint.

Nonclaims: no source-staging of `d(solvedA1 p)`, no terminal `Psucc` cleanup,
no target staging, no determinant-one `LinearEquiv`, no actual derivative
determinant equality, no measure transport, no normal crossings, no pole
order, and no RLCT.

## 2026-06-27 A2 dEarly dPcast substitution

Reproduction:
`reproduction-a2-retained-passive-dearly-dpcast-substitution.md`.
Statement card:
`statement-card-a2-retained-passive-dearly-dpcast-substitution.md`.
Review:
`review-a2-retained-passive-dearly-dpcast-substitution.md`, PASS by xhigh
`Euclid`.

Lean now proves:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_dPcast_castSucc_apply
```

This substitutes the solved-`A1` residual-product product rule into the
already `dCprod`/`dG`-staged retained-passive `dEarly` recurrence.  For
`q : Fin M`, set `p = q.castSucc` and `r = q.succ`.  The theorem replaces the
explicit term

```text
Cprod(z) * A3p(z) * Pcast(z)^-1 * dPcast_z(v) * Pcast(z)^-1
```

by

```text
Cprod(z) * A3p(z) * Pcast(z)^-1
  * (dPsucc_z(v) * solvedA1_z(p)
      + Psucc(z) * d(solvedA1 p)_z(v))
  * Pcast(z)^-1.
```

The derivative of the current solved-`A1` factor remains explicit.  The
focused module build for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` passed.  The
`scripts/sorries` audit, `git diff --check`, full `DLNFibre` build, and
theorem axiom audit also passed; the theorem has only the standard
`[propext, Classical.choice, Quot.sound]` footprint.

Nonclaims: no source-staging of `d(solvedA1 p)`, no iteration of `dPsucc`, no
closed finite-sum formula, no target staging, no determinant-one
`LinearEquiv`, no actual derivative determinant equality, no measure
transport, no normal crossings, no pole order, and no RLCT.

## 2026-06-27 A2 dEarly dPcast solvedA1 product rule

Reproduction:
`reproduction-a2-retained-passive-dearly-dpcast-solveda1-product-rule.md`.
Statement card:
`statement-card-a2-retained-passive-dearly-dpcast-solveda1-product-rule.md`.
Review:
`review-a2-retained-passive-dearly-dpcast-solveda1-product-rule.md`, PASS by
xhigh `Fermat`.

Lean now proves:

```text
fderiv_retainedPassive_solvedA1_residualFactorProduct_castSucc_apply
```

This is the narrow product-rule expansion for the solved-`A1` residual product
appearing as `Pcast` in the retained-passive `dEarly` recurrence.  For a
general `p : Fin (M+1)`,

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(p)
    + Psucc(z) * d(solvedA1 p)_z(v).
```

The theorem keeps the determinant-chart hypothesis because solved `A1` uses
matrix inversion at `p=0`, and it leaves `d(solvedA1 p)_z(v)` explicit.  The
focused module build for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` passed.  The
`scripts/sorries` audit, `git diff --check`, and full `DLNFibre` build also
passed; theorem axiom audit reports only the standard
`[propext, Classical.choice, Quot.sound]` footprint.

Nonclaims: no derivative formula for `solvedA1 0`, no complete `dPcast`
source-staging, no downstream Jacobian import, no substitution into the
`dEarly` recurrence, no target staging, no determinant-one `LinearEquiv`, no
actual derivative determinant equality, no measure transport, no normal
crossings, no pole order, and no RLCT.

## 2026-06-27 A2 dEarly terminal dCprod boundary

Reproduction:
`reproduction-a2-retained-passive-dearly-terminal-dcprod-boundary.md`.
Statement card:
`statement-card-a2-retained-passive-dearly-terminal-dcprod-boundary.md`.
Review:
`review-a2-retained-passive-dearly-terminal-dcprod-boundary.md`, PASS by
xhigh `Copernicus`.

Lean now proves:

```text
fderiv_retainedPassive_C_residualFactorProduct_self_apply
fderiv_retainedPassiveLowerLeftProductTailSum_last_product_dCprod_dG_apply
```

This is the terminal boundary companion to the source-staged `dCprod`
recurrence.  For `q = Fin.last M : Fin (M+1)`, with `p = q.castSucc` and
`r = q.succ`, the theorem collapses the empty successor stored-`C` derivative
and the successor zeroed-final tail derivative:

```text
dCnext_z(v) = 0,
dNextTail_z(v) = 0.
```

The Lean statement deliberately leaves the empty-product value `Cnext(z)`, the
one-edge boundary value `Cprod(z)`, and `dPcast_z(v)` explicit.  The first
current-summand term is therefore recorded as

```text
-((0 * C_z r + Cnext(z) * v.2.2.2.1 r) * A3p(z) * Pcast(z)^-1).
```

Focused module build for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` passed after the
post-interruption reorientation.  The `scripts/sorries` audit,
`git diff --check`, full `DLNFibre` build, and theorem axiom audit also
passed; both new theorem names have only the standard
`[propext, Classical.choice, Quot.sound]` footprint.

Nonclaims: no empty-product value cleanup, no one-edge `Cprod` cleanup, no
`dPcast` staging, no closed finite-sum formula for `dCprod`, no target
staging, no full positive-tail `F3` target staging, no determinant-one
`LinearEquiv`, no actual derivative determinant equality, no measure
transport, no normal crossings, no pole order, and no RLCT.

## 2026-06-27 A2 dEarly dCprod source staging

Reproduction:
`reproduction-a2-retained-passive-dearly-dcprod-source-staging.md`.
Statement card:
`statement-card-a2-retained-passive-dearly-dcprod-source-staging.md`.
Review:
`review-a2-retained-passive-dearly-dcprod-source-staging.md`, PASS by xhigh
`Lovelace`.

Lean now proves:

```text
fderiv_retainedPassive_C_apply
fderiv_retainedPassive_C_residualFactorProduct_castSucc_apply
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_castSucc_apply
```

This source-stages the `dCprod` factor in the retained-passive `dEarly`
product-rule recurrence after the `dG` substitution.  For `q : Fin M`, with
`p = q.castSucc` and `r = q.succ`, it rewrites the suffix-product derivative as

```text
dCprod_z(v) = dCnext_z(v) * C_z r + Cnext(z) * v.2.2.2.1 r.
```

The theorem keeps `dCnext`, `dPcast`, and the successor-tail derivative
explicit.  Focused module build for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` passed.  The
`scripts/sorries` audit, `git diff --check`, full `DLNFibre` build, and
theorem axiom audit also passed; all three new theorem names have only the
standard `[propext, Classical.choice, Quot.sound]` footprint.

Nonclaims: no `dPcast` staging, no closed finite-sum formula for `dCprod`, no
target staging, no full positive-tail `F3` target staging, no determinant-one
`LinearEquiv`, no actual derivative determinant equality, no measure
transport, no normal crossings, no pole order, and no RLCT.

## 2026-06-27 A2 dEarly terminal zero tail

Reproduction:
`reproduction-a2-retained-passive-dearly-terminal-zero-tail.md`.
Statement card:
`statement-card-a2-retained-passive-dearly-terminal-zero-tail.md`.
Review:
`review-a2-retained-passive-dearly-terminal-zero-tail.md`, PASS by xhigh
`Aquinas`.

Lean now proves:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_withoutLast_last_apply
```

This is the terminal boundary for the retained-passive `dEarly` recurrence
when the final `A3` block is zeroed by `retainedPassiveA3WithoutLast`.  The
tail at index `M (Nat.le_succ M)` is pointwise constant zero, by the algebraic
lemma `retainedPassiveLowerLeftProductTailSum_withoutLast_last`, so its
Frechet derivative is zero at every ambient tuple and tangent.

Focused module build for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` passed.  The
`scripts/sorries` audit, `git diff --check`, full `DLNFibre` build, and
theorem axiom audit also passed; the theorem has only the standard
`[propext, Classical.choice, Quot.sound]` footprint.

Nonclaims: not a solved terminal `A3` or `F3` derivative theorem, no `dCprod`
staging, no `dPcast` staging, no target staging, no full positive-tail `F3`
target staging, no determinant-one `LinearEquiv`, no actual derivative
determinant equality, no measure transport, no normal crossings, no pole
order, and no RLCT.

## 2026-06-27 A2 dEarly product-rule dG substitution

Reproduction:
`reproduction-a2-retained-passive-dearly-product-rule-dg-substitution.md`.
Statement card:
`statement-card-a2-retained-passive-dearly-product-rule-dg-substitution.md`.
Review:
`review-a2-retained-passive-dearly-product-rule-dg-substitution.md`, PASS by
xhigh `Averroes`.

Lean now proves:

```text
fderiv_retainedPassiveA3WithoutLast_apply
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dG_castSucc_apply
```

This substitutes the nonterminal source-staged `dG` factor into the retained-
passive `dEarly` product-rule recurrence.  For `p = q.castSucc`, the term
`- Cprod(z) * (fderiv A3p z)(v) * Pcast(z)^{-1}` is rewritten as
`- Cprod(z) * v.2.2.1 q * Pcast(z)^{-1}`.  The matrix factor order is
unchanged.

Focused module build for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` passed.  The
`scripts/sorries` audit, `git diff --check`, full `DLNFibre` build, and
theorem axiom audit also passed; both new theorems have only the standard
`[propext, Classical.choice, Quot.sound]` footprint.

Nonclaims: no `dCprod` staging, no `dPcast` staging, no target staging, no
full positive-tail `F3` target staging, no determinant-one `LinearEquiv`, no
actual derivative determinant equality, no measure transport, no normal
crossings, no pole order, and no RLCT.

## 2026-06-27 A2 dEarly dG source staging

Reproduction:
`reproduction-a2-retained-passive-dearly-dg-source-staging.md`.
Statement card:
`statement-card-a2-retained-passive-dearly-dg-source-staging.md`.
Review:
`review-a2-retained-passive-dearly-dg-source-staging.md`, PASS by xhigh
`Halley` and xhigh `Nietzsche`.

Lean now proves:

```text
fderiv_retainedPassiveA3WithoutLast_castSucc_apply
fderiv_retainedPassiveA3WithoutLast_last_apply
```

These theorems source-stage the `dG` factor in the retained-passive `dEarly`
product-rule recurrence.  For nonterminal `q : Fin M`, the derivative is the
passive source tangent `v.2.2.1 q`; at the terminal edge `Fin.last M`, it is
zero.  This is the zeroed retained-passive `G_p`, not the solved terminal
lower-left block.

Focused module build for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` passed.  The
`scripts/sorries` audit, `git diff --check`, full `DLNFibre` build, and
theorem axiom audit also passed; both new theorems have only the standard
`[propext, Classical.choice, Quot.sound]` footprint.

Nonclaims: no target staging, no `dD` or `dP` staging, no full positive-tail
`F3` target staging, no determinant-one `LinearEquiv`, no actual derivative
determinant equality, no measure transport, no normal crossings, no pole
order, and no RLCT.

## 2026-06-27 A2 dEarly product-rule derivative unfold

Reproduction:
`reproduction-a2-retained-passive-dearly-product-rule-unfold.md`.
Statement card:
`statement-card-a2-retained-passive-dearly-product-rule-unfold.md`.
Review:
`review-a2-retained-passive-dearly-product-rule-unfold.md`, PASS by xhigh
`Wegener`.

Lean now proves:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_apply
```

This refines the recursive `dEarly` derivative theorem by expanding the
current summand derivative with the noncommutative product rule and matrix
inverse derivative:

```text
dE_p =
  -dD_p * G_p * P_p^-1
  -D_p * dG_p * P_p^-1
  +D_p * G_p * P_p^-1 * dP_p * P_p^-1
  +dE_next.
```

The derivatives `dD_p`, `dG_p`, and `dP_p` remain explicit.  `G_p` is the
zeroed retained-passive family `retainedPassiveA3WithoutLast`, not the solved
terminal lower-left block.

Focused module build for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` passed.  Full
`DLNFibre` build passed; `scripts/sorries`, `git diff --check`, and axiom audit
passed.  Xhigh math and Lean-terrain scouts passed.  Xhigh implementation
review passed.

Nonclaims: no source or target staging for `dD`, `dG`, or `dP`, no full
positive-tail `F3` target staging, no determinant-one `LinearEquiv`, no actual
derivative determinant equality, no measure transport, no normal crossings, no
pole order, and no RLCT.

## 2026-06-27 A2 dEarly recursive derivative unfold

Reproduction:
`reproduction-a2-retained-passive-dearly-recursive-unfold.md`.
Statement card:
`statement-card-a2-retained-passive-dearly-recursive-unfold.md`.
Review:
`review-a2-retained-passive-dearly-recursive-unfold.md`, PASS by xhigh
`Faraday`.

Lean now proves:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_apply
```

This is the minimal recursive `dEarly` derivative unfold.  For arbitrary
`p : Fin (M + 1)`, the derivative of the tail
`retainedPassiveLowerLeftProductTailSum ... p.val` is rewritten as the
derivative of the current summand

```text
fun y => -(Cprod y * A3p y * (Pcast y)^-1)
```

plus the derivative of the successor tail.  The current summand derivative is
kept explicit; no source or target staging is claimed.  `A3p` is the zeroed
family `retainedPassiveA3WithoutLast`, not the solved terminal lower-left
block.

Focused module build for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` passed.  Full
`DLNFibre` build passed; `scripts/sorries`, `git diff --check`, and axiom audit
passed.

Nonclaims: no full positive-tail `F3` target staging, no source or target
staging for `dD`, `dG`, or `dP`, no determinant-one `LinearEquiv`, no actual
derivative determinant equality, no measure transport, no normal crossings, no
pole order, and no RLCT.

## 2026-06-27 A2 F3 positive-tail dLast target-staged shear

Reproduction:
`reproduction-a2-retained-passive-f3-positive-tail-dlast-target-staged.md`.
Statement card:
`statement-card-a2-retained-passive-f3-positive-tail-dlast-target-staged.md`.
Review:
`review-a2-retained-passive-f3-positive-tail-dlast-target-staged.md`, PASS by
xhigh `Raman`.

Lean now proves the terminal `dLast` substitution slice:

```text
fderiv_retainedPassive_toCoordinateData_solvedA1_succ_apply
F3_tail_pos_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

For a terminal passive index `q : Fin M` with `q.succ = Fin.last M`, the
terminal top residual product `Last` is the terminal solved top block
`coord.solvedA1 (Fin.last M)`, and its Frechet derivative is the passive
source tangent `v.1 q`.  The theorem replaces only this `dLast` factor by the
target-staged passive `A1` expression

```text
Dzv.1 q
  - retainedPassiveTargetRecoveredSuccessorF2At(z,Dzv)(q.succ)
      * coord.solvedA3(q.succ)
  - coord.F2(q.succ.succ) * rawEdgeTupleA3(Dzv,q.succ).
```

The `dEarly` term remains explicit in the positive-tail `F3` bridge.  Focused
module build and full `DLNFibre` build passed via `scripts/lb`; `scripts/sorries`
reported zero forbidden markers; `git diff --check` passed; theorem axiom
audits report only `[propext, Classical.choice, Quot.sound]`; independent
implementation review passed.

Nonclaims: no full positive-tail `F3` target staging, no derivative recurrence
for `Early`, no whole-tuple target-side normalization, no determinant-one
`LinearEquiv`, no actual derivative determinant equality, no measure
transport, no normal crossings, no pole order, and no RLCT.

## 2026-06-27 A2 F3 zero-tail target-staged shear

Reproduction:
`reproduction-a2-retained-passive-f3-mzero-target-staged-shear.md`.
Statement card:
`statement-card-a2-retained-passive-f3-mzero-target-staged-shear.md`.
Review:
`review-a2-retained-passive-f3-mzero-target-staged-shear.md`, PASS by xhigh
`Bernoulli`.

Lean now proves the one-edge (`M = 0`) `F3` target-staged formula:

```text
F3_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

The theorem collapses the landed `F3` source-staged bridge by proving the
one-edge `Early` source tail is zero and the one-edge `Last` top factor is
`coord.Ctop`.  It then substitutes the landed Ctop zero-tail target-staged
recovery.  The final expression contains
`retainedPassiveTargetRecoveredSuccessorF2At z Dzv` and the raw target readout
`rawEdgeTupleA3 Dzv 0` only inside
`coord.F2 (0 : Fin 1).succ * rawEdgeTupleA3 Dzv 0`.  Recovery right-multiplies
by `(-(coord.Ctop))⁻¹`.

Focused/full builds, `scripts/sorries`, `git diff --check`, and axiom audit
all passed; the new theorems depend only on
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no positive-tail `F3` target staging, no derivative recurrence for
`Early`, no whole-tuple target-side normalization, no determinant-one
`LinearEquiv`, no actual derivative determinant equality, no measure
transport, no normal crossings, no pole order, and no RLCT.

## 2026-06-27 A2 Ctop target-staged endpoint shear

After passive `A1` target staging, the analogous Ctop endpoint step is to
consume the target-recovered successor `F2` family and the multiplied raw
lower-left target readout at the first retained edge `0 : Fin (M+1)`.
Reproduction:
`reproduction-a2-retained-passive-ctop-target-staged-endpoint-shear.md`.
Statement card:
`statement-card-a2-retained-passive-ctop-target-staged-endpoint-shear.md`.

Lean now keeps the already-landed zero/positive tail split.  For `M = 0`, it
replaces the two source-staged successor terms in the empty-tail Ctop formula.
For `0 < M`, it makes the same replacement while leaving the explicit suffix derivative
`(fderiv Psucc z) v * data.A1seed p + Psucc z * v.A1passive_q` in the same
noncommutative order.  The terminal lower-left target derivative is not
claimed to be zero; in the zero-tail case it is used only under the terminal
zero extended `F2` multiplier.

New Lean names:

```text
Ctop_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_pos_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
Ctop_tail_pos_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
```

Review:
`review-a2-retained-passive-ctop-target-staged-endpoint-shear.md`
passed by xhigh `Einstein`.  Focused/full builds, `scripts/sorries`,
`git diff --check`, and axiom audit all passed; the new theorems depend only
on `[propext, Classical.choice, Quot.sound]`.

Nonclaims: no `F3` target staging, no whole-tuple target-side normalization,
no determinant-one `LinearEquiv`, no actual derivative determinant equality,
no measure transport, no normal crossings, no pole order, and no RLCT.

## 2026-06-27 A2 passive A1 target-staged shear

After the target-side `(F2,C)` edge-pair recovery landed, the next branch that
can consume it without claiming a determinant theorem is passive `A1`.  The
new reproduction is
`reproduction-a2-retained-passive-a1passive-target-staged-shear.md`; statement
card:
`statement-card-a2-retained-passive-a1passive-target-staged-shear.md`.

Lean now replaces the passive `A1` source-staged successor `F2` correction by
`retainedPassiveTargetRecoveredSuccessorF2At z Dzv` and replaces the
source-staged lower-left correction by `rawEdgeTupleA3 Dzv q` only under left
multiplication by `coord.F2 q.succ`.  The terminal lower-left derivative is
not claimed to be zero; it is killed by the terminal zero extended `F2` slot.

New Lean names:

```text
retainedPassive_F2_succ_mul_rawEdgeTupleA3_fderiv_eq_sourceStagedSuccessorA3
A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_A1passive
```

Review:
`review-a2-retained-passive-a1passive-target-staged-shear.md`
passed by xhigh `Boyle`.  Focused/full builds, `scripts/sorries`,
`git diff --check`, and axiom audit all passed; the new theorems depend only
on `[propext, Classical.choice, Quot.sound]`.

Nonclaims: no `Ctop` target staging, no `F3` target staging, no whole-tuple
target-side normalization, no determinant-one `LinearEquiv`, no actual
derivative determinant equality, no measure transport, no normal crossings,
no pole order, and no RLCT.

## 2026-06-27 A2 target-side edge-pair recovery frontier

Post-interruption reorientation found the expedition worktree clean at
`f7d63f10` on `origin/expedition/aoyagi-rlct`.  Read-only xhigh scouts `Curie`
and `Maxwell` both warned against jumping to determinant equality.  Curie
identified the next determinant-relevant gap as target-side reconstruction of
the `(F2,C)` edge family; Maxwell independently confirmed that any theorem
still mentioning source-staged or derivative-staged corrections is not a
determinant theorem.

Chosen next slice:
`reproduction-a2-retained-passive-target-edge-pair-recovery.md`.
Statement card:
`statement-card-a2-retained-passive-target-edge-pair-recovery.md`.
Review:
`review-a2-retained-passive-target-edge-pair-recovery.md`, PASS after
documentation status repair.

Lean now defines a backward target recurrence: recover terminal `F2` using
the zero successor correction, recover each nonterminal `F2` using the
recovered successor value transported by the
`p.succ.castSucc = p.castSucc.succ` cast, then build the target-side all-edge
`(F2,C)` shear.  On actual derivatives, this target successor family equals
the earlier source-staged successor family, so the existing all-edge
source-staged theorem is reused.

Nonclaims remain active: no whole-tuple target-side normalization, no
determinant-one `LinearEquiv`, no actual derivative determinant equality, no
measure transport, no normal crossings, no pole order, and no RLCT.

## 2026-06-27 A2 Ctop/F3 source-staged recovery consumers

After the Ctop tail endpoint substitution, the controller chose the small
consumer slice rather than a closed finite-sum expansion of `dTail`.  The
finite-sum formula remains plausible, but it is not needed for the next
determinant/shear consumers and would introduce dependent-index and
noncommutative-order friction before a downstream theorem needs it.

Reproduction:
`reproduction-a2-retained-passive-ctop-f3-recovery-consumers.md`.
Statement card:
`statement-card-a2-retained-passive-ctop-f3-recovery-consumers.md`.
Review:
`review-a2-retained-passive-ctop-f3-recovery-consumers.md`, PASS after
documentation repair by xhigh `Turing`.  Focused Jacobian build, full
`DLNFibre` build, `scripts/sorries`, `git diff --check`, and theorem axiom
audit all passed.

Lean now proves:

```text
Ctop_tail_zero_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
Ctop_tail_pos_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
F3_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

The two `Ctop` theorems rewrite the already-landed staged component equality
into the formal `Ctop` component and then use
`retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop`.  The positive-tail
theorem keeps the first passive recurrence substitution inside the two
`Tail^{-1}` factors and leaves the suffix derivative `(fderiv Psucc z) v`
explicit.

The `F3` theorem rewrites the terminal lower-left staged expression into the
formal `F3` component and then uses
`retainedPassiveFormalRawOrderJacobianAt_recovers_F3`, right-multiplying by
the inverse of `-(coord.solvedA1 (Fin.last M))`.  This terminal factor is
`coord.Ctop` when `M=0`; it is not the passive tail.

All three theorems assume `z in topologyTupleDetChartSet`; the statement card
now records this determinant-chart hypothesis explicitly.  Nonclaims remain:
no closed finite-sum formula for `dTail`, no F3 early-tail derivative formula,
no full source-staged tuple theorem, no target-side determinant-one
`LinearEquiv`, no determinant equality, no measure transport, no normal
crossings, no pole order, and no RLCT.

## 2026-06-27 A2 all-edge source-staged edge-pair package

After post-crash reorientation in the dedicated worktree, the next retained-
passive Jacobian slice is the all-edge source-staged `(F2,C)` packaging lemma.
Xhigh scout `Chandrasekhar` passed the statement shape before implementation.

Reproduction:
`reproduction-a2-retained-passive-all-edge-pair-source-staged-target-shear.md`.
Statement card:
`statement-card-a2-retained-passive-all-edge-pair-source-staged-target-shear.md`.

Lean now defines the staged successor family by `Fin.snoc`: nonterminal edges
use the casted successor source tangent, and the terminal edge uses zero.  The
proof splits an arbitrary retained edge by `Fin.lastCases`, reuses the
terminal edge-pair package in the last case and the nonterminal source-staged
package in the castSucc case, then applies the formal edge-pair inverse to
recover `(v.F2, v.C)`.  Review:
`review-a2-retained-passive-all-edge-pair-source-staged-target-shear.md`
passed by xhigh `Dewey`.

Nonclaims remain active: no determinant equality, no determinant-one
target-side `LinearEquiv`, no descending induction, no measure transport, no
normal crossings, no pole order, and no RLCT.

## 2026-06-27 A2 edge-pair source-staged tuple assembly

Xhigh statement scout `Descartes` passed the next narrow package: a hybrid
whole-tuple assembly whose `(F2,C)` branch uses the all-edge source-staged
edge-pair family, while the passive `A1`, passive `A3`, `Ctop`, and `F3`
branches remain the existing derivative-staged tuple assembly.

Reproduction:
`reproduction-a2-retained-passive-edge-pair-source-staged-tuple-assembly.md`.
Statement card:
`statement-card-a2-retained-passive-edge-pair-source-staged-tuple-assembly.md`.

The intended Lean names are
`edgePairSourceStagedShearedTopologyTupleEdgeRawOrderFDerivAt` and
`edgePairSourceStaged_sheared_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`.
Lean now proves both.  Review:
`review-a2-retained-passive-edge-pair-source-staged-tuple-assembly.md` passed
by xhigh `Dalton`.  The naming must not suggest that the whole tuple is
source-staged.  Nonclaims: no target-side `LinearEquiv`, determinant-one
shear, actual derivative determinant equality, measure transport, normal
crossings, pole order, or RLCT.

## 2026-06-27 A2 passive A1 source-staged shear

Next narrow derivative-factorization slice: source-stage the passive
`A1passive` correction terms only, while leaving `Ctop` and `F3`
derivative-staged.

Reproduction:
`reproduction-a2-retained-passive-a1passive-source-staged-shear.md`.
Statement card:
`statement-card-a2-retained-passive-a1passive-source-staged-shear.md`.
Review:
`review-a2-retained-passive-a1passive-source-staged-shear.md` passed by xhigh
`Lagrange`.

Lean now defines the staged successor lower-left family
`retainedPassiveSourceStagedSuccessorA3`, proves the nonterminal projection
derivative
`fderiv_retainedPassive_toCoordinateData_solvedA3_castSucc_apply`, proves the
all-edge successor `F2` derivative readout, and proves the all-edge
multiplier identity
`retainedPassive_F2_succ_mul_fderiv_solvedA3_eq_sourceStagedSuccessorA3`.
The terminal case of that multiplier theorem uses only the terminal zero
extended `F2` slot; it does not identify the terminal `solvedA3` derivative.

The resulting passive `A1` source-staged bridge is
`A1passive_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`.
This is not a fully source-staged tuple, not `Ctop` or `F3` staging, not a
target-side `LinearEquiv`, not determinant-one shear, not determinant equality,
and not measure transport, normal crossings, pole order, or RLCT.

## 2026-06-27 A2 formal non-edge recovery

Formal inverse bookkeeping for the non-edge branches of
`retainedPassiveFormalRawOrderJacobianAt` has landed.

Reproduction:
`reproduction-a2-retained-passive-formal-nonedge-recovery.md`.
Statement card:
`statement-card-a2-retained-passive-formal-nonedge-recovery.md`.
Review:
`review-a2-retained-passive-formal-nonedge-recovery.md` passed by xhigh
`Nash`.

Lean now proves:

```text
retainedPassiveFormalRawOrderJacobianAt_recovers_A1passive
retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop
retainedPassiveFormalRawOrderJacobianAt_recovers_F3
```

The `A1passive` recovery is projection-level.  The `Ctop` recovery multiplies
the formal output by the solved first-edge top-left tail and uses determinant
unitness of `Tail`.  The `F3` recovery right-multiplies by the nonsingular
inverse of `-(coord.solvedA1 (Fin.last M))`.

This is formal-map recovery only.  It does not identify the actual Frechet
derivative with the formal map, source-stage `Ctop` or `F3`, prove a
target-side determinant-one equivalence, determinant equality, measure
transport, normal crossings, pole order, or RLCT.

## 2026-06-27 A2 Ctop source-staged successor shear

The next narrow Ctop derivative slice has landed locally.

Reproduction:
`reproduction-a2-retained-passive-ctop-source-staged-successor-shear.md`.
Statement card:
`statement-card-a2-retained-passive-ctop-source-staged-successor-shear.md`.
Review:
`review-a2-retained-passive-ctop-source-staged-successor-shear.md` passed by
xhigh `Kant`.

Lean now proves:

```text
Ctop_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

The theorem starts from the existing `Ctop` derivative-staged bridge and
rewrites only the successor `F2` derivative and the multiplied successor
lower-left derivative:

```text
Dzv.Ctop
  - X_F(0) * coord.solvedA3 0
  - coord.F2 1 * X_G(0)
  - d(Tail^{-1})_z(v) * coord.Ctop
= formal(z)(v).Ctop.
```

The passive-tail inverse derivative remains the explicit Frechet derivative
term.  This is not full `Ctop` source staging, not a tail-product derivative
formula, not `F3` staging, not a target-side `LinearEquiv`, not determinant
equality, and not measure transport, normal crossings, pole order, or RLCT.

## 2026-06-27 A2 retained-passive tail-inverse Frechet derivative

The next narrow inverse-tail slice is implemented locally.

Reproduction:
`reproduction-a2-retained-passive-tail-inverse-fderiv.md`.
Statement card:
`statement-card-a2-retained-passive-tail-inverse-fderiv.md`.
Review:
`review-a2-retained-passive-tail-inverse-fderiv.md` passed by xhigh
`Epicurus`.

Lean now proves:

```text
fderiv_retainedPassive_A1TailAfterFirst_inv_eq_tail_fderiv
Ctop_tail_fderiv_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

The first theorem applies the matrix-inverse Frechet derivative to the actual
tail map

```text
Tfun(y) = retainedPassiveA1TailAfterFirst (ofTopologyTuple y).A1seed
```

and proves

```text
d_y(Tfun(y)^{-1})_z(v) = -Tail^{-1} * dTail * Tail^{-1},
```

where `dTail = (fderiv Tfun z) v`.  The determinant-chart hypothesis is used
only to get `IsUnit det(Tail)` from the passive top-left unit fields.  The
second theorem substitutes this identity into the previous `Ctop` successor
staging bridge, changing the `-d(Tail^{-1})*Ctop` term to
`+Tail^{-1}*dTail*Tail^{-1}*Ctop`.

Verification so far: focused
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` build passed and full
`DLNFibre` build passed.  `scripts/sorries` reported zero forbidden markers,
`git diff --check` passed, and both new theorem axiom audits report only
`[propext, Classical.choice, Quot.sound]`.

This still does not compute `dTail` as a recursive product.  It is not full
`Ctop` source staging, not `F3` staging, not a target-side `LinearEquiv`, not
determinant equality, and not measure transport, normal crossings, pole order,
or RLCT.

## 2026-06-27 A2 retained-passive tail product FDeriv recursion

The next narrow tail-product derivative slice is implemented locally.

Reproduction:
`reproduction-a2-retained-passive-tail-product-fderiv-recursion.md`.
Statement card:
`statement-card-a2-retained-passive-tail-product-fderiv-recursion.md`.

Lean now proves:

```text
differentiableAt_retainedPassiveA1seed_residualFactorProduct
fderiv_retainedPassive_A1seed_residualFactorProduct_self_apply
fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_apply
```

The first theorem exposes differentiability of every suffix of the passive
`A1seed` product.  The endpoint theorem says the derivative of the empty
suffix product is zero.  The recursive step says, for `q : Fin M` and
`p=q.succ`,

```text
d(P_{p.castSucc})_z(v)
  = d(P_{p.succ})_z(v) * A1seed_z(p)
    + P_{p.succ}(z) * v.A1passive_q.
```

The theorem rewrites the derivative of `A1seed(q.succ)` to the source tangent
`v.1 q`, so the dummy `A1seed 0` is not part of this passive-tail recurrence.
No determinant-chart hypothesis is used.

Verification so far: focused
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` build passed.
Independent xhigh implementation review passed after a documentation wording
fix, recorded in
`review-a2-retained-passive-tail-product-fderiv-recursion.md`.  Full
`DLNFibre` build passed.  `scripts/sorries` reported `0 sorry`, `0 #exit`,
`0 native_decide`, and `0 axiom`; `git diff --check` passed.  Axiom audit for
the three new theorems reported only `propext`, `Classical.choice`, and
`Quot.sound`.

This is still not a closed finite-sum formula for `dTail`; it is the
recursive product-rule step.  It is not full `Ctop` source staging, not `F3`
staging, not determinant equality, and not measure transport, normal
crossings, pole order, or RLCT.

## 2026-06-27 A2 retained-passive tail endpoint FDeriv

The next direct endpoint specialization of the recurrence is implemented
locally.

Reproduction:
`reproduction-a2-retained-passive-tail-endpoint-fderiv.md`.
Statement card:
`statement-card-a2-retained-passive-tail-endpoint-fderiv.md`.

Lean now proves:

```text
fderiv_retainedPassive_A1TailAfterFirst_zero_apply
fderiv_retainedPassive_A1TailAfterFirst_succ_apply
fderiv_retainedPassive_A1TailAfterFirst_pos_apply
```

The zero theorem says that when `M=0`, the tail after the first edge is the
empty residual product and its derivative is zero.  The successor-indexed and
positive-length theorems specialize the passive suffix-product recurrence to
the first passive factor:

```text
d(Tail)_z(v)
  = d(Psucc)_z(v) * A1seed_z(p) + Psucc(z) * v.A1passive_0.
```

Here `Psucc` is the suffix after the first passive factor, `p` is the seed
index `1`, and the source tangent is the right factor in the second product.
The dummy `A1seed 0` is not part of the tail.

Verification so far: focused
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` build passed.
Pen-and-paper scout `Goodall` and Lean/API scout `Bohr` both recommended this
boundary.  Independent xhigh implementation review `Russell` passed, recorded
in `review-a2-retained-passive-tail-endpoint-fderiv.md`.  Full `DLNFibre`
build passed.  `scripts/sorries` reported `0 sorry`, `0 #exit`,
`0 native_decide`, and `0 axiom`; `git diff --check` passed.  Axiom audit for
the three new theorems reported only `propext`, `Classical.choice`, and
`Quot.sound`.

This is still not a closed finite-sum formula for `dTail`; it only opens the
first endpoint recurrence step.  It is not full `Ctop` source staging, not
`F3` staging, not determinant equality, and not measure transport, normal
crossings, pole order, or RLCT.

## 2026-06-27 A2 retained-passive Ctop tail endpoint substitution

The direct Ctop consumer of the endpoint tail derivative is implemented
locally.

Reproduction:
`reproduction-a2-retained-passive-ctop-tail-endpoint-substitution.md`.
Statement card:
`statement-card-a2-retained-passive-ctop-tail-endpoint-substitution.md`.

Lean now proves:

```text
Ctop_tail_zero_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_pos_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

The zero theorem uses `dTail=0` for the empty passive tail and removes only
the tail correction term from the existing Ctop bridge.  The positive theorem
substitutes the first passive endpoint recurrence into the already positive
tail-inverse correction term:

```text
+ Tail^{-1}
    * (d(Psucc)_z(v) * A1seed_z(p) + Psucc(z) * v.A1passive_0)
    * Tail^{-1}
    * coord.Ctop.
```

The remaining suffix derivative `d(Psucc)` is still explicit.  The theorem
does not introduce the dummy `A1seed 0`.

Verification so far: focused
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` build passed.
Pen-and-paper scout `Godel` and Lean/API scout `Hooke` both recommended this
boundary.  Independent xhigh implementation review `Galileo` passed, recorded
in `review-a2-retained-passive-ctop-tail-endpoint-substitution.md`.  Full
`DLNFibre` build passed.  `scripts/sorries` reported `0 sorry`, `0 #exit`,
`0 native_decide`, and `0 axiom`; `git diff --check` passed.  Axiom audit for
the two new theorems reported only `propext`, `Classical.choice`, and
`Quot.sound`.

This is not a closed finite-sum formula for `dTail` and not full `Ctop`
source staging.  It is not `F3` staging, determinant equality, measure
transport, normal crossings, pole order, or RLCT.

## 2026-06-18 A1 narrow tide

Opened xhigh worker tide `Lovelace` for the first Lean implementation. Scope is
only Aoyagi Lemma 2's checked algebraic block-elimination chart identity, and
possibly the rank formula if it falls out without overclaiming. Explicitly out
of scope: RLCT invariance, local-germ/ideal consequences, Theorem 3 product
reduction, and target-normalisation claims.

Read-only xhigh statement reviewer `Euclid` was also opened to audit the exact
statement shape before controller acceptance.

Outcome: landed two algebraic block identities in
`lean/DLNFibre/DLN/Aoyagi/BlockElimination.lean`:
`schurComplement_leftBlockElim_fromBlocks` and
`schurComplement_blockElim_fromBlocks`. Theorems are over `[CommRing K]` with
explicit chart hypothesis `IsUnit A1.det`, and contain no rank/RLCT/germ/ideal
claim. Controller verified targeted build, full `DLNFibre` build, and
`scripts/sorries`. Statement card:
`statement-card-a1-block-identities.md`.

Remaining A1 target: rank formula as a separate theorem, likely via a
block-diagonal rank lemma over a field. A2 remains blocked by the checker
findings: source-faithful basis/open-chart hypotheses and analytic-boundary
decision.

## 2026-06-18 A1 rank-formula tide

Opened xhigh worker tide `Lovelace` to prove a separate block-diagonal rank
theorem and then the Schur-complement rank corollary. Scope remains purely
algebraic: no RLCT/germ/ideal/Theorem 3 claim.

Outcome: landed `rank_fromBlocks_zero_zero` and
`rank_fromBlocks_eq_card_add_rank_schurComplement_of_isUnit_det` in
`lean/DLNFibre/DLN/Aoyagi/BlockElimination.lean`. Controller verified targeted
build, full `DLNFibre` build, and `scripts/sorries`. Xhigh reviewer `Euclid`
accepted after minor docstring/name edits. Rank statement card:
`statement-card-a1-rank-formula.md`.

## 2026-06-18 A2 repair scout

Opened xhigh read-only scout `Erdos` to repair the pen-and-paper reproduction of
Aoyagi Theorem 3/product reduction before any A2 Lean target. The requested
output is a source-faithful algebraic statement, induction invariant, boundary
case analysis, and separation of analytic/RLCT assumptions.

Outcome: report saved at `reproduction-repair-a2.md`. Verdict: full Theorem 3
is still blocked, but the chart-local algebraic induction-step theorem is
reproduction-ready for Lean. The target-product normalization and post-Theorem-3
RLCT equality remain analytic-boundary issues.

## 2026-06-18 A2 chart-local induction-step tide

Opened xhigh formalisation work on only the reproduction-ready chart-local
algebraic induction step from the A2 repair report. Scope is the block identity
for a prefix diagonal block `fromBlocks C1 0 0 D` multiplied by the next
transformed layer `fromBlocks A1 A2 A3 A4`, under explicit determinant-unit
chart hypotheses for `C1` and `A1`.

Outcome: landed
`DLNFibre.DLN.Aoyagi.productReduction_chartLocalInductionStep_fromBlocks` in
`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`, imported by the single-writer
aggregator. The theorem proves only the chart-local algebraic block identity:
left lower-left multiplier `-(D * A3 * (C1 * A1)⁻¹)`, right upper-right
multiplier `-(A1⁻¹ * A2)`, and residual block
`D * (A4 - A3 * A1⁻¹ * A2)`. It includes an identity-corner example showing
the determinant-unit chart hypotheses are inhabited, including zero-size
corners.

Controller verified targeted build, full `DLNFibre` build, `scripts/sorries`,
and `#print axioms` for the theorem. Xhigh hardener `Jason` and xhigh fidelity
reviewer `Huygens` passed the artifact at this narrow scope. Statement card:
`statement-card-a2-chart-local-induction-step.md`.

Still blocked: full Aoyagi Theorem 3 from source rank/neighborhood hypotheses,
through-layer basis/open-chart existence, target-product normalization via
Aoyagi Lemma 1, local analytic/ideal-germ invariance, regular-coordinate RLCT
additivity, and every final RLCT consequence.

## 2026-06-18 A2 matrix-entry ideal tide

After the analytic-interface repair, opened the next elementary transport
target: matrix-entry ideal algebra for the post-Theorem-3 block generators.
Scope is algebraic ideals over a commutative ring only. Explicitly out of
scope: analytic germs, local coordinate invariance, normal-crossing
certificates, RLCT equality, and pole-order consequences.

Outcome: landed `lean/DLNFibre/DLN/Aoyagi/EntryIdeal.lean`, imported by the
single-writer aggregator. Main theorems:

- `matrixEntryIdeal_mul_left_eq_of_isUnit_det`;
- `matrixEntryIdeal_mul_right_eq_of_isUnit_det`;
- `matrixEntryIdeal_mul_le_sup`;
- `fourMatrixEntryIdeal_sub_mul_eq`.

The last theorem proves the elementary cleanup

```text
<entries X, entries F2, entries F3, entries (D - F3 F2)>
  = <entries X, entries F2, entries F3, entries D>.
```

The file includes identity-multiplier examples witnessing the determinant-unit
hypotheses. Controller verified targeted build, full `DLNFibre` build,
`scripts/sorries`, and `#print axioms` for the main theorems. Xhigh fidelity
reviewer `Dalton` and xhigh hardener `Linnaeus` passed the artifact at the
elementary algebraic scope. Statement card: `statement-card-a2-entry-ideal.md`.

Still blocked: the same algebraic ideal does not by itself imply the same RLCT.
The final route must construct or transport a normal-crossing certificate before
using the single extraction citation.

## 2026-06-18 A2 through-layer basis reproduction

Opened xhigh pen-and-paper scout `Gibbs` to reproduce the missing
through-layer basis/open-chart lemma, then xhigh checker `Hooke` to audit it.
Report saved at `through-layer-basis-reproduction.md`.

Verdict: product rank `r` is enough to choose bases existentially so the true
layer maps have block form `[I B; 0 D]` and the Aoyagi induction charts contain
the base point. Product rank is not enough for a preselected fixed chart; the
report records counterexamples. This is an auxiliary elementary
linear-algebra repair, not a source-stated Aoyagi lemma and not an analytic
claim.

Lean-ready now: the field-linear through-subspace existence lemma, and the
local unitriangular chart-stability block calculation. Full Theorem 3 remains
blocked until this basis lemma is formalised and connected to the already
landed chart-local induction identity.

Outcome for the local calculation: landed
`DLNFibre.DLN.Aoyagi.upperUnitriangular_mul_fromBlocks_one_zero` in
`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`. It proves

```text
[I -F; 0 I] [I B; 0 D] = [I B - F D; 0 D].
```

Controller verified targeted build, full `DLNFibre` build, `scripts/sorries`,
and `#print axioms`. Statement card:
`statement-card-a2-unitriangular-chart.md`.

## 2026-06-19 A2 through-subspace Lean layer

Landed the elementary through-subspace theorem in
`lean/DLNFibre/DLN/Aoyagi/ThroughLayerBasis.lean`.

Main Lean artifacts:

- `chainMap`, `chainMap_succ`, `chainMap_trans`: source-to-target composites
  for an upward finite chain `A i : V i.castSucc -> V i.succ`.
- `exists_chain_throughSubspaces`: chooses `U0` complementary to the total
  kernel and defines through-subspaces `U j` as prefix images; proves edge
  transport, suffix-kernel disjointness, constant finrank equal to the total
  range finrank, and `U last = range total`.
- `throughSubspaceEdgeEquiv` and `throughSubspaceEdgeEquiv_apply`: each edge
  restricts to a linear equivalence between adjacent through-subspaces, induced
  by the original edge map.

Orientation note: this Lean chain runs from `V 0` to `V (Fin.last N)`. It is
Aoyagi's chain after reversing the paper-order maps
`A^(s) : V_(s+1) -> V_s`.

Xhigh reviewers `Nietzsche` and `Pascal` accepted the statement scope. Caveats:
this is not a fixed-coordinate chart theorem, does not choose complements to
the through-subspaces, and does not itself produce basis matrices. The next
target is the complement/direct-sum and chain-level matrix packaging needed to
connect this subspace layer to the already-proved chart-local product reduction
identity.

Statement card: `statement-card-a2-through-subspaces.md`.

## 2026-06-19 A2 through-matrix block Lean layer

Landed the per-edge transported-basis matrix block theorem in
`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`, imported by the single-writer
aggregator.

Main Lean artifacts:

- `exists_toMatrix_sumQuot_eq_fromBlocks_one_zero`: for a linear map `f : E -> F`
  whose restriction to `U` is a specified equivalence `U ≃ U'`, transported
  `Module.Basis.sumQuot` bases put the matrix of `f` in block form
  `fromBlocks 1 B 0 D`.
- `exists_toMatrix_throughSubspaceEdge_eq_fromBlocks_one_zero`:
  specialization to an edge `A p : V p.castSucc -> V p.succ` using
  `throughSubspaceEdgeEquiv`.
- `basisOfIsCompl`: builds an ambient basis from bases of complementary
  subspaces using `Submodule.prodEquivOfIsCompl`.
- `exists_toMatrix_basisOfIsCompl_eq_fromBlocks_one_zero`: generic direct-sum
  adapted-basis block theorem.
- `exists_toMatrix_throughSubspaceEdge_basisOfIsCompl_eq_fromBlocks_one_zero`:
  through-edge specialization in supplied complement/direct-sum bases.

This checkpoint proves basis-coordinate bookkeeping only: transported
through-subspace bases give the identity top-left block, and subspace
membership gives the zero lower-left block. Quotient bases, complements, and
complement bases are explicit inputs. It is not a fixed-coordinate chart
theorem, does not package simultaneous chain bases, and does not prove Aoyagi
Theorem 3 or any analytic/RLCT consequence.

Statement card: `statement-card-a2-through-matrix-block.md`.

## 2026-06-19 A2 endpoint total-product block

Extended `lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean` with the endpoint
normalization theorem for the whole chain.

Main Lean artifacts:

- `toMatrix_basisOfIsCompl_eq_fromBlocks_one_zero_zero_of_map_complement_eq_zero`:
  generic direct-sum theorem saying that if the source complement maps to zero,
  the matrix is `fromBlocks 1 0 0 0` in transported direct-sum bases.
- `toMatrix_chainMap_zero_last_ker_basisOfIsCompl_eq_fromBlocks_one_zero_zero`:
  specialization to the total composite `chainMap V A 0 (Fin.last N) ...`,
  with source decomposition `U₀ ⊕ ker P` and target decomposition
  `throughSubspace last ⊕ Wlast`.

This proves only endpoint matrix normalization. It does not package one
simultaneous family of bases at every intermediate layer, does not translate
orientation back to Aoyagi paper order, and does not yet connect the endpoint
and per-edge block forms to the chart-local product-reduction identity.

Statement card: `statement-card-a2-total-product-block.md`.

## 2026-06-19 A2 prefix-compatible edge bases

Extended `lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean` with the prefix
transport package:

- `disjoint_ker_chainMap_prefix_of_disjoint_ker_total`: a subspace disjoint
  from the total kernel is disjoint from every prefix kernel.
- `throughSubspacePrefixEquiv` and `throughSubspacePrefixEquiv_apply`:
  transport from the initial through-subspace `U₀` to `throughSubspace ... j`
  by the prefix chain map.
- `throughSubspacePrefixEquiv_succ_apply`: adjacent prefix transports are
  related by the edge map.
- `exists_toMatrix_throughSubspaceEdge_prefix_basisOfIsCompl_eq_fromBlocks_one_zero`:
  a through-layer edge has matrix form `fromBlocks 1 B 0 D` when the top bases
  at both endpoints are obtained by transporting one common initial basis of
  `U₀`.

This proves compatibility of the top/through bases across layers. It still
takes local complements and complement bases as inputs for the source and target
of a single edge. It does not yet bundle complement data across all layers, run
the chart-local product-reduction induction, or state any analytic/RLCT
consequence.

## 2026-06-19 A2 unitriangular chart-form corollary

Extended `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean` with
`exists_fromBlocks_one_zero_of_upperUnitriangular_mul`. The theorem packages the
already-proved identity

```text
[I -F; 0 I] [I B; 0 D] = [I B - F D; 0 D]
```

as an existential chart-form preservation statement: if a matrix has some
identity-corner, zero-lower-left block form, then the upper-unitriangular left
multiplier leaves it in some such form.

This is still pure block algebra over a commutative ring. It does not run the
product-reduction induction, choose the complement data supplied to the
through-layer matrix theorems, or state analytic/RLCT consequences.

## 2026-06-19 A2 supplied chart-data bundle

Extended the matrix/chart layer with indexed and bundled forms:

- `upperUnitriangular_mul_fromBlocks_one_zero_indexed` and
  `exists_fromBlocks_one_zero_of_upperUnitriangular_mul_indexed` generalize the
  unitriangular chart-form lemmas from `Fin` dimensions to arbitrary finite
  basis index types.
- `ThroughSubspaceChartData` bundles, for every layer, a complement to the
  through-subspace and a basis of that complement, together with one initial
  through-basis.
- `exists_toMatrix_throughSubspaceEdge_chartData_eq_fromBlocks_one_zero`
  restates the prefix-compatible edge block theorem using the bundled data.
- `exists_unitriangular_toMatrix_throughSubspaceEdge_chartData_eq_fromBlocks_one_zero`
  combines the bundled edge matrix form with the indexed unitriangular
  chart-preservation lemma.

This is still a supplied-data theorem. It does not itself construct finite
indexed complement data, does not run the product-reduction induction, and does
not state analytic/RLCT consequences.

## 2026-06-19 A2 finite chart-data existence

Extended `lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean` with the
finite-dimensional existence layer:

- `throughSubspaceComplement` and `throughSubspace_isCompl_complement` choose
  and verify a complement to each transported through-subspace.
- `throughSubspaceComplementIndex` indexes each chosen complement by
  `Fin (Module.finrank K ...)`.
- `throughSubspaceChartDataOfFiniteDimensional` constructs concrete
  finite-indexed chart data for any chosen initial through-subspace `U₀`, using
  `Module.finBasis` for the initial subspace and complements.
- `exists_isCompl_ker_throughSubspaceChartDataOfFiniteDimensional`
  additionally chooses `U₀` complementary to the total kernel and preserves the
  earlier `finrank U₀ = finrank range P` equality.

This proves the elementary finite-dimensional supplied-data construction needed
by the through-basis repair. It does not prove Aoyagi's fixed-coordinate chart
claim, the paper-order rank/open-neighborhood bridge, the product-reduction
induction, or any analytic/RLCT consequence.

## 2026-06-19 A2 concrete finite-basis block corollaries

Added concrete finite-dimensional wrappers around the supplied-data block
theorems:

- `exists_toMatrix_throughSubspaceEdge_finiteDimensional_eq_fromBlocks_one_zero`
  instantiates the per-edge `[I B; 0 D]` theorem with the chosen complements
  and `Module.finBasis` bases from `throughSubspaceChartDataOfFiniteDimensional`.
- `exists_unitriangular_toMatrix_throughSubspaceEdge_finiteDimensional_eq_fromBlocks_one_zero`
  instantiates the unitriangular chart-preservation theorem with the same
  concrete finite indices.
- `toMatrix_chainMap_zero_last_ker_finiteDimensional_eq_fromBlocks_one_zero_zero`
  instantiates the endpoint `[I 0; 0 0]` theorem using `Module.finBasis` for
  `U₀`, `ker P`, and the chosen target complement.

These are still adapted-coordinate statements. They do not identify Aoyagi's
paper-order top-left coordinate blocks, prove rank-open neighborhoods, run the
induction, or state analytic/RLCT consequences.

## 2026-06-19 A2 paper-order bridge notes

Added `paper-order-bridge-notes.md` recording the source-to-Lean direction
reversal:

```text
V_j = W_(L+1-j),    Lean edge j = paper layer s = L-j.
```

The note identifies the next elementary bridge obligations: a reindexing lemma,
a finite chart-data-to-paper-block wrapper, a determinant-open chart statement,
the paper-order induction assembly, and optional rank corollaries. It also
records nonclaims: this does not prove Theorem 3, does not make the Lemma 1
normalization elementary, and does not justify the post-Theorem-3 RLCT shift.

## 2026-06-19 A2 paper-order chain composite

Extended `lean/DLNFibre/DLN/Aoyagi/ThroughLayerBasis.lean` with
`paperChainMap`, a descending composite for Aoyagi-order maps
`B p : W p.succ -> W p.castSucc`.

The proved API is:

- `paperChainMap_self`: the empty paper-order composite is the identity.
- `paperChainMap_succ`: extending the upper endpoint composes the new paper
  edge on the right.
- `paperChainMap_edge`: a one-edge paper-order composite is the edge itself.
- `paperChainMap_trans`: the composite splits at an intermediate vertex as
  prefix composed with suffix.
- `paperChainMap_zero_last_eq_prefix_comp_suffix`: the full product splits as
  paper prefix followed by paper suffix.

This is only product-order bookkeeping. It does not transfer adapted block
forms to paper notation, run the product-reduction induction, or state
analytic/RLCT consequences.

## 2026-06-19 A2 reversed-chain bridge

Extended `lean/DLNFibre/DLN/Aoyagi/ThroughLayerBasis.lean` with the formal
source-to-paper orientation bridge:

- `rev_succ_eq_rev_castSucc`, `rev_castSucc_eq_rev_succ`, and
  `rev_succ_le_rev_castSucc`: the `Fin.rev` endpoint bookkeeping for a reversed
  edge.
- `reverseVertex`: the paper-order vertex family viewed in source-to-target
  order.
- `reverseEdge`: the one-edge paper-order composite viewed as a
  source-to-target edge.
- `chainMap_reverse_eq_paper`: the composite `chainMap` on reversed vertices is
  exactly the corresponding `paperChainMap`.

This removes the orientation mismatch between the Lean through-subspace chain
and Aoyagi's printed product order. It still does not transfer the finite
adapted-basis block corollaries into paper notation, prove determinant-open
chart wrappers, run the product-reduction induction, or state analytic/RLCT
consequences.

## 2026-06-19 A2 paper-order finite matrix blocks

Extended `lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean` with finite
paper-order matrix wrappers:

- `disjoint_ker_reverse_total_of_disjoint_ker_paperChainMap`: converts a
  disjointness hypothesis for the paper-order total product into the reversed
  source-to-target total-kernel hypothesis, using `chainMap_reverse_eq_paper`.
- `isCompl_ker_reverse_total_of_isCompl_ker_paperChainMap`: the matching
  complement-hypothesis bridge.
- `exists_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero`:
  instantiates the concrete finite edge block theorem on `reverseVertex W` and
  `reverseEdge W B`.
- `exists_unitriangular_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero`:
  gives the corresponding unitriangular chart-form preservation wrapper.
- `toMatrix_paperChainMap_ker_finiteDimensional_eq_fromBlocks_one_zero_zero`:
  gives the endpoint `[I 0; 0 0]` form for the total paper product.

This transfers the finite adapted-basis edge and endpoint statements into the
paper-order orientation. It still does not provide determinant/open chart
wrappers, the product-reduction induction, or analytic/RLCT consequences.

## 2026-06-20 A2 triangular endpoint multiplier wrapper

Returned to A2 to expose the triangular multipliers appearing explicitly in
Aoyagi Theorem 3.  Pen-and-paper reproduction saved at
`reproduction-a2-triangular-block-diagonal.md`; statement card saved at
`statement-card-a2-triangular-block-diagonal.md`.

Lean changes:

- `lowerUnitriangular_mul_fromBlocks_one_zero_indexed` proves
  `[I 0; F I] [I 0; G I] = [I 0; F + G I]`.
- `ChartLocalSuffixState.step_L_eq_lowerUnitriangular` and
  `ChartLocalSuffixState.suffixState_L_eq_lowerUnitriangular` prove the
  deterministic suffix state's accumulated left multiplier has shape
  `[I 0; F3 I]`.
- `ChartLocalSuffixState.suffixState_blockDiagonal_exists_triangularBlockDiagonal`
  and `productReduction_chartLocal_suffixChain_triangularBlockDiagonal_indexed`
  restate the abstract block-diagonal invariant with regular triangular
  multipliers.
- `PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal`
  extracts fixed-endpoint Aoyagi-style multipliers from the existing
  source-facing certificate, with right multiplier `F2 = -S.B`.

This is still elementary finite block algebra and certificate repackaging.  It
does not prove chart coverage, exact-rank openness, Aoyagi Lemma 1, analytic
ideal transport, regular-coordinate RLCT additivity, normal crossings, or an
RLCT consequence.

## 2026-06-19 A2 indexed block algebra

Extended the pure block algebra layer with indexed variants:

- `schurComplement_leftBlockElim_fromBlocks_indexed`;
- `schurComplement_blockElim_fromBlocks_indexed`;
- `productReduction_chartLocalInductionStep_fromBlocks_indexed`.

These are the same identities as the existing `Fin`-indexed A1/A2 block
theorems, but stated for arbitrary finite block index types. This is
infrastructure for chart-data assembly only; it does not prove the
product-reduction induction or any analytic consequence.

## 2026-06-19 A2 determinant chart predicates

Added a non-topological determinant-chart predicate layer:

- `topLeftCorner`;
- `identityCornerForm`;
- `identityCornerDetChart`;
- `topLeftCorner_eq_one_of_identityCornerForm`;
- `identityCornerDetChart_of_identityCornerForm`;
- `identityCornerForm_upperUnitriangular_mul`.

Then named the adapted paper edge matrix as `paperAdaptedReverseEdgeMatrix` and
the corresponding upper-unitriangular multiplier as `paperUnitriangularLeft`.
Theorems now state that the adapted paper edge matrix has identity-corner form,
selected top-left corner `1`, and determinant-chart membership; the
unitriangularly transformed matrix also has identity-corner form and
determinant-chart membership.

This is algebraic `IsUnit` at the adapted base matrix. It is not a topological
open-neighborhood theorem, not a fixed-coordinate chart theorem, and not a
rank or RLCT statement.

## 2026-06-19 A2 one-edge right elimination

Added the explicit indexed algebraic theorem
`productReduction_blockDiagonal_mul_fromBlocks_one_zero_rightElim_indexed`:

- a block-diagonal prefix `fromBlocks C1 0 0 Dprev`;
- followed by the witnessed identity-corner edge `fromBlocks 1 B 0 Dnext`;
- followed by a right unitriangular source-side multiplier
  `fromBlocks 1 (-B) 0 1`;
- equals a new block-diagonal prefix `fromBlocks C1 0 0 (Dprev * Dnext)`.

Also added the equality corollary
`productReduction_blockDiagonal_mul_eq_fromBlocks_one_zero_rightElim_indexed`
and the convenience wrapper
`productReduction_blockDiagonal_mul_identityCornerForm_rightElim`, which
packages the witness through `identityCornerForm`.

No determinant-unit hypothesis is needed in this identity because the next edge
has top-left corner exactly `1`; no inverse or Schur complement is used.

Added the paper-order corollary
`productReduction_paperAdaptedReverseEdgeMatrix_rightElim`. For
`paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p`, rows are indexed by
`Fin (finrank U₀) ⊕ κ p.succ` and columns by
`Fin (finrank U₀) ⊕ κ p.castSucc`, where
`κ j = throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j`.
Thus `Dprev` has columns `κ p.succ`, `Dnext` has rows `κ p.succ` and columns
`κ p.castSucc`, and the right multiplier's lower identity is on `κ p.castSucc`.

This is still one-edge algebra. Full product assembly remains blocked on a
shared adapted basis family whose endpoint source complement is the total
kernel; the current concrete finite edge wrappers use automatically chosen
complements at every vertex, while the endpoint total-product theorem uses
`ker P` as the source complement.

## 2026-06-19 A2 endpoint-compatible chart data

Added a named shared adapted basis family:

- `throughSubspaceAdaptedBasis`.

Using that basis family:

- `exists_toMatrix_throughSubspaceEdge_adaptedBasis_eq_fromBlocks_one_zero`
  restates the edge `[I B; 0 D]` theorem with the named basis at adjacent
  vertices.
- `toMatrix_chainMap_zero_last_chartData_eq_fromBlocks_one_zero_zero_of_maps_complement_to_zero`
  states the endpoint `[I 0; 0 0]` theorem for any supplied chart data whose
  source complement maps to zero under the total product.

Then added endpoint-compatible finite chart data:

- `throughSubspaceEndpointComplement`: source complement is the total kernel,
  other complements are chosen arbitrarily;
- `throughSubspaceEndpointComplementIndex`;
- `throughSubspaceEndpointChartDataOfFiniteDimensional`;
- `exists_isCompl_ker_throughSubspaceEndpointChartDataOfFiniteDimensional`;
- `toMatrix_chainMap_zero_last_endpointChartData_eq_fromBlocks_one_zero_zero`;
- `endpointChartData_edge_and_totalProduct_blocks`.

Finally added paper-order wrappers:

- `exists_isCompl_ker_paperEndpointChartDataOfFiniteDimensional`;
- `paperEndpointChartData_edge_and_totalProduct_blocks`.

This removes the previous endpoint-basis mismatch: one edge matrix and the
total product matrix can now be stated in the same endpoint-compatible adapted
basis family, including in paper order. It still does not prove that the
ordered product of all edge matrices equals the endpoint total matrix in this
basis family, and it does not run the product-reduction induction.

## 2026-06-19 A2 adapted matrix composition

Added generic supplied-data matrix names:

- `throughSubspaceAdaptedChainMapMatrix`;
- `throughSubspaceAdaptedEdgeMatrix`.

Added the one-step composition theorem
`throughSubspaceAdaptedChainMapMatrix_succ`. For `i ≤ p.castSucc`, the matrix
of `chainMap i p.succ` in the supplied adapted bases is

`throughSubspaceAdaptedEdgeMatrix p *
throughSubspaceAdaptedChainMapMatrix i p.castSucc`.

This is the matrix form of `chainMap_succ`, using Mathlib
`LinearMap.toMatrix_comp`. The order is edge-on-the-left and prefix-on-the-right
for the source-to-target Lean chain. This is not yet an all-layer product
theorem and does not use the endpoint-compatible data specifically.

## 2026-06-19 A2 adapted edge-product theorem

Added a dependent recursive product of adapted edge matrices:

- `throughSubspaceAdaptedEdgeProductMatrix`;
- `throughSubspaceAdaptedEdgeProductMatrix_self`;
- `throughSubspaceAdaptedEdgeProductMatrix_succ`.

The recurrence is the same edge-on-left order as the chain-map matrix:

`edge p * edgeProduct i p.castSucc`.

Added `throughSubspaceAdaptedChainMapMatrix_eq_edgeProductMatrix`, proving for
any interval `i ≤ j` that the adapted matrix of `chainMap i j` equals this
dependent edge product. Added prefix/endpoint corollaries:

- `throughSubspaceAdaptedChainMapMatrix_zero_eq_edgeProductMatrix`;
- `toMatrix_chainMap_zero_last_eq_adaptedEdgeProductMatrix`.

This closes the composition-only gap between one-edge adapted matrices and the
endpoint total-product matrix in a supplied adapted basis family. It still does
not run Aoyagi's product-reduction induction or assert any analytic/RLCT
consequence. The next algebraic assembly layer needs right-oriented suffix
composition and canonical block projections for the one-edge elimination step.

## 2026-06-19 A2 right-elimination assembly API

Added deterministic block projections in `ProductReduction.lean`:

- `upperRightBlock`;
- `lowerRightBlock`.

Added deterministic right-elimination wrappers:

- `productReduction_blockDiagonal_mul_identityCornerForm_rightElim_submatrix`;
- `productReduction_blockDiagonal_mul_unitriangular_identityCornerForm_rightElim`.

These turn an `identityCornerForm M` hypothesis into the concrete elimination
identity using `upperRightBlock M` as the right multiplier and
`lowerRightBlock M` as the residual edge block. The unitriangular version first
left-multiplies by `[I -F; 0 I]`, using the already proved chart-form
stability theorem.

Added the suffix-oriented adapted matrix composition theorem
`throughSubspaceAdaptedChainMapMatrix_succ_right` in `ThroughLayerMatrix.lean`:
for `p.succ ≤ j`, the matrix of `chainMap p.castSucc j` is

`throughSubspaceAdaptedChainMapMatrix p.succ j *
throughSubspaceAdaptedEdgeMatrix p`.

This is the direction needed by right-elimination induction. It is still only
composition/block algebra; it does not yet prove the abstract suffix-chain
reduction theorem.

## 2026-06-19 A2 suffix-chain right elimination

Added cancellation and suffix-step algebra in `ProductReduction.lean`:

- `upperUnitriangular_neg_mul_upperUnitriangular`;
- `upperUnitriangular_neg_mul_upperUnitriangular_neg_neg`;
- `productReduction_identityCorner_suffixStep_rightElim`.

The suffix-step theorem proves the induction step: from a reduced suffix
`Ptail * [I -Bprev; 0 I] = [I 0; 0 Dprev]` and an identity-corner edge `E`,
one gets `Ptail * E * [I -B; 0 I] = [I 0; 0 D]` for suitable `B, D`.

Added the abstract chain theorem
`productReduction_identityCorner_suffixChain_rightElim`. It assumes:

- identity empty segments;
- suffix composition `P p.castSucc j = P p.succ j * E p`;
- identity-corner form for every edge `E p`;
- proof-irrelevance of `P i j h` in the proof `h : i ≤ j`.

The theorem returns existence of a source-side upper-unitriangular right
multiplier putting `P i j` in block-diagonal form `[I 0; 0 D]`.

Added supplied adapted-basis wrappers in `ThroughLayerMatrix.lean`:

- `throughSubspaceAdaptedChainMapMatrix_proof_irrel`;
- `throughSubspaceAdaptedChainMapMatrix_self`;
- `identityCornerForm_throughSubspaceAdaptedEdgeMatrix`;
- `productReduction_throughSubspaceAdaptedChainMapMatrix_suffixChain_rightElim`.

This is the first full chain-level product-reduction algebra for supplied
through-subspace adapted bases. It is still not full Aoyagi Theorem 3: no
paper-order endpoint wrapper, rank/open chart bridge, target normalization, or
analytic/RLCT consequence is asserted here.

Xhigh review found no blocking orientation issue. The review confirmed the
unitriangular signs, the backward suffix induction order, and the supplied
adapted-basis wrapper. It flagged the key source-fidelity boundary: this is a
pointwise theorem for an already supplied adapted basis family, with bases
depending on the actual chain. It does not yet provide fixed coordinate charts
over a neighborhood, regular `P1`/`P2`, rank/open-chart hypotheses, endpoint
kernel normalization as a paper-facing statement, or any RLCT/generator
transport.

## 2026-06-19 A2 paper endpoint suffix-chain wrapper

Added
`productReduction_paperChainMap_endpointChartData_suffixChain_rightElim` in
`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`.

The theorem works in Aoyagi paper order for maps `B p : W p.succ -> W
p.castSucc`. It reverses the paper chain via `(reverseVertex W) (reverseEdge W
B)`, uses endpoint-compatible finite chart data from an explicit complement
`IsCompl U0 (ker totalPaperProduct)`, and states that the adapted matrix of the
full `paperChainMap` admits a source-side upper-unitriangular right elimination:

`paperTotalMatrix * [I -Bmat; 0 I] = [I 0; 0 Dmat]`.

The proof is a thin wrapper around
`productReduction_throughSubspaceAdaptedChainMapMatrix_suffixChain_rightElim`
plus `chainMap_reverse_eq_paper`. This closes the paper-order endpoint
packaging gap for the supplied-data algebra. It remains pointwise and
adapted-coordinate only: no fixed coordinate neighborhood, openness/rank chart,
regular coordinate-change, named residual-factor identification, or RLCT
consequence is claimed.

## 2026-06-19 A2 rank/open split

Added rank bridge helpers in
`lean/DLNFibre/DLN/Aoyagi/BlockElimination.lean`:

- `rank_toMatrix_eq_finrank_range`;
- `rank_schurComplement_eq_sub_rank_fromBlocks`.

Added the paper adapted-edge residual-rank corollary in
`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`:

- `lowerRightBlock_paperAdaptedReverseEdgeMatrix_rank_eq_sub`.

It proves that the lower-right residual block of an adapted paper-order edge
has rank

`finrank range(reverseEdge W B p) - finrank U0`.

Added `lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean`, imported by the aggregator.
It proves:

- `isOpen_identityCornerDetChart`;
- `identityCornerDetChart_mem_nhds`;
- `identityCornerForm_mem_nhds_identityCornerDetChart`;
- `paperAdaptedReverseEdgeMatrix_mem_nhds_identityCornerDetChart`;
- `unitriangular_paperAdaptedReverseEdgeMatrix_mem_nhds_identityCornerDetChart`.

This is the first honest topological bridge: determinant nonvanishing defines
an open chart around the adapted base matrices. Exact rank is not claimed to be
open. The current paper adapted bases still depend on the actual chain `B`, so
the remaining source-faithful local theorem needs fixed basepoint chart data
and variable-layer matrices expressed in those fixed bases.

## 2026-06-19 A2 endpoint basepoint certificate

Added `lean/DLNFibre/DLN/Aoyagi/BasepointCertificate.lean` and imported it in
the aggregator. The module names the endpoint-compatible paper-order objects:

- `paperTotalMap`;
- `paperEndpointChartData`;
- `paperEndpointAdaptedEdgeMatrix`;
- `paperEndpointUnitriangularLeft`;
- `paperEndpointAdaptedTotalMatrix`.

It proves the endpoint-specific residual rank bridge
`lowerRightBlock_throughSubspaceEndpointAdaptedEdgeMatrix_rank_eq_sub` and the
paper wrapper `lowerRightBlock_paperEndpointAdaptedEdgeMatrix_rank_eq_sub`.
Unlike the earlier ordinary-complement residual-rank theorem, this version uses
the endpoint chart data whose source complement is the total product kernel.

It also proves endpoint-compatible determinant-chart and block/elimination
wrappers:

- `identityCornerForm_paperEndpointAdaptedEdgeMatrix`;
- `identityCornerDetChart_paperEndpointAdaptedEdgeMatrix`;
- `paperEndpointAdaptedEdgeMatrix_mem_nhds_identityCornerDetChart`;
- `identityCornerDetChart_unitriangular_paperEndpointAdaptedEdgeMatrix`;
- `unitriangular_paperEndpointAdaptedEdgeMatrix_mem_nhds_identityCornerDetChart`;
- `paperEndpointAdaptedTotalMatrix_eq_fromBlocks_one_zero_zero`;
- `productReduction_paperEndpointAdaptedTotalMatrix_suffixChain_rightElim`.

The package theorem `paperEndpointBasepointCertificate_of_isCompl` bundles
these facts for a supplied total-kernel complement, and
`exists_paperEndpointBasepointCertificate` chooses such a complement in finite
dimension. This is the current bedrock A2 basepoint certificate. It remains a
fixed-chain, adapted-coordinate statement: it does not prove a fixed coordinate
family for variable nearby chains, exact rank-stratum openness, regular
coordinate-change transport, normal-crossing extraction, or any RLCT claim.

## 2026-06-19 A2 fixed-basepoint variable chart

Added generic block-corner and Schur-residual API to `ProductReduction.lean`:

- `lowerLeftBlock`;
- `fromBlocks_corners`;
- `schurResidualBlock`;
- `rank_schurResidualBlock_eq_sub_rank_of_identityCornerDetChart`.

The last theorem says that if a block matrix is in the selected determinant
chart, then its Schur residual has rank `rank M - r`. This is the correct
variable-edge rank statement; for a variable chain in fixed basepoint bases,
the raw lower-right block is not the residual unless the variable edge remains
in identity-corner form.

Added `lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean`. It fixes endpoint
bases from a base paper-order chain `B` and represents a variable chain `C` in
those same bases:

- `paperEndpointFixedBaseBasis`;
- `paperEndpointFixedBaseChainMapMatrix`;
- `paperEndpointFixedBaseEdgeMatrix`;
- `paperEndpointFixedBaseTotalMatrix`;
- `paperEndpointFixedBaseChainMapMatrix_succ_right`;
- `paperEndpointFixedBaseTotalMatrix_eq_chainMapMatrix`;
- basepoint equalities for `C = B`;
- `rank_schurResidualBlock_paperEndpointFixedBaseEdgeMatrix_eq_sub`;
- two-edge wrappers
  `paperEndpointFixedBaseTwoEdgeTotalMatrix_eq_edge1_mul_edge0`.

The rank theorem keeps both hypotheses explicit:
`identityCornerDetChart (paperEndpointFixedBaseEdgeMatrix W B C U0 hU0 p)` and
`rank = rho`. No openness of exact rank strata, no automatic chart membership
for nearby chains, and no re-adaptation of bases to `C` is claimed.

Added the first variable-chart suffix step. In `ProductReduction.lean`,
`productReduction_chartLocal_suffixStep_fromBlocks_indexed` abstracts the
one-step induction move: from a reduced suffix

`Lprev * Ptail * Rprev = [Ctop 0; 0 Dprev]`

and a next edge factored as `E = Rprev * M`, if `Ctop` and the selected
top-left block of `M` have unit determinant, explicit left and right
block-triangular multipliers reduce `Ptail * E` to

`[Ctop * topLeft(M) 0; 0 Dprev * schurResidualBlock(M)]`.

In `FixedBasepointChart.lean`,
`paperEndpointFixedBase_chartLocal_suffixStep` instantiates this for fixed-base
variable-chain segment matrices. The wrapper
`rank_paperEndpointFixedBaseEdgeMatrix_eq_finrank_range` identifies fixed-base
matrix rank with the variable edge's source linear-map range rank, and
`rank_schurResidualBlock_paperEndpointFixedBaseEdgeMatrix_eq_range_sub`
states the Schur-residual rank as
`finrank range(reverseEdge W C p) - finrank U0` under the explicit determinant
chart hypothesis.

Added the all-layer explicit-chart induction:

- `productReduction_chartLocal_suffixChain_blockDiagonal_indexed` in
  `ProductReduction.lean`;
- `paperEndpointFixedBaseChainMapMatrix_proof_irrel` and
  `productReduction_paperEndpointFixedBaseChainMapMatrix_chartLocal_blockDiagonal`
  in `FixedBasepointChart.lean`.

The abstract chain theorem mirrors the older identity-corner suffix-chain
induction, but its chart hypothesis is on the transformed edge

`[I Bprev; 0 I] * E p`

at every stage. It returns a left multiplier `L`, a right upper-unitriangular
source multiplier, a determinant-unit top block `Ctop`, and a residual block
`D` such that

`L * P i j * [I -B; 0 I] = [Ctop 0; 0 D]`.

The fixed-base wrapper applies this to variable paper-order chains expressed
in endpoint bases fixed from `B`. It still assumes all transformed-edge
determinant-chart hypotheses explicitly; it does not prove these from
neighborhood membership or exact rank.

## 2026-06-19 A2 fixed-base transformed determinant neighborhood

Extended `ChartTopology.lean` with matrix-space pullback lemmas for the
selected determinant chart:

- `leftMul_identityCornerDetChart_mem_nhds`;
- `fromBlocks_leftMul_identityCornerDetChart_mem_nhds`.

Extended `FixedBasepointChart.lean` with
`paperEndpointFixedBaseEdgeMatrix_selfBase_mem_nhds_transformed_identityCornerDetChart`.
For each fixed edge `p` and fixed accumulated upper block `Bprev`, the set of
matrices `M` such that `[I Bprev; 0 I] * M` lies in the selected determinant
chart is an ambient matrix-space neighborhood of the base fixed-base edge
matrix at `C = B`. The proof uses the endpoint unitriangular basepoint
certificate with parameter `-Bprev`, then pulls back the open determinant chart
along fixed left multiplication.

This closes the matrix-local determinant-neighborhood package needed by the
explicit-chart induction. It still does not prove a chain-neighborhood theorem:
there is no formal topology on the variable paper-order chain space here and
no continuity theorem for
`C ↦ paperEndpointFixedBaseEdgeMatrix W B C U0 hU0 p`. Exact rank remains an
explicit hypothesis, not an ambient-open condition.

## 2026-06-19 A2 single-edge topology pullback

Extended `ChartTopology.lean` with
`continuous_linearMap_toMatrix`: for fixed source and target bases, the map
from a continuous linear map to its coordinate matrix is continuous. The proof
is coordinatewise: evaluate the continuous linear map at a fixed source-basis
vector, then take a fixed coordinate in the target basis.

Extended `FixedBasepointChart.lean` with
`paperEndpointFixedBaseContinuousEdge_selfBase_mem_nhds_transformed_identityCornerDetChart`.
For each fixed edge `p` and fixed accumulated upper block `Bprev`, the
transformed determinant-chart predicate pulls back to a neighborhood of the
base edge `reverseEdge W B p` in the `ContinuousLinearMap` topology.

This is the first honest topology pullback beyond ambient matrix space. It is
still one edge only. It does not define a topology on the whole dependent
paper-order chain, does not assemble finite intersections over all edges, does
not handle continuity of the induction-produced `Bprev`, and does not make
exact rank strata open.

## 2026-06-19 A2 fixed-Bprev edge-family topology assembly

Extended `FixedBasepointChart.lean` with
`paperEndpointFixedBaseContinuousEdges_selfBase_mem_nhds_transformed_identityCornerDetChart`.
For a prescribed family of accumulated upper blocks `Bprev p`, the set of
continuous reversed-edge families `Cedge` such that every fixed-basis coordinate
matrix satisfies

`identityCornerDetChart ([I Bprev p; 0 I] * M(Cedge p))`

is a neighborhood of the base edge family

`fun p => LinearMap.toContinuousLinearMap (reverseEdge W B p)`

in the finite Pi/product topology. The proof is the finite intersection of the
single-edge neighborhoods, pulled back along the coordinate projections
`continuous_apply p`.

This closes the finite-intersection part of the topology bridge for fixed chart
data. It still does not control a neighborhood simultaneously for all possible
`Bprev`, does not prove continuity or local boundedness of the `Bprev` produced
by the suffix-chain induction, does not handle exact rank strata, and does not
prove Aoyagi Theorem 3.

## 2026-06-19 A2 variable-Bprev topology handoff

Extended `FixedBasepointChart.lean` with
`paperEndpointFixedBaseContinuousEdges_variableBprev_mem_nhds_transformed_identityCornerDetChart`.
For an arbitrary topological parameter space, if the continuous reversed-edge
family `Cedge x` and the accumulated-upper-block family `Bprev x` are
continuous at `x0`, and if every transformed determinant chart holds at `x0`,
then all those chart predicates hold on a neighborhood of `x0`.

This is the reusable topological handoff for variable chart data. It does not
construct the `Bprev` family produced by the suffix-chain induction.

Pen-and-paper recurrence check for that still-open construction:

- write `U_+(B) = [I B; 0 I]` and `U_-(B) = [I -B; 0 I]`;
- the induction hypothesis has
  `Lprev * Ptail * U_-(Bprev) = [Cprev 0; 0 Dprev]`;
- insert `E = U_-(Bprev) * (U_+(Bprev) * E)` and set
  `M = U_+(Bprev) * E`;
- the next right-elimination block is
  `(topLeftCorner M)⁻¹ * upperRightBlock M`.

The next Lean target is a deterministic recursive suffix-chain reduction using
this update under recursive determinant-chart hypotheses, followed by a
continuity theorem for that recursive data. Exact rank assumptions remain
separate.

## 2026-06-19 A2 deterministic suffix-state step

Extended `ProductReduction.lean` with a deterministic one-step state layer:

- `ChartLocalSuffixState`;
- `ChartLocalSuffixState.BlockDiagonal`;
- `ChartLocalSuffixState.transformedEdge`;
- `ChartLocalSuffixState.step`;
- `ChartLocalSuffixState.step_blockDiagonal`.

The state records the left multiplier `L`, right-elimination block `B`, top
block `Ctop`, and residual block `D`. The transformed edge is

`M = [I B; 0 I] * E p`,

and the deterministic step sets

`Bnext = (topLeftCorner M)⁻¹ * upperRightBlock M`.

The theorem `step_blockDiagonal` proves that this one-step update preserves the
block-diagonal invariant, assuming the previous suffix state satisfies the
invariant and the transformed edge lies in the determinant chart. This is the
algebraic one-step recurrence hidden inside the older existential suffix-chain
proof.

Still open: define the full recursive state from endpoint `j` down to `i`,
prove its block-diagonal invariant by iterating this step, and then prove
continuity of that recursive state on a chart neighborhood. Exact rank
assumptions remain separate.

## 2026-06-19 A2 deterministic recursive suffix state

Extended the deterministic suffix-state layer from one step to the full
recursive chart-local chain:

- `ChartLocalSuffixState.terminal`;
- `ChartLocalSuffixState.suffixState`;
- `ChartLocalSuffixState.suffixState_self`;
- `ChartLocalSuffixState.terminal_blockDiagonal`;
- `ChartLocalSuffixState.suffixState_castSucc`;
- `ChartLocalSuffixState.suffixState_blockDiagonal`.

The definition uses `Nat.decreasingInduction` on the lower endpoint `m ≤ j.val`
and keeps the dependent `Fin` casts local to `ProductReduction.lean`.
`suffixState E j i hij` is the deterministic state obtained by starting from
the terminal state at `j` and repeatedly applying
`ChartLocalSuffixState.step` down to `i`. The theorem
`suffixState_blockDiagonal` proves the full recursive block-diagonal invariant
under determinant-chart hypotheses for the actual transformed edges

`ChartLocalSuffixState.transformedEdge E p (suffixState E j p.succ hpj)`.

The older public existential theorem
`productReduction_chartLocal_suffixChain_blockDiagonal_indexed` is now a
wrapper extracting `L`, `B`, `Ctop`, and `D` from `suffixState`, rather than a
separate duplicate induction.

Still open: continuity of the recursively produced `suffixState` fields,
source-faithful neighborhoods where the recursive transformed-edge charts hold,
certificate transport, and the full source Theorem 3 statement. Exact rank
assumptions remain separate.

## 2026-06-19 A2 recursive-Bprev topology handoff

Extended the topology layer from supplied `Bprev` families to the actual
deterministic accumulated upper blocks produced by `suffixState`.

In `ChartTopology.lean`:

- `continuousAt_matrix_inv_of_isUnit_det`;
- `continuousAt_chartLocalSuffixState_step_B`;
- `continuousAt_chartLocalSuffixState_suffixState_B`.

The one-step continuity theorem proves that the updated block

`Bnext = (topLeftCorner M)⁻¹ * upperRightBlock M`

varies continuously with the edge and previous accumulated upper block, assuming
the transformed edge is in the determinant chart at the base point. The
recursive theorem iterates this along `suffixState`, proving continuity of the
`B` field at every lower endpoint under the recursive basepoint chart
hypotheses.

In `FixedBasepointChart.lean`,
`paperEndpointFixedBaseContinuousEdges_recursiveBprev_mem_nhds_transformed_identityCornerDetChart`
feeds the recursively produced `Bprev` family into the existing
variable-`Bprev` handoff. The result is a fixed-base neighborhood on which all
recursive transformed-edge determinant charts persist, assuming those charts
hold at the base parameter.

Still open: exact-rank neighborhoods, certificate transport, the full
source-facing Theorem 3 statement, and continuity of `L`, `Ctop`, and `D` if a
later certificate needs those fields. Exact rank assumptions remain separate.

## 2026-06-19 A2 endpoint block-diagonal neighborhood

Extended `FixedBasepointChart.lean` from chart persistence to the endpoint
block form controlled by the same recursive suffix state.

New fixed-base reversed-edge coordinate API:

- `paperEndpointFixedBaseChainMapMatrixOfReverseEdges`;
- `paperEndpointFixedBaseEdgeMatrixOfReverseEdges`;
- `paperEndpointFixedBaseTotalMatrixOfReverseEdges`;
- composition and identity lemmas for these matrices.

The pointwise theorem
`paperEndpointFixedBaseChainMapMatrixOfReverseEdges_recursiveChart_blockDiagonal`
specializes `ChartLocalSuffixState.suffixState_blockDiagonal` to the endpoint
`0 ≤ Fin.last N`. It uses only the determinant charts for the actual recursive
states `suffixState E (Fin.last N) p.succ _`, not the stronger all-`Bprev`
hypothesis in the older public fixed-base wrapper.

The topology-level predicate
`paperEndpointFixedBaseContinuousEdgesRecursiveBlockDiagonal` names the
deterministic endpoint block form for a continuous reversed-edge family. The
neighborhood theorems
`paperEndpointFixedBaseContinuousEdges_recursiveBprev_blockDiagonal_mem_nhds`
and
`paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_blockDiagonal_mem_nhds`
combine recursive chart persistence with the pointwise block theorem. At a base
family equal to `reverseEdge W B`, the recursive basepoint chart hypotheses are
proved by the unitriangular endpoint identity-corner theorem with `F = -Bprev`.

Still open: exact-rank neighborhoods, certificate transport, a source-facing
Theorem 3 statement, and any continuity of `L`, `Ctop`, or `D` if future
certificate data needs them.

## 2026-06-19 A2 adapted residual rank API

Added a minimal API for the residual blocks visited by the deterministic suffix
state. In `ProductReduction.lean`:

- `ChartLocalSuffixState.residualBlock`;
- `ChartLocalSuffixState.suffixState_D_self`;
- `ChartLocalSuffixState.suffixState_D_castSucc`.

The recurrence is intentionally adapted:

`S_next.D = S_tail.D * schurResidualBlock ([I S_tail.B; 0 I] * E p)`.

This names the lower-right block product in the block-diagonalized endpoint
matrix without claiming it is a raw product of the original edge residuals.

In `FixedBasepointChart.lean`, added the reversed-edge rank bridge
`rank_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_eq_finrank_range` and
pointwise transformed residual-rank wrappers, including
`rank_transformedEdge_fixedBaseReverseEdges_eq_range_sub`.
These results assume determinant-chart membership and exact edge rank at the
point. They do not assert exact-rank openness or any neighborhood of exact-rank
conditions.

Then added the first source-facing rank/certificate boundary theorem:

- `paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts`;
- `paperEndpointFixedBaseContinuousEdgesRecursiveResidualRankImplications`;
- `paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_blockDiagonal_rankImp_mem_nhds`.

This theorem gives one neighborhood on which recursive determinant charts and
endpoint block form hold, and on which every residual rank conclusion is
available as an implication from an exact pointwise edge-rank hypothesis. It
does not place exact-rank hypotheses inside the neighborhood conclusion.

## 2026-06-19 A2 product-reduction boundary certificate

Landed `lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`, imported by the
single-writer aggregator.

Main Lean artifacts:

- `PaperEndpointFixedBaseProductReductionCertificate`: a Prop-valued package
  for the fixed-base recursive determinant charts, endpoint block form, and
  residual-rank implications.
- `paperEndpointFixedBaseProductReductionCertificate_of_recursiveDetCharts`:
  a pointwise constructor from recursive determinant charts, reusing the
  deterministic endpoint block theorem and transformed residual-rank bridge.
- `paperEndpointFixedBaseProductReductionCertificate_selfBase_mem_nhds`: the
  neighborhood theorem for a continuous reversed-edge family based at
  `reverseEdge W B`.
- `PaperEndpointFixedBaseProductReductionLocalCertificate` and
  `paperEndpointFixedBaseProductReductionLocalCertificate_of_isCompl`: the
  fixed-base local package carrying both the basepoint certificate and the
  product-reduction certificate neighborhood.
- `PaperEndpointProductReductionLocalCertificate` and
  `exists_paperEndpointProductReductionLocalCertificate`: the existential local
  package choosing a total-kernel complement.

This checkpoint packages the current source-facing elementary/topological
boundary. It does not prove exact-rank openness, analytic ideal-germ transport,
regular-suspension/RLCT additivity, normal-crossing extraction, or the full
printed triangular product-reduction theorem from Aoyagi's source hypotheses.
The post-Theorem-3 RLCT transport remains a separate deferred problem. Xhigh
scouts `Herschel` and `Ohm` independently recommended this boundary shape,
with the same non-claims. Controller verified targeted build, full `DLNFibre`
build, `scripts/sorries`, `git diff --check`, and axiom spot checks for the
public theorems. Statement card:
`statement-card-a2-product-reduction-boundary-certificate.md`.

## 2026-06-21 A2 residual-product endpoint wrapper

Returned to the Theorem 3 endpoint form to name the lower-right residual
product explicitly. Aoyagi's induction updates the lower-right block by
multiplying the previous residual product by the Schur residual of the next
transformed layer. The Lean suffix state already had this recurrence for `D`;
this checkpoint gives the recurrence a named product.

New Lean artifacts in `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`:

- `ChartLocalSuffixState.residualProduct`;
- `ChartLocalSuffixState.residualProduct_self`;
- `ChartLocalSuffixState.residualProduct_castSucc`;
- `ChartLocalSuffixState.suffixState_D_eq_residualProduct`;
- `ChartLocalSuffixState.suffixState_blockDiagonal_exists_triangularBlockDiagonal_residualProduct`;
- `productReduction_chartLocal_suffixChain_triangularBlockDiagonal_residualProduct_indexed`.

New endpoint wrapper in
`lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`:

- `PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal_residualProduct`.

The product is explicitly the deterministic product of transformed Schur
residuals visited by `suffixState`, not a raw product of original lower-right
edge blocks. The abstract suffix-chain wrapper still keeps the older
all-`Bprev` determinant-chart hypothesis; that is stronger than needed for the
proof but explicit in the statement.

Still open: weakening the abstract chart hypothesis, chart coverage from
source rank hypotheses, exact-rank openness, Aoyagi Lemma 1, analytic
ideal-germ transport, regular-coordinate RLCT bookkeeping, normal-crossing
extraction, and every RLCT consequence.

Artifacts:
`reproduction-a2-residual-product.md`,
`statement-card-a2-residual-product.md`, and
`review-a2-residual-product.md`.

## 2026-06-22 A2 rank-stratum boundary

Returned to the exact-rank side of Aoyagi Theorem 3.  The previous fixed-base
certificate kept residual-rank conclusions as implications from exact layer
ranks.  This checkpoint packages the intended restriction explicitly rather
than treating exact-rank strata as open.

New Lean artifacts in `lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`:

- `paperEndpointFixedBaseEdgeRankStratum`;
- `paperEndpointFixedBaseSourceRankStratum`;
- `paperEndpointFixedBaseContinuousEdgesRecursiveResidualRanks`;
- `PaperEndpointFixedBaseProductReductionRankStratumCertificate`;
- `PaperEndpointFixedBaseProductReductionCertificate.residualRanks_of_edgeRankStratum`;
- `PaperEndpointFixedBaseProductReductionCertificate.rankStratumCertificate`;
- `PaperEndpointFixedBaseProductReductionCertificate.residualBlock_rank_eq_sourceRankSubProductRank`;
- `paperEndpointFixedBaseProductReductionRankStratumCertificate_selfBase_mem_nhdsWithin`;
- `paperEndpointFixedBaseProductReductionRankStratumCertificate_selfBase_mem_nhdsWithin_source`;
- `PaperEndpointFixedBaseProductReductionRankStratumLocalCertificate`;
- `PaperEndpointFixedBaseProductReductionRankStratumLocalCertificate.mem_nhdsWithin_source`;
- `PaperEndpointProductReductionRankStratumLocalCertificate`;
- `exists_paperEndpointProductReductionRankStratumLocalCertificate`.

The source-shaped stratum records base product rank `r`, exact nearby edge ranks
`rEdge`, and the inequalities `r <= rEdge p`.  On that stratum the basepoint
certificate rewrites `finrank U0` to `r`, giving the residual-rank formula
`rank(residualBlock p) = rEdge p - r`.

This still does not prove exact-rank openness, chart coverage from only source
rank hypotheses, Aoyagi Lemma 1, analytic ideal-germ transport,
regular-coordinate RLCT bookkeeping, normal crossings, or any RLCT consequence.

Artifacts:
`reproduction-a2-rank-stratum-boundary.md` and
`statement-card-a2-rank-stratum-boundary.md`.

## 2026-06-23 A2 source-rank-stratum endpoint wrapper

Combined the two latest fixed-base A2 boundary pieces: the endpoint triangular
block form with deterministic transformed residual product, and the source
rank-stratum residual-rank formula.

New Lean artifacts in `lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`:

- `PaperEndpointFixedBaseTriangularResidualProductSourceRanks`;
- `PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal_residualProduct_sourceRanks`.

The theorem takes a fixed-base basepoint certificate, a fixed-base
product-reduction certificate, and membership in
`paperEndpointFixedBaseSourceRankStratum`.  It returns a bundled endpoint
conclusion: regular triangular endpoint multipliers expose
`ChartLocalSuffixState.residualProduct`, and every visited residual block has
rank `rEdge p - r`.

Scope caveats: "source rank stratum" is repository terminology for Aoyagi's
fixed layer-rank restrictions.  The stratum supplies rank data for the
subtraction formula; the determinant-chart hypotheses required by Lemma 2
remain in the certificate.  This is not exact-rank openness, source-stratum
nonemptiness, full Theorem 3, Lemma 1 normalization, analytic ideal transport,
regular-coordinate RLCT bookkeeping, normal crossings, pole order, or RLCT.

Artifacts:
`reproduction-a2-source-rank-stratum-theorem3-boundary.md`,
`statement-card-a2-source-rank-stratum-theorem3-boundary.md`, and
`review-a2-source-rank-stratum-theorem3-boundary.md`.

## 2026-06-23 A2 local source-rank endpoint package

Lifted the fixed-base/source-rank endpoint wrapper into the local
product-reduction boundary.  The new theorem
`paperEndpointFixedBaseTriangularSourceRanks_selfBase_mem_nhdsWithin_source`
uses the existing ordinary neighborhood of fixed-base product-reduction
certificates, intersects it with `paperEndpointFixedBaseSourceRankStratum`, and
applies the pointwise source-rank endpoint wrapper.  Thus the conclusion is
relative to the source rank stratum; it does not assert exact-rank openness.

New Lean artifacts in `lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`:

- `paperEndpointFixedBaseSourceRankStratum_selfBase_mem`;
- `paperEndpointFixedBaseTriangularSourceRanks_selfBase_mem_nhdsWithin_source`;
- `PaperEndpointTriangularSourceRanksLocalCertificate`;
- `exists_paperEndpointTriangularSourceRanksLocalCertificate`.

This removes a downstream composition step for A2 consumers: after choosing a
total-kernel complement, the local package directly yields the triangular
endpoint residual-product/source-rank shape relative to the source rank
stratum.  The basepoint membership wrapper proves membership in that stratum
only from supplied product/layer rank equalities and inequalities.  The
endpoint lower-right block remains
`ChartLocalSuffixState.residualProduct` for transformed Schur residuals, not a
raw product of original edge lower-right blocks.

Scope caveats: this is not exact-rank openness, source-stratum nonemptiness,
full Theorem 3, Aoyagi Lemma 1 normalization, analytic ideal transport,
regular-coordinate RLCT additivity, normal crossings, pole order, or RLCT.

Artifacts:
`reproduction-a2-local-source-rank-endpoint-package.md` and
`statement-card-a2-local-source-rank-endpoint-package.md`.
Review:
`review-a2-local-source-rank-endpoint-package.md`.

## 2026-06-23 A2 block product-difference algebra

Formalized the p. 13 pointwise block product-difference calculation downstream
of the triangular endpoint form.  The new theorem
`triangularBlockProductDifference_fromBlocks_indexed` assumes

```text
[I 0; F3 I] * T * [I F2; 0 I] = [Ctop 0; 0 D]
```

and proves

```text
[I 0; F3 I] * (T - [I 0; 0 0]) * [I F2; 0 I]
  = [Ctop - I, -F2; -F3, D - F3 * F2].
```

This is pure block algebra over a commutative ring.  The endpoint wrapper was
intentionally not added: it would only destruct the existing triangular
endpoint certificate, and the source-rank field is irrelevant until a concrete
downstream ideal/certificate theorem needs the exact `T - T0` form.

Scope caveats: this is not source production of the triangular endpoint form,
full Theorem 3, Aoyagi Lemma 1, analytic generator transport, regular
suspension, normal crossings, pole order, or RLCT.

Artifacts:
`reproduction-a2-block-product-difference-algebra.md` and
`statement-card-a2-block-product-difference-algebra.md`.
Independent pen-and-paper check: xhigh `Lorentz`.
Fidelity/scope review: xhigh `Fermat`, accepted in
`review-a2-block-product-difference-algebra.md`.

## 2026-06-23 A2 product-difference entry-ideal boundary

Returned to the p. 13 product-difference block matrix because it now has a
concrete downstream consumer: the scalar matrix-entry ideal handoff at the
fixed-base/source-rank boundary.

New generic Lean artifacts in `lean/DLNFibre/DLN/Aoyagi/EntryIdeal.lean`:

- `matrixEntryIdeal_neg_eq`;
- `matrixEntryIdeal_fromBlocks_eq_fourMatrixEntryIdeal`;
- `matrixEntryIdeal_fromBlocks_neg_neg_sub_mul_eq_fourMatrixEntryIdeal`.

New boundary Lean artifacts in
`lean/DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean`:

- `matrixEntryIdeal_triangularBlockProductDifference_eq_fourMatrixEntryIdeal`;
- `PaperEndpointFixedBaseProductDifferenceEntryIdealSourceRanks`;
- `PaperEndpointFixedBaseTriangularResidualProductSourceRanks.exists_productDifferenceEntryIdeal`;
- `PaperEndpointFixedBaseTriangularResidualProductSourceRanks.toProductDifferenceEntryIdealSourceRanks`;
- `paperEndpointFixedBaseProductDifferenceEntryIdeal_selfBase_mem_nhdsWithin_source`;
- `PaperEndpointProductDifferenceEntryIdealLocalCertificate`;
- `exists_paperEndpointProductDifferenceEntryIdealLocalCertificate`.

The wrapper takes the existing triangular residual-product/source-rank package,
uses determinant-unit left/right entry-ideal transport, rewrites the signed
four-block matrix, and removes the `F3 * F2` correction modulo the entries of
`F2` and `F3`.  The lower-right block remains
`ChartLocalSuffixState.residualProduct`; the conclusion is a scalar
matrix-entry-ideal equality for endpoint matrices, relative to the source rank
stratum.

Scope caveats: this is not analytic germ-ideal transport, exact-rank openness,
source-stratum nonemptiness, full Theorem 3, Aoyagi Lemma 1 normalization,
regular-suspension RLCT additivity, normal-crossing production, pole order, or
RLCT.

Artifacts:
`reproduction-a2-product-difference-entry-ideal-boundary.md` and
`statement-card-a2-product-difference-entry-ideal-boundary.md`.
Review:
`review-a2-product-difference-entry-ideal-boundary.md`.

## 2026-06-23 A2 regular-variable count and finite shift

Returned to the regular block families isolated after Aoyagi Theorem 3:
`C1 - Er`, `F2`, and `F3`.  The pen-and-paper calculation records their scalar
entry count as

```text
r^2 + r(H^(L+1)-r) + (H^(1)-r)r
  = -r^2 + r(H^(1)+H^(L+1)).
```

Under endpoint rank-width bounds, half of this count is the regular term
already named in the Theorem 2 formula layer.

New Lean artifacts:

- `aoyagiTheorem2RegularVariableCount`;
- `aoyagiTheorem2RegularTerm_eq_half_regularVariableCount`;
- `AoyagiNormalCrossingExponentData.exponentMinimum_jacobianPriorLossShift_regularVariableCount`;
- `AoyagiNormalCrossingExponentData.exponentOrder_jacobianPriorLossShift_regularVariableCount`;
- `AoyagiNormalCrossingChartCertificate.exponentData_exponentMinimum_jacobianPriorLossShift_regularVariableCount`;
- `AoyagiNormalCrossingChartCertificate.exponentData_exponentOrder_jacobianPriorLossShift_regularVariableCount`;
- `AoyagiTheorem2FiniteExponentFormulaHypothesis.of_regularVariableCountShift`;
- `AoyagiTheorem2FiniteExponentFormulaHypothesis.of_chart_regularVariableCountShift`.

The first two names live in `lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean`; the
finite-shift bridge lives in `lean/DLNFibre/DLN/Aoyagi/RegularVariableShift.lean`.

Scope caveats: this is finite count and exponent-array arithmetic only.  It
does not construct a regular-suspension chart, transport analytic ideals,
invoke Aoyagi Lemma 1, prove regular-coordinate RLCT additivity, produce a
normal-crossing certificate, prove pole order, or prove an RLCT theorem.

Artifacts:
`reproduction-a2-regular-variable-count.md` and
`statement-card-a2-regular-variable-count.md`.
Review:
`review-a2-regular-variable-count.md`.

## 2026-06-24 A2 transformed-edge rank-stratum bridge

Returned to the source-rank boundary after the product-difference entry-ideal
package.  The recursive Schur-residual product applies Lemma 2 to transformed
edges of the form

```text
[I Bprev; 0 I] * E_p.
```

Because `[I Bprev; 0 I]` is determinant-unit block-unitriangular, the
transformed edge has the same rank as the original fixed-base source edge.

New Lean artifact in
`lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`:

- `paperEndpointFixedBase_transformedEdgeRanks_iff_edgeRankStratum`.

The theorem identifies the transformed-edge rank predicate used by
`ChartLocalSuffixState.transformedEdge` and `suffixState` with the already
named `paperEndpointFixedBaseEdgeRankStratum`.  This removes an ambiguity at
the A2 source-rank boundary: the recursion's transformed-edge exact-rank
condition is not an extra rank hypothesis beyond the fixed-base edge-rank
component of Aoyagi's source-shaped rank stratum.

Scope caveats: no exact-rank openness, source-stratum nonemptiness, chart
production, analytic ideal transport, regular-suspension/RLCT additivity,
normal-crossing production, pole order, or RLCT.

Artifacts:
`reproduction-a2-transformed-edge-rank-stratum-bridge.md` and
`statement-card-a2-transformed-edge-rank-stratum-bridge.md`.
Review:
`review-a2-transformed-edge-rank-stratum-bridge.md`.

## 2026-06-24 A2 regular-variable source-rank shift

Connected the A2 source-rank boundary to the regular-variable finite shift.
The existing regular-variable shift required endpoint rank-width assumptions
`r <= H 1` and `r <= H (N+1)`.  The new slice derives those assumptions from
source-rank-stratum membership and the explicit dimension convention
`H(k+1)=finrank(W k)`.

New Lean artifacts in `lean/DLNFibre/DLN/Aoyagi/RegularVariableShift.lean`:

- `paperEndpointFixedBaseSourceRankStratum_regularVariableEndpointBounds`;
- `AoyagiNormalCrossingExponentData.exponentMinimum_jacobianPriorLossShift_regularVariableCount_of_sourceRankStratum`;
- `AoyagiNormalCrossingChartCertificate.exponentData_exponentMinimum_jacobianPriorLossShift_regularVariableCount_of_sourceRankStratum`;
- `AoyagiTheorem2FiniteExponentFormulaHypothesis.of_regularVariableCountShift_sourceRankStratum`;
- `AoyagiTheorem2FiniteExponentFormulaHypothesis.of_chart_regularVariableCountShift_sourceRankStratum`.

Scope caveats: this is endpoint rank-width provenance and finite
certificate arithmetic only.  It does not prove exact-rank openness, regular
suspension chart construction, analytic ideal transport, Aoyagi Lemma 1,
normal-crossing chart production, pole order, RLCT, or a connection from the
supplied reduced certificate to the A2 geometry.

Artifacts:
`reproduction-a2-regular-variable-source-rank-shift.md` and
`statement-card-a2-regular-variable-source-rank-shift.md`.
Review:
`review-a2-regular-variable-source-rank-shift.md`.

## 2026-06-24 A2 regular-variable rank-width shift

The regular-variable finite shift has been weakened from A2 source-rank
stratum data to the source-range rank-width hypothesis already used by
Definition 3:

```text
forall s, 1 <= s -> s <= L+1 -> r <= H s.
```

The finite shift still needs only the endpoint projections `r <= H 1` and
`r <= H (L+1)`.  The final Definition 3 handoff, however, keeps the full
source-range rank-width hypothesis because selected-width side facts use
rank-width at every selected cutpoint.

New Lean artifacts in `lean/DLNFibre/DLN/Aoyagi/RegularVariableShift.lean`:

- `sourceRangeRankWidth_regularVariableEndpointBounds`;
- `AoyagiTheorem2FiniteExponentFormulaHypothesis.of_regularVariableCountShift_rankWidth`;
- `AoyagiTheorem2FiniteExponentFormulaHypothesis.of_chart_regularVariableCountShift_rankWidth`.

The older source-rank finite constructors remain as leaf wrappers but now
delegate through the rank-width constructors.

Scope caveats: finite exponent-array arithmetic and rank-width provenance
only.  This does not prove regular-suspension chart construction, analytic
ideal transport, Aoyagi Lemma 1, active-ratio or chart-count facts,
normal-crossing production, pole order, or RLCT.

Artifacts:
`reproduction-a2-regular-variable-rank-width-shift.md` and
`statement-card-a2-regular-variable-rank-width-shift.md`.
Review:
`review-a2-regular-variable-rank-width-shift.md`.

## 2026-06-24 A2 supplied regular-suspension interface

The p. 13 regular-variable step has been pinned to a conservative boundary:
Aoyagi supplies the block algebra and the count, while a genuine full
regular-suspension normal-crossing chart remains supplied.  The intended Lean
socket carries a reduced chart certificate and a full chart certificate
possibly over different parameter/coefficient types, named abstract
obligations for source/ideal/coverage/Jacobian compatibility, and the finite
exponent equality

```text
Cfull.exponentData =
  Cred.exponentData.jacobianPriorLossShift regularCount.
```

The extraction hypothesis is required for `Cfull`, not for `Cred` with an
after-the-fact `c/2` addition.  Finite consequences then build the existing
`AoyagiTheorem2SuppliedChartFinalBoundary Cfull ...` from reduced
minimum-plus-regular-term and order equalities, without routing through a
boundary for the synthetic shifted certificate.

Artifacts:
`reproduction-a2-regular-suspension-interface.md` and
`statement-card-a2-regular-suspension-interface.md`.
Review:
`review-a2-regular-suspension-interface.md`.

## 2026-06-24 Lean chart-local suffix-state field continuity

Reproduction:
`reproduction-a2-chart-local-suffix-state-field-continuity.md`.
Statement card:
`statement-card-a2-chart-local-suffix-state-field-continuity.md`.
Review:
`review-a2-chart-local-suffix-state-field-continuity.md`.

Lean now extends the chart-local topology API in `ChartTopology.lean`:

```text
continuousAt_chartLocalSuffixState_step_fields
continuousAt_chartLocalSuffixState_suffixState_fields
```

The one-step theorem proves fieldwise continuity of `L`, `B`, `Ctop`, and
`D`, and carries the next `IsUnit Ctop.det` invariant.  The suffix theorem
descends through the deterministic recursion under the same recursive
determinant-chart hypotheses as the existing `B` theorem, returning the
basepoint `Ctop.det` unit and fieldwise continuity for every `i <= j`.

This is only continuity of deterministic matrix fields at the basepoint.  It
does not prove analytic regularity, exact-rank openness, source-rank-stratum
openness, local source-neighborhood construction, regular suspension, ideal
transport, normal crossings, pole order, or RLCT.

## 2026-06-24 A2 fixed-base suffix-state field continuity handoff

Reproduction:
`reproduction-a2-fixed-base-suffix-state-field-continuity.md`.
Statement card:
`statement-card-a2-fixed-base-suffix-state-field-continuity.md`.
Review:
`review-a2-fixed-base-suffix-state-field-continuity.md`.

Lean now applies the generic suffix-state field-continuity theorem to the
endpoint-coordinate matrix family fixed from the base paper chain `B`:

```text
paperEndpointFixedBaseContinuousEdges_recursiveSuffixState_fields_continuousAt
```

The theorem defines the fixed-base coordinate edge family from a continuous
reversed-edge family `Cedge`, proves this matrix family is continuous by
fixed-basis coordinate continuity, rewrites the recursive determinant-chart
hypotheses, and returns `IsUnit Ctop.det` plus continuity of `L`, `B`,
`Ctop`, and `D` for every suffix state ending at `Fin.last N`.

Boundary: fixed-base continuity handoff only.  This does not prove analytic
regularity, exact-rank/source-rank openness, chart coverage, regular
suspension, ideal transport, normal crossings, pole order, or RLCT.

## 2026-06-24 A2 canonical product-difference coefficient fields

Reproduction:
`reproduction-a2-canonical-product-difference-coefficient-fields.md`.
Statement card:
`statement-card-a2-canonical-product-difference-coefficient-fields.md`.
Review:
`review-a2-canonical-product-difference-coefficient-fields.md`.

Lean now exposes the p. 13 product-difference entry-ideal equality with the
deterministic suffix-state fields instead of existential triangular witnesses:

```text
ChartLocalSuffixState.productDifferenceEntryIdeal_eq_fourMatrixEntryIdeal
PaperEndpointFixedBaseProductReductionCertificate.productDifferenceEntryIdeal_eq_fourMatrixEntryIdeal_canonicalFields
```

The generic theorem starts from a suffix-state block-diagonal invariant

```text
S.L * P(i,j) * [I -S.B; 0 I] = [S.Ctop 0; 0 S.D]
```

and proves the scalar matrix-entry ideal of
`P(i,j) - [I 0; 0 0]` is the four-block ideal generated by
`S.Ctop - I`, `-S.B`, `lowerLeftBlock S.L`, and `S.D`.  The proof uses
`suffixState_L_eq_lowerUnitriangular` to rewrite `S.L` as
`[I 0; lowerLeftBlock S.L I]`, then delegates to the existing
`matrixEntryIdeal_triangularBlockProductDifference_eq_fourMatrixEntryIdeal`.

The fixed-base theorem applies this pointwise to the endpoint matrix family
from `PaperEndpointFixedBaseProductReductionCertificate`, rewriting the
endpoint total matrix to the chain-map family with
`paperEndpointFixedBaseTotalMatrixOfReverseEdges_eq_chainMapMatrix`.

Boundary: rank-free algebraic entry-ideal handoff only.  This does not prove
source-rank neighborhood construction, exact-rank/source-rank openness,
analytic regularity, analytic germ-ideal transport, chart coverage, normal
crossings, pole order, or RLCT.

## 2026-06-24 A2 canonical product-difference coefficient-field continuity

Reproduction:
`reproduction-a2-canonical-product-difference-field-continuity.md`.
Statement card:
`statement-card-a2-canonical-product-difference-field-continuity.md`.
Review:
`review-a2-canonical-product-difference-field-continuity.md`.

Lean now proves that the deterministic fields used in the canonical
product-difference entry-ideal boundary are continuous fixed-base local
functions, and that they are centered at the self-base chain:

```text
paperEndpointFixedBaseContinuousEdges_productDifferenceCoefficientFields_continuousAt
paperEndpointFixedBaseContinuousEdges_selfBase_productDifferenceCoefficientFields_continuousAt
paperEndpointFixedBaseContinuousEdges_selfBase_productDifferenceCoefficientFields_centered_continuousAt
```

The explicit-chart theorem assumes a continuous reversed-edge family together
with the recursive determinant-chart hypotheses at `x0`; the self-base theorem
derives those hypotheses from `Cedge x0 = reverseEdge W B`.  The returned
fields are exactly the canonical p. 13 fields

```text
S.Ctop - 1,  -S.B,  lowerLeftBlock S.L,  S.D.
```

together with `IsUnit ((S x0).Ctop.det)`.  The centered self-base theorem also
proves the four basepoint equalities

```text
(S x0).Ctop - 1 = 0,
-(S x0).B = 0,
lowerLeftBlock (S x0).L = 0,
(S x0).D = 0.
```

Boundary: continuity and basepoint centering only.  This does not prove
analytic regularity, exact-rank/source-rank openness, chart coverage, analytic
ideal or germ transport, a regular-suspension certificate, normal crossings,
pole order, or RLCT.

## 2026-06-24 A2 canonical product-difference local certificate

Reproduction:
`reproduction-a2-canonical-product-difference-local-certificate.md`.
Statement card:
`statement-card-a2-canonical-product-difference-local-certificate.md`.
Review:
`review-a2-canonical-product-difference-local-certificate.md`.

Lean now packages the centered continuous canonical fields with the local
source-rank product-difference boundary:

```text
PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks
PaperEndpointFixedBaseProductReductionCertificate.toCanonicalProductDifferenceSourceRanks
paperEndpointFixedBaseCanonicalProductDifferenceSourceRanks_selfBase_mem_nhdsWithin_source
PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate
paperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate_of_isCompl
PaperEndpointCanonicalProductDifferenceLocalCertificate
exists_paperEndpointCanonicalProductDifferenceLocalCertificate
```

The pointwise source-rank predicate uses the deterministic fields

```text
S.Ctop - 1,  -S.B,  lowerLeftBlock S.L,  S.D
```

in the `fourMatrixEntryIdeal` equality and carries the residual-rank formulas
`rank residualBlock_p = rEdge p - r`.  The fixed-base local certificate also
stores the self-base centered-continuity theorem for those same four fields.
The local conclusion is relative to `paperEndpointFixedBaseSourceRankStratum`
via `nhdsWithin`.

Boundary: canonical local packaging only.  This does not assert exact-rank or
source-rank openness, analytic regularity, chart coverage, analytic ideal or
germ transport, a regular-suspension certificate, normal crossings, pole
order, or RLCT.

## 2026-06-24 A2 canonical product-difference local source certificate

Reproduction:
`reproduction-a2-canonical-product-difference-local-source-certificate.md`.
Statement card:
`statement-card-a2-canonical-product-difference-local-source-certificate.md`.
Review:
`review-a2-canonical-product-difference-local-source-certificate.md`.

Target: pair the canonical product-difference local certificate with basepoint
membership in Aoyagi's source-shaped rank stratum, under supplied source rank
data for the base product and base edges.  This removes the vacuity caveat for
the base chain without claiming exact-rank/source-rank openness.

Lean now has:

```text
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
paperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate_of_isCompl
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_source_neighborhood
PaperEndpointCanonicalProductDifferenceLocalSourceCertificate
exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate
```

Boundary: nonvacuity/source-rank packaging only.  The local conclusion remains
`nhdsWithin` the source-shaped rank stratum, and the explicit neighborhood
projection keeps source-rank membership as a guard.  This does not prove the
stratum is open, construct regular-suspension charts, transport analytic
ideals, prove normal crossings, identify pole order, or extract RLCT.

## 2026-06-24 A2 canonical product-difference regular-chart source

Reproduction:
`reproduction-a2-canonical-product-difference-regular-chart-source.md`.
Statement card:
`statement-card-a2-canonical-product-difference-regular-chart-source.md`.
Review:
`review-a2-canonical-product-difference-regular-chart-source.md`.

Target: make the supplied regular-suspension boundary consume the A2 local
source certificate directly for its `regular_chart_source` field, without
claiming the analytic regular-suspension construction.

Lean now has:

```text
AoyagiCanonicalProductDifferenceRegularChartSource
AoyagiSuppliedRegularSuspensionBoundary.of_canonicalProductDifferenceRegularChartSource
```

The source predicate is definitionally the existing
`PaperEndpointCanonicalProductDifferenceLocalSourceCertificate W B x0 Cedge r
rEdge`, viewed as a predicate on `Cred`, `Cfull`, and `regularCount`.  The
constructor fills only `regular_chart_source`; ideal transport, coverage,
Jacobian compatibility, and the exponent-data shift equality remain supplied.

Boundary: A2 source-predicate handoff only.  This does not scalarize the
regular variables, prove the regular count, construct `Cfull`, prove analytic
ideal/germ transport, prove chart coverage, prove Jacobian compatibility,
produce normal crossings, identify pole order, or extract RLCT.

Next stronger A2 target from xhigh scout: scalarize the p. 13 regular blocks
`S.Ctop - 1`, `-S.B`, and `lowerLeftBlock S.L`, prove their centered
continuity as finite scalar coordinates, and prove the coordinate count is
`aoyagiTheorem2RegularVariableCount`.

## 2026-06-24 A2 regular-suspension coordinate index

Reproduction:
`reproduction-a2-regular-suspension-coordinate-index.md`.
Statement card:
`statement-card-a2-regular-suspension-coordinate-index.md`.
Review:
`review-a2-regular-suspension-coordinate-index.md`.

Lean now scalarizes the p. 13 regular block families:

```text
AoyagiRegularBlockCoordinateIndex
AoyagiRegularBlockCoordinateIndex.card
AoyagiRegularBlockCoordinateIndex.value
AoyagiRegularBlockCoordinateIndex.value_centered_continuousAt
AoyagiRegularBlockCoordinateIndex.card_eq_aoyagiTheorem2RegularVariableCount
paperEndpointEndpointComplementIndex_card_eq_layerSubRank
paperEndpointRegularBlockCoordinateIndex_card_eq_regularVariableCount
PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.regularBlockScalarCoordinates_centered_continuousAt
PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.regularBlockCoordinateIndex_card_eq_regularVariableCount
```

The coordinate index is the finite disjoint union of entries of
`Ctop - 1`, `F2`, and `F3`.  The local-certificate projection applies the
existing centered continuity of `S.Ctop - 1`, `-S.B`, and
`lowerLeftBlock S.L` to every scalar coordinate.  The residual field `S.D` is
excluded.  The endpoint-compatible count theorem now derives the source and
target residual cardinalities from the fixed-base endpoint complement
construction, base product rank, and dimension convention.

Boundary: finite coordinate bookkeeping and componentwise continuity only.
This does not construct analytic regular coordinates, construct `Cfull`, prove
the four-block ideal split, prove ideal transport, prove chart coverage, prove
Jacobian compatibility, produce normal crossings, identify pole order, or
extract RLCT.

## 2026-06-24 A2 regular/residual ideal split

Reproduction:
`reproduction-a2-regular-residual-ideal-split.md`.
Statement card:
`statement-card-a2-regular-residual-ideal-split.md`.
Review:
`review-a2-regular-residual-ideal-split.md`.

Lean now names the regular block-entry ideal and exposes the algebraic split
from the four-block product-difference ideal:

```text
regularBlockEntryIdeal
fourMatrixEntryIdeal_eq_regularBlockEntryIdeal_sup_matrixEntryIdeal
matrixEntryIdeal_triangularBlockProductDifference_eq_regular_sup_residual
ChartLocalSuffixState.productDifferenceEntryIdeal_eq_regularBlockEntryIdeal_sup_matrixEntryIdeal
PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks.canonicalProductDifferenceEntryIdeal_eq_regularBlockEntryIdeal_sup_matrixEntryIdeal
```

The canonical fixed-base theorem rewrites the product-difference entry ideal as

```text
regularBlockEntryIdeal (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) ⊔
  matrixEntryIdeal S.D.
```

Boundary: scalar ideal regrouping only.  `S.D` remains residual, not part of
the regular-coordinate index.  This does not prove analytic germ-ideal
transport, regular-suspension chart construction, coverage, Jacobian
compatibility, normal crossings, pole order, or RLCT.

## 2026-06-24 A2 regular-coordinate ideal bridge

Reproduction:
`reproduction-a2-regular-coordinate-ideal-bridge.md`.
Statement card:
`statement-card-a2-regular-coordinate-ideal-bridge.md`.
Review:
`review-a2-regular-coordinate-ideal-bridge.md`.

Lean now connects the scalar coordinate index to the regular block-entry ideal:

```text
AoyagiRegularBlockCoordinateIndex.entryIdeal
AoyagiRegularBlockCoordinateIndex.entryIdeal_eq_regularBlockEntryIdeal
PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks.canonicalProductDifferenceEntryIdeal_eq_regularCoordinateIdeal_sup_matrixEntryIdeal
```

The theorem proves that the ideal generated by the scalar values of
`AoyagiRegularBlockCoordinateIndex.value X F2 F3` is exactly
`regularBlockEntryIdeal X F2 F3`.  The fixed-base canonical theorem composes
this with the regular/residual split, rewriting the product-difference entry
ideal as the scalar regular-coordinate ideal joined with `matrixEntryIdeal S.D`.

Boundary: algebraic ideal bookkeeping only.  The scalar-coordinate ideal theorem
is valid without finite index assumptions; the finite Aoyagi use is supplied by
the count theorems.  The residual block `D` is not part of the scalar
regular-coordinate index.  This does not construct analytic regular
coordinates, transport analytic germ ideals, prove chart coverage or Jacobian
compatibility, produce normal crossings, identify pole order, or extract RLCT.

## 2026-06-24 A2 local source regular-coordinate ideal split

Reproduction:
`reproduction-a2-local-source-regular-coordinate-ideal-split.md`.
Statement card:
`statement-card-a2-local-source-regular-coordinate-ideal-split.md`.
Review:
`review-a2-local-source-regular-coordinate-ideal-split.md`.

Lean now upgrades the fixed-base local source certificate to a neighborhood
statement using scalar regular coordinates:

```text
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_regularCoordinateIdeal_source_neighborhood
```

For points in the returned neighborhood that also lie in the source-shaped rank
stratum, the product-difference entry ideal is the scalar regular-coordinate
ideal generated by `S.Ctop - 1`, `-S.B`, and `lowerLeftBlock S.L`, joined with
the residual ideal `matrixEntryIdeal S.D`.

Boundary: local source-side algebraic bookkeeping only.  The source-stratum
guard remains explicit; this does not prove source-rank openness, analytic
germ-ideal transport, regular-suspension chart construction, coverage,
Jacobian compatibility, normal crossings, pole order, or RLCT.

## 2026-06-24 A2 regular-coordinate ideal source predicate

Reproduction:
`reproduction-a2-regular-coordinate-ideal-source-predicate.md`.
Statement card:
`statement-card-a2-regular-coordinate-ideal-source-predicate.md`.
Review:
`review-a2-regular-coordinate-ideal-source-predicate.md`.

Lean now names the source predicate needed by a later supplied
regular-suspension chart:

```text
PaperEndpointFixedBaseRegularCoordinateIdealSourceNeighborhood
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.regularCoordinateIdealSourceNeighborhood
AoyagiCanonicalProductDifferenceRegularCoordinateIdealSource
aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_localSourceCertificate
AoyagiSuppliedRegularSuspensionBoundary.of_canonicalProductDifferenceRegularCoordinateIdealSource
```

The fixed-base predicate records a neighborhood where, on the source-shaped
rank stratum, the canonical product-difference ideal is the scalar
regular-coordinate ideal joined with the residual `S.D` ideal.  The
regular-suspension source predicate existentially chooses the fixed endpoint
base certificate and carries both the local source certificate and the named
regular-coordinate/residual ideal neighborhood.

The boundary constructor fills only `regular_chart_source`.  Ideal transport,
coverage, Jacobian compatibility, and the exponent-shift equality are still
supplied.  This keeps the stronger algebraic source information available
without importing the coordinate file back into `RegularSuspensionInterface`.

Boundary: source-side algebraic source predicate only.  No source-rank
openness, analytic germ-ideal transport, construction of `Cfull`, coverage,
Jacobian compatibility, exponent shift, normal crossings, pole order, or RLCT
is proved.

## 2026-06-24 A2 regular-coordinate ideal source existence

Reproduction:
`reproduction-a2-regular-coordinate-ideal-source-existence.md`.
Statement card:
`statement-card-a2-regular-coordinate-ideal-source-existence.md`.
Review:
`review-a2-regular-coordinate-ideal-source-existence.md`.

Lean now gives the raw-hypothesis constructor for the stronger source
predicate:

```text
exists_aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource
```

It takes a continuous reversed-edge family based at `B`, the supplied base
product rank, supplied base edge ranks, and the supplied rank bounds
`r <= rEdge p`.  It first uses
`exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate` to
choose the endpoint complement and local source certificate, then applies
`aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_localSourceCertificate`.

Boundary: composition of existing source-side algebra only.  No source-rank
openness, analytic germ-ideal transport, construction of `Cfull`, ideal
transport, coverage, Jacobian compatibility, exponent shift, normal crossings,
pole order, or RLCT is proved.

## 2026-06-24 A2 base product rank bounded by edge ranks

Reproduction:
`reproduction-a2-base-product-rank-le-edge-rank.md`.
Statement card:
`statement-card-a2-base-product-rank-le-edge-rank.md`.
Review:
`review-a2-base-product-rank-le-edge-rank.md`.

Lean now proves the elementary base-chain rank inequality:

```text
paperTotalMap_finrank_range_le_reverseEdge_finrank_range
```

For each edge `p`, the full reversed product factors through
`reverseEdge W B p`, so its range finrank is bounded by the edge range
finrank.  The basepoint source-rank-stratum API now has a no-`hle` constructor:

```text
paperEndpointFixedBaseSourceRankStratum_selfBase_mem_of_rank_eq
```

and the source-certificate path has matching no-`hle` wrappers:

```text
paperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate_of_isCompl_of_rank_eq
exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate_of_rank_eq
exists_aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_rank_eq
```

Boundary: basepoint rank packaging only.  This removes the redundant base
inequality input from the new wrappers, but it does not prove exact-rank or
source-rank openness, analytic germ-ideal transport, `Cfull`, ideal transport,
coverage, Jacobian compatibility, exponent shift, normal crossings, pole
order, or RLCT.

## 2026-06-24 A2 regular-coordinate source data

Reproduction:
`reproduction-a2-regular-coordinate-source-data.md`.
Statement card:
`statement-card-a2-regular-coordinate-source-data.md`.
Review:
`review-a2-regular-coordinate-source-data.md`.

Lean now packages the source-produced p. 13 regular-coordinate data in
`RegularSuspensionCoordinates.lean`:

```text
PaperEndpointFixedBaseRegularBlockScalarCoordinatesCenteredContinuousAt
PaperEndpointFixedBaseRegularCoordinateSourceData
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.regularCoordinateSourceData
exists_paperEndpointFixedBaseRegularCoordinateSourceData_of_rank_eq
```

The rank-equality theorem starts from a continuous reversed-edge family based
at `B`, base product rank `r`, base edge ranks `rEdge`, and the dimension
convention `H(k+1)=finrank(W k)`.  It chooses a total-kernel complement and
returns a fixed-base package containing the local source certificate, the
source-stratum guarded regular/residual ideal split, centered continuous
scalar coordinates for `S.Ctop - 1`, `-S.B`, and `lowerLeftBlock S.L`, and the
cardinality equality with `aoyagiTheorem2RegularVariableCount N H r`.

Boundary: source-side regular-coordinate data only.  No exact-rank or
source-rank openness, analytic germ-ideal transport, regular-suspension chart
construction, coverage, Jacobian compatibility, exponent shift, normal
crossings, pole order, or RLCT is proved.

## 2026-06-24 A2 regular-suspension normal-crossing boundary audit

Audit:
`audit-a2-regular-suspension-normal-crossing-boundary.md`.

Controller inspection and xhigh scout `Locke the 3rd` agree that the current
APIs cannot construct a full regular-suspension normal-crossing certificate
`Cfull` from `PaperEndpointFixedBaseRegularCoordinateSourceData`.

The reason is precise.  The source-data package proves centered continuous
scalar regular-coordinate functions and a source-stratum guarded ideal split,
but it does not prove those scalar functions form analytic coordinates.  The
current `AoyagiNormalCrossingChartCertificate` records finite monomial chart
data and supports certificate algebra such as `jacobianPriorLossShift`; it
does not encode analytic chart coverage, coordinate invertibility, generator
transport, or regular-coordinate additivity.

Do not add a theorem

```text
PaperEndpointFixedBaseRegularCoordinateSourceData -> exists Cfull, ...
```

and do not introduce source-anchored analytic obligation predicates whose
fields are empty, `True`, or merely renamed arbitrary predicates.  A Lean
boundary for regular suspension is worthwhile only after a pen-and-paper
reproduction identifies concrete full/reduced generator families, analytic
regular coordinates, coverage, Jacobian/prior shift, units, and extraction for
the actual full certificate.

## 2026-06-24 A2 residual-coordinate source data

Reproduction:
`reproduction-a2-residual-coordinate-source-data.md`.
Statement card:
`statement-card-a2-residual-coordinate-source-data.md`.
Review:
`review-a2-residual-coordinate-source-data.md`.

Lean now also scalarizes the residual p. 13 block in
`RegularSuspensionCoordinates.lean`:

```text
AoyagiResidualBlockCoordinateIndex
AoyagiResidualBlockCoordinateIndex.entryIdeal_eq_matrixEntryIdeal
AoyagiResidualBlockCoordinateIndex.value_centered_continuousAt
paperEndpointResidualBlockCoordinateIndex_card_eq_endpointResidualEntryCount
PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.residualBlockScalarCoordinates_centered_continuousAt
PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.residualBlockCoordinateIndex_card_eq_endpointResidualEntryCount
PaperEndpointFixedBaseResidualBlockScalarCoordinatesCenteredContinuousAt
```

The existing `PaperEndpointFixedBaseRegularCoordinateSourceData` structure now
also carries centered continuity for scalar entries of `S.D` and the residual
endpoint entry count `(H 1-r)*(H(N+1)-r)`.  This makes the reduced block side
of the regular/residual split explicit while keeping it separate from the
regular-coordinate index and the regular-variable finite shift.

Boundary: source-side residual-coordinate bookkeeping only.  No analytic
residual chart, normal-crossing certificate, germ-ideal transport, coverage,
Jacobian compatibility, exponent shift, regular-coordinate additivity, pole
order, or RLCT is proved.

Xhigh review by `Curie the 3rd` passed after repairing prose that called the
row/left and column/right residual endpoint indices "source" and "target".
The formulas were correct before the wording repair.

## 2026-06-24 A2 product-difference coordinate source data

Reproduction:
`reproduction-a2-product-difference-coordinate-source-data.md`.
Statement card:
`statement-card-a2-product-difference-coordinate-source-data.md`.
Review:
`review-a2-product-difference-coordinate-source-data.md`.

Lean now scalarizes the cleaned p. 13 product-difference ideal-level family in
`RegularSuspensionCoordinates.lean`:

```text
AoyagiProductDifferenceCoordinateIndex
AoyagiProductDifferenceCoordinateIndex.entryIdeal_eq_fourMatrixEntryIdeal
AoyagiProductDifferenceCoordinateIndex.matrixEntryIdeal_fromBlocks_neg_neg_sub_mul_eq_entryIdeal
AoyagiProductDifferenceCoordinateIndex.value_centered_continuousAt
AoyagiProductDifferenceCoordinateIndex.card_eq_endpointProductEntryCount
paperEndpointProductDifferenceCoordinateIndex_card_eq_endpointProductEntryCount
PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks.canonicalProductDifferenceEntryIdeal_eq_productDifferenceCoordinateIdeal
PaperEndpointFixedBaseProductDifferenceCoordinateIdealSourceNeighborhood
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_productDifferenceCoordinateIdeal_source_neighborhood
PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.productDifferenceScalarCoordinates_centered_continuousAt
PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.productDifferenceCoordinateIndex_card_eq_endpointProductEntryCount
PaperEndpointFixedBaseProductDifferenceScalarCoordinatesCenteredContinuousAt
```

The index is the sum of the regular scalar-coordinate index and residual
scalar-coordinate index, so its scalar ideal is the cleaned four-block ideal
generated by entries of `S.Ctop - 1`, `-S.B`, `lowerLeftBlock S.L`, and `S.D`.
The source-data structure now also carries the source-stratum guarded
product-difference coordinate ideal neighborhood, componentwise centered
continuity for the combined family, and the endpoint product-entry count
`H 1 * H(N+1)`.

Boundary: source-side finite coordinate and ideal bookkeeping only. No
analytic coordinate chart, regular-suspension chart construction, analytic
germ-ideal transport, coverage, transition regularity, Jacobian compatibility,
normal crossings, pole order, or RLCT is proved.

Xhigh review by `Descartes the 3rd` passed after repairing the reproduction's
source anchor to distinguish the literal signed/corrected p. 13 display from
the cleaned four-family entry-ideal generator package.

## 2026-06-24 A2 literal product-difference coordinate ideal bridge

Reproduction:
`reproduction-a2-literal-product-difference-coordinate-ideal-bridge.md`.
Statement card:
`statement-card-a2-literal-product-difference-coordinate-ideal-bridge.md`.
Review:
`review-a2-literal-product-difference-coordinate-ideal-bridge.md`.

Lean now names the direct ideal bridge from the literal signed/corrected p. 13
block to the combined product-difference coordinate ideal:

```text
AoyagiProductDifferenceCoordinateIndex.matrixEntryIdeal_fromBlocks_neg_neg_sub_mul_eq_entryIdeal
```

For arbitrary `X`, `F2`, `F3`, and `D`, it proves

```text
matrixEntryIdeal (fromBlocks X (-F2) (-F3) (D - F3 * F2))
  =
AoyagiProductDifferenceCoordinateIndex.entryIdeal X F2 F3 D.
```

The theorem is finite scalar ideal algebra only.  It uses the previous
signed-block cleanup and
`AoyagiProductDifferenceCoordinateIndex.entryIdeal_eq_fourMatrixEntryIdeal`;
the correction is `F3*F2`, not `F2*F3`.

## 2026-06-24 A2 product-reduction triangular coordinate chart

Reproduction:
`reproduction-a2-product-reduction-triangular-coordinate-chart.md`.
Statement card:
`statement-card-a2-product-reduction-triangular-coordinate-chart.md`.
Review:
`review-a2-product-reduction-triangular-coordinate-chart.md`.

Lean now packages the one-step p. 13 triangular variable change in
`ProductReduction.lean`:

```text
ProductReductionStepRawCoordinates
ProductReductionStepChartCoordinates
ProductReductionStepRawCoordinates.detChart
ProductReductionStepChartCoordinates.detChart
ProductReductionStepRawCoordinates.toChart
ProductReductionStepChartCoordinates.toRaw
ProductReductionStepRawCoordinates.detChart_toChart
ProductReductionStepChartCoordinates.detChart_toRaw
productReductionStepCoordinate_left_inverse
productReductionStepCoordinate_right_inverse
```

The raw variables are `C1, D, F3, A1, A2, A3, A4`; the chart variables are
`Ctop, D, A1, A3, F2, F3, C`.  The forward formulas are
`Ctop=C1*A1`, `F2=-(A1⁻¹*A2)`,
`F3=F3old-D*A3*(C1*A1)⁻¹`, and `C=A4-A3*A1⁻¹*A2`, with inverse formulas that
retain passive `D`, `A1`, and `A3` and never invert `D`.

Boundary: elementary determinant-chart coordinate algebra only.  It does not
prove analytic coordinate chart status, exact-rank/source-rank openness,
regular-suspension chart construction, block-difference wrapper transport,
analytic germ-ideal transport, coverage, Jacobian compatibility, normal
crossings, pole order, or RLCT extraction.

## 2026-06-24 A2 product-reduction step product-difference wrapper

Reproduction:
`reproduction-a2-product-reduction-step-product-difference-wrapper.md`.
Statement card:
`statement-card-a2-product-reduction-step-product-difference-wrapper.md`.
Review:
`review-a2-product-reduction-step-product-difference-wrapper.md`.

Lean now connects the p. 13 coordinate package to the one-step product and
product-difference block identities:

```text
productReductionStepCoordinate_triangularBlockProduct
productReductionStepCoordinate_productDifference
```

The theorem consumes a prior triangular product hypothesis
`[I 0; F3old I] T = [C1 0; 0 D] [A1 A2; A3 A4]`, sets
`y = x.toChart`, and proves
`[I 0; y.F3 I] T [I y.F2; 0 I] = [y.Ctop 0; 0 y.D*y.C]`.
Subtracting `[I 0; 0 0]` gives the signed p. 13 block
`[y.Ctop-I, -y.F2; -y.F3, y.D*y.C - y.F3*y.F2]`.

Boundary: finite block algebra only.  No inverse of `D` is used.  The
lower-right correction is `F3*F2`.  The suffix-state adapter from
`ChartLocalSuffixState.BlockDiagonal` is recorded separately, and the
coordinate-ideal naming bridge is recorded in the literal product-difference
coordinate ideal bridge card.

## 2026-06-24 A2 suffix-state step coordinate adapter

Reproduction:
`reproduction-a2-suffix-state-step-coordinate-adapter.md`.
Statement card:
`statement-card-a2-suffix-state-step-coordinate-adapter.md`.
Review:
`review-a2-suffix-state-step-coordinate-adapter.md`.

Lean now exposes the one-step deterministic suffix-state adapter:

```text
ChartLocalSuffixState.stepRawCoordinates
ChartLocalSuffixState.stepRawCoordinates_detChart
ChartLocalSuffixState.stepRawCoordinates_toChart_Ctop
ChartLocalSuffixState.stepRawCoordinates_toChart_F2
ChartLocalSuffixState.stepRawCoordinates_toChart_C
ChartLocalSuffixState.stepRawCoordinates_toChart_D_mul_C
ChartLocalSuffixState.stepRawCoordinates_toChart_F3_of_L_eq_lowerUnitriangular
ChartLocalSuffixState.stepRawCoordinates_priorProduct
ChartLocalSuffixState.stepRawCoordinates_triangularBlockProduct
ChartLocalSuffixState.stepRawCoordinates_productDifference
```

The adapter builds raw p. 13 coordinates from `S.Ctop`, `S.D`, a witnessed
lower-left block `F3prev` of `S.L`, and the four corners of
`transformedEdge E p S`.  It proves that `S.BlockDiagonal P hpj` supplies the
prior product hypothesis for `T = P p.castSucc j`, then applies the p. 13
coordinate wrappers to get the triangular product and signed
product-difference block.

Boundary: finite block algebra only.  `BlockDiagonal` alone does not prove
`S.L` is lower unitriangular; the adapter takes that witness as an input.
The determinant chart is on `transformedEdge E p S`, not raw `E p`, and no
inverse of `S.D` is used.

## 2026-06-24 A2 suffix-state step coordinate specialization

Reproduction:
`reproduction-a2-suffix-state-step-coordinate-specialization.md`.
Statement card:
`statement-card-a2-suffix-state-step-coordinate-specialization.md`.
Review:
`review-a2-suffix-state-step-coordinate-specialization.md`.

Lean now specializes the previous arbitrary-suffix-state coordinate adapter to
the actual recursive state:

```text
ChartLocalSuffixState.suffixState_stepRawCoordinates_triangularBlockProduct
ChartLocalSuffixState.suffixState_stepRawCoordinates_productDifference
```

For `S = suffixState E j p.succ hpj`, the wrappers keep the local hypotheses
`S.BlockDiagonal P hpj` and
`identityCornerDetChart (transformedEdge E p S)`, choose the lower-left
witness `F3prev` from `suffixState_L_eq_lowerUnitriangular`, and apply the
generic `stepRawCoordinates_*` theorems.  The product matrix is still
`P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj)`, while the raw
coordinate corners come from `transformedEdge E p S`.

Boundary: finite block algebra only.  This does not derive `S.BlockDiagonal`
from global recursion hypotheses, and it does not prove analytic chart
coverage, ideal transport, regular-suspension construction, normal crossings,
pole order, or RLCT.

## 2026-06-24 A2 regular-suspension coordinate map source data

Reproduction:
`reproduction-a2-regular-suspension-coordinate-map-source-data.md`.
Statement card:
`statement-card-a2-regular-suspension-coordinate-map-source-data.md`.
Review:
`review-a2-regular-suspension-coordinate-map-source-data.md`.

Lean now packages the existing scalar p. 13 source-data fields as Pi-valued
coordinate maps:

```text
paperEndpointFixedBaseRegularBlockCoordinateMap
paperEndpointFixedBaseResidualBlockCoordinateMap
paperEndpointFixedBaseProductDifferenceCoordinateMap
```

and proves that the existing fixed-base source-data package supplies centered
continuity for each map:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.regularBlockCoordinateMap_centered_continuousAt
PaperEndpointFixedBaseRegularCoordinateSourceData.residualBlockCoordinateMap_centered_continuousAt
PaperEndpointFixedBaseRegularCoordinateSourceData.productDifferenceCoordinateMap_centered_continuousAt
```

The proofs are componentwise: basepoint vanishing is function extensionality
from the scalar source fields, and continuity uses `continuousAt_pi`.

Boundary: finite/topological packaging only.  This does not construct an
analytic coordinate chart, local inverse, source-rank-open neighborhood,
analytic ideal transport, chart coverage, Jacobian compatibility, normal
crossings, pole order, or RLCT.

## 2026-06-24 A2 cleaned coordinate square-sum

Reproduction:
`reproduction-a2-cleaned-coordinate-square-sum.md`.
Statement card:
`statement-card-a2-cleaned-coordinate-square-sum.md`.
Review:
`review-a2-cleaned-coordinate-square-sum.md`.

Lean now names the finite algebraic square-sum of a scalar coordinate family:

```text
aoyagiCoordinateSquareSum
aoyagiCoordinateSquareSum_sumElim
```

and proves the cleaned p. 13 product-difference coordinate family splits over
the regular/residual disjoint sum:

```text
AoyagiProductDifferenceCoordinateIndex.coordinateSquareSum_eq_regular_add_residual
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_sumElim
paperEndpointFixedBaseProductDifferenceCoordinateMap_squareSum_eq_regular_add_residual
```

This gives the exact square-sum decomposition for the cleaned coordinate
family `C1-Er, F2, F3, prod_s C^(s)`.

Boundary: finite square-sum bookkeeping only.  It does not identify this
cleaned square-sum with the literal signed/corrected p. 13 Frobenius loss,
does not prove analytic generator transport or loss comparability, and does
not construct charts, prove Jacobian compatibility, normal crossings, pole
order, or RLCT.

## 2026-06-24 A2 literal product-difference square-sum

Reproduction:
`reproduction-a2-literal-product-difference-square-sum.md`.
Statement card:
`statement-card-a2-literal-product-difference-square-sum.md`.
Review:
`review-a2-literal-product-difference-square-sum.md`.

Lean now names the scalar coordinate family attached to the literal
signed/corrected p. 13 block:

```text
AoyagiProductDifferenceCoordinateIndex.literalValue
AoyagiProductDifferenceCoordinateIndex.literalValue_regular
AoyagiProductDifferenceCoordinateIndex.literalValue_residual
```

and proves the finite square-sum split

```text
AoyagiProductDifferenceCoordinateIndex.literalCoordinateSquareSum_eq_regular_add_correctedResidual
```

for

```text
fromBlocks X (-F2) (-F3) (D - F3 * F2).
```

The theorem expands the literal square-sum as regular square-sum plus the
corrected residual square-sum for `D - F3 * F2`; the signs disappear by
`(-a)^2 = a^2`.

Boundary: finite square-sum bookkeeping only.  It does not compare
`D - F3*F2` with `D`, prove local loss comparability, prove analytic generator
transport, construct charts, prove Jacobian compatibility, normal crossings,
pole order, or RLCT.

## 2026-06-24 A2 regular-suspension finite loss comparison

Reproduction:
`reproduction-a2-regular-suspension-loss-comparison-and-fubini-boundary.md`.
Statement card:
`statement-card-a2-regular-suspension-loss-comparison-and-fubini-boundary.md`.
Review:
`review-a2-regular-suspension-loss-comparison-and-fubini-boundary.md`.

Lean now proves the finite ordered-ring square-sum comparison between the
literal p. 13 scalar family

```text
X, -F2, -F3, D - F3 * F2
```

and the cleaned scalar family

```text
X, F2, F3, D.
```

The key new Lean names include:

```text
aoyagiCoordinateSquareSum_sub_le_two_mul_add_two_mul
aoyagiCoordinateSquareSum_add_le_two_mul_add_two_mul
AoyagiRegularBlockCoordinateIndex.coordinateSquareSum_eq_ctop_add_f2_add_f3
AoyagiProductDifferenceCoordinateIndex.productCorrectionSquareSum_le_f3SquareSum_mul_f2SquareSum
AoyagiProductDifferenceCoordinateIndex.four_mul_productCorrectionSquareSum_le_regular_of_f2_f3_squareSum_add_le_one
AoyagiProductDifferenceCoordinateIndex.literalCoordinateSquareSum_le_two_mul_coordinateSquareSum_of_f2_f3_squareSum_add_le_one
AoyagiProductDifferenceCoordinateIndex.coordinateSquareSum_le_two_mul_literalCoordinateSquareSum_of_f2_f3_squareSum_add_le_one
```

Under the finite smallness hypothesis

```text
squareSum(F2) + squareSum(F3) <= 1,
```

Lean proves both

```text
literalSquareSum <= 2 * cleanedSquareSum,
cleanedSquareSum <= 2 * literalSquareSum.
```

The proof includes the finite row-column Cauchy-Schwarz estimate
`squareSum(F3*F2) <= squareSum(F3) * squareSum(F2)`.

Boundary: finite ordered-ring square-sum comparison only.  The generic real
ambient-neighborhood shrink from centered continuity is a separate entry
below; analytic regular-coordinate status, Fubini/polar regular-variable
shift, chart coverage, Jacobian compatibility, normal crossings, pole order,
and RLCT remain unproved.

Review passed after wording repairs: the factor-`2` theorem docstrings now
state the combined hypothesis `squareSum(F2)+squareSum(F3) <= 1`, and the
statement card no longer claims sharpness of the constant.

## 2026-06-24 A2 continuity-to-small-loss neighborhood

Reproduction:
`reproduction-a2-continuity-to-small-loss-neighborhood.md`.
Statement card:
`statement-card-a2-continuity-to-small-loss-neighborhood.md`.
Review:
`review-a2-continuity-to-small-loss-neighborhood.md`.

Lean now proves the generic real topology that supplies the finite
comparison's smallness hypothesis from centered continuity:

```text
aoyagiCoordinateSquareSum_continuousAt
aoyagiCoordinateSquareSum_eventually_le_one_of_continuousAt_zero
aoyagiCoordinateSquareSum_add_eventually_le_one_of_continuousAt_zero
aoyagiCoordinateSquareSum_eventually_le_one_of_forall_centered_continuousAt
aoyagiCoordinateSquareSum_add_eventually_le_one_of_forall_centered_continuousAt
```

The one-family theorem says that if `f : alpha -> eta -> real` is continuous at
`x0` and `f x0 = 0`, then eventually in `nhds x0`,
`aoyagiCoordinateSquareSum (f x) <= 1`.  The two-family theorem applies this
to a disjoint-sum family and proves eventual
`squareSum(f x) + squareSum(g x) <= 1`.  The coordinatewise variants first
assemble per-coordinate centering and continuity into Pi-valued centered
continuity.

Boundary: ambient real finite topology only.  This is not yet specialised to
the p. 13 source-data maps or weakened to the source-rank stratum, and it does
not prove analytic regular-coordinate status, source-rank openness,
Fubini/polar regular-variable shift, chart coverage, Jacobian compatibility,
normal crossings, pole order, or RLCT.

## 2026-06-24 A2 regular-coordinate F2/F3 smallness projection

Reproduction:
`reproduction-a2-regular-coordinate-f2-f3-smallness-projection.md`.
Statement card:
`statement-card-a2-regular-coordinate-f2-f3-smallness-projection.md`.
Review:
`review-a2-regular-coordinate-f2-f3-smallness-projection.md`.

Lean now projects the generic two-family smallness theorem through the p. 13
regular-coordinate tags:

```text
AoyagiRegularBlockCoordinateIndex.f2_f3_squareSum_eventually_le_one_of_forall_centered_continuousAt
```

For a finite real tagged family
`coord : alpha -> AoyagiRegularBlockCoordinateIndex iota mu nu -> real`, if
every tagged coordinate is centered and continuous at `x0`, then eventually in
`nhds x0` the square-sums of the `F2` and `F3` tagged subfamilies have total at
most `1`.

Boundary: finite real tag projection only.  This is not yet specialised to the
actual fixed-base source-data map and not weakened to a source-rank stratum.
It does not prove analytic regular-coordinate status, source-rank openness,
Fubini/polar regular-variable shift, chart coverage, Jacobian compatibility,
normal crossings, pole order, or RLCT.

Xhigh review passed.  The reviewer confirmed the narrow theorem shape, the
focused module build, and the need for explicit nested-sum type annotations for
the `F2` and `F3` tags.

## 2026-06-24 A2 fixed-base regular-coordinate F2/F3 smallness

Reproduction:
`reproduction-a2-fixed-base-regular-coordinate-f2-f3-smallness.md`.
Statement card:
`statement-card-a2-fixed-base-regular-coordinate-f2-f3-smallness.md`.
Review:
`review-a2-fixed-base-regular-coordinate-f2-f3-smallness.md`.

Lean now specialises the p. 13 `F2/F3` smallness theorem to the actual real
fixed-base regular-coordinate map in
`PaperEndpointFixedBaseRegularCoordinateSourceData`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one
PaperEndpointFixedBaseRegularCoordinateSourceData.regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one_nhdsWithin_source
```

The ambient theorem uses the source-data package's centered-continuous
Pi-valued regular-coordinate map.  The relative theorem is only a weakening to
`nhdsWithin` the source-rank stratum.

Boundary: real finite topology for the actual fixed-base scalar coordinate
map.  This does not prove source-rank openness, analytic coordinate status,
source coverage, analytic ideal transport, Fubini/polar regular-variable
shift, normal crossings, pole order, or RLCT.

## 2026-06-24 A2 fixed-base literal-cleaned square-sum comparison

Reproduction:
`reproduction-a2-fixed-base-literal-cleaned-square-sum-comparison.md`.
Statement card:
`statement-card-a2-fixed-base-literal-cleaned-square-sum-comparison.md`.
Review:
`review-a2-fixed-base-literal-cleaned-square-sum-comparison.md`.

Lean now defines the actual fixed-base literal signed/corrected p. 13 scalar
coordinate family:

```text
paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
```

and proves that, under real
`PaperEndpointFixedBaseRegularCoordinateSourceData`, its square-sum and the
cleaned `paperEndpointFixedBaseProductDifferenceCoordinateMap` square-sum are
eventually mutually bounded by factor `2`, both in ambient `nhds x0` and in
the source-rank `nhdsWithin` filter.  Directional projection theorems expose
each inequality separately.

Boundary: finite real square-sum comparison only.  This does not prove
analytic ideal transport, chart construction, source coverage, source-rank
openness, normal crossings, pole order, or RLCT.

## 2026-06-24 A2 one-step determinant-chart coordinate equivalence

Reproduction:
`reproduction-a2-one-step-determinant-chart-coordinate-equivalence.md`.
Statement card:
`statement-card-a2-one-step-determinant-chart-coordinate-equivalence.md`.
Review:
`review-a2-one-step-determinant-chart-coordinate-equivalence.md`.

Lean now topologizes the raw and chart one-step product-reduction coordinate
structures by their matrix-field product topologies and proves the p. 13
one-step determinant-chart coordinate change is a homeomorphism:

```text
ProductReductionStepRawCoordinates.continuous_toChart_detChart_subtype
ProductReductionStepRawCoordinates.continuous_detChart_toChart
ProductReductionStepChartCoordinates.continuous_toRaw_detChart_subtype
ProductReductionStepChartCoordinates.continuous_detChart_toRaw
productReductionStepCoordinate_detChart_homeomorph
```

The theorem uses the existing algebraic inverse identities from
`ProductReduction.lean` and the matrix-inversion continuity helper in
`ChartTopology.lean`.  The right-inverse proof passes the chart determinant
pair in the required order: `A1` unit first, then `Ctop` unit.

Boundary: finite determinant-chart topology only.  This does not prove
analytic regularity, an analytic Jacobian determinant calculation,
source-rank openness, source coverage, ideal-germ transport, a
regular-suspension certificate, normal crossings, pole order, or RLCT.

## 2026-06-24 A2 p.13 source regular-suspension boundary

Reproduction:
`reproduction-a2-p13-source-regular-suspension-boundary.md`.
Statement card:
`statement-card-a2-p13-source-regular-suspension-boundary.md`.
Review:
`review-a2-p13-source-regular-suspension-boundary.md`.

The source audit pins the p. 13 split: after Theorem 3 the literal
target-centered block is
`[C1-Er, -F2; -F3, prod_s C^(s)-F3F2]`, while the reduced residual family is
the entries of `D = prod_s C^(s)`.  Aoyagi then states the displayed RLCT
shift by the regular count, but pp. 10-14 do not give the analytic
regular-suspension construction, Jacobian/prior computation, coverage, or
normal-crossing lift.  The p. 14 reduction to `r(s)=r` is also via Theorem 4,
not Theorem 3 alone.

Lean now adds only the reviewed source-side wrapper

```text
exists_paperEndpointFixedBaseRegularCoordinateSourceData_literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two_nhdsWithin_source_of_rank_eq
```

in `RegularSuspensionCoordinates.lean`.  From real rank/source data it chooses
the existing fixed-base regular-coordinate source data and returns the existing
source-rank-stratum factor-`2` comparison between the literal p. 13 square-sum
and the cleaned square-sum.

Boundary: source-data packaging plus finite real square-sum comparison only.
No analytic regular-coordinate chart, source coverage, ideal-germ transport,
Jacobian/prior shift, full normal-crossing certificate, Theorem 4 reduction,
pole order, or RLCT equality is proved.

## 2026-06-24 A2 supplied regular-suspension extraction projection

Reproduction:
`reproduction-a2-supplied-regular-suspension-extraction-projection.md`.
Statement card:
`statement-card-a2-supplied-regular-suspension-extraction-projection.md`.
Review:
`review-a2-regular-suspension-projections-and-loss-shape.md`.

Lean now hardens the supplied full-certificate boundary in
`RegularSuspensionInterface.lean`:

```text
AoyagiSuppliedRegularSuspensionCertificate.
  lambda_eq_reduced_add_half_regularCount
AoyagiSuppliedRegularSuspensionCertificate.
  poleOrder_eq_reduced_exponentOrder
AoyagiSuppliedRegularSuspensionCertificate.
  lambda_eq_reduced_add_regularTerm
AoyagiSuppliedRegularSuspensionCertificate.
  lambda_and_poleOrder_eq_reduced_add_regularTerm
```

These project `Cfull.ExtractionHypothesis lambda poleOrder` through the
supplied finite equality
`Cfull.exponentData = Cred.exponentData.jacobianPriorLossShift regularCount`.
The result is that the external `lambda` equals the reduced finite minimum
plus `regularCount/2`, the external `poleOrder` equals the reduced finite
order, and under the p.13 count with endpoint bounds the shift is Aoyagi's
displayed `aoyagiTheorem2RegularTerm`.

Boundary: extraction remains on `Cfull`.  This does not construct `Cfull`,
extract from `Cred`, prove Fubini/polar regular-variable shift, prove Aoyagi
Lemma 1 or Theorem 4, produce normal crossings, or prove an RLCT theorem beyond
the supplied full-certificate extraction hypothesis.

## 2026-06-24 A2 source-stratum literal regular/residual square-sum

Reproduction:
`reproduction-a2-source-stratum-literal-regular-residual-square-sum.md`.
Statement card:
`statement-card-a2-source-stratum-literal-regular-residual-square-sum.md`.
Review:
`review-a2-regular-suspension-projections-and-loss-shape.md`.

Lean now proves

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  literal_regular_add_residual_squareSum_eventually_factor_two_nhdsWithin_source
```

in `RegularSuspensionCoordinates.lean`.  It composes the existing
source-stratum literal/cleaned factor-`2` comparison with the cleaned
product-difference square-sum split:

```text
cleanedSquareSum = regularBlockSquareSum + residualBlockSquareSum.
```

Thus, eventually on the source-rank stratum, the literal p.13 square-sum is
mutually bounded by factor `2` with
`regularBlockSquareSum + residualBlockSquareSum`.

Boundary: finite source-side square-sum comparison only.  No analytic chart,
Fubini/polar shift, normal-crossing certificate construction, pole order, or
RLCT extraction is proved.

## 2026-06-24 A2 regular square-suspension integrability target

Reproduction target:
`reproduction-a2-regular-square-suspension-integrability-target.md`.

The next genuine analytic target is now pinned as an independent Euclidean
product-coordinate theorem: if a full loss is locally comparable to
`|u|^2 + g(y)` with bounded positive density on `R^k x R^m`, then adding the
regular square variables shifts the local power-integrability threshold by
`k/2`.  The proof route is Fubini plus polar-coordinate estimates for

```text
integral_0^eps r^(k-1) (r^2 + a)^(-t) dr.
```

This theorem is not yet formalised.  It is separate from normal-crossing
extraction and still needs actual Aoyagi p.13 product-chart/density hypotheses
before it can be applied.

## 2026-06-24 A2 one-sided regular-suspension integrability

Reproduction:
`reproduction-a2-one-sided-regular-suspension-integrability.md`.
Statement card:
`statement-card-a2-one-sided-regular-suspension-integrability.md`.
Review:
`review-a2-one-sided-regular-suspension-integrability.md`.

Lean now proves the first narrow ENNReal product-measure brick toward the
regular-square theorem:

```text
lintegral_rpow_neg_add_right_le_prod_fst
lintegral_rpow_neg_add_right_lt_top_of_lintegral_rpow_neg_lt_top
lintegral_rpow_neg_add_right_restrict_lt_top_of_lintegral_rpow_neg_restrict_lt_top
```

The pointwise estimate is

```text
(a x + q y)^(-s) <= (a x)^(-s)
```

for `s >= 0`, proved in `ENNReal` by monotonicity of positive powers and
inverse order reversal.  If the extra measure is finite and the base integral
of `(a x)^(-s)` is finite, Tonelli's product formula gives finiteness of the
integral after adding the extra nonnegative term.  The restricted version uses
`nu t < infinity` to make `nu.restrict t` finite.

Boundary: one-sided finite-factor integrability preservation only.  No
threshold definition, no `+ k/2` shift, no polar-coordinate estimate, no
bounded-density theorem, no p.13 analytic chart or Jacobian theorem, no
normal-crossing construction, no pole-order theorem, and no RLCT theorem is
proved.

## 2026-06-24 A2 radial finite-side integrability

Reproduction:
`reproduction-a2-radial-finite-side-integrability.md`.
Statement card:
`statement-card-a2-radial-finite-side-integrability.md`.
Review:
`review-a2-radial-finite-side-integrability.md`.

Lean now proves the first punctured radial finite-side estimate for the
regular-square theorem in `RegularSuspensionIntegrability.lean`:

```text
integrable_norm_rpow_neg_indicator_Ioo
integrable_norm_sq_add_rpow_neg_indicator_Ioo
lintegral_ofReal_norm_sq_add_rpow_neg_indicator_Ioo_lt_top
```

The radial model uses Mathlib's additive-Haar radial integrability theorem to
reduce

```text
x |-> 1_(0,R)(||x||) * ||x||^(-t)
```

to one-dimensional integrability of `r^(d-1-t)` on `(0,R)`, hence proves
finiteness under `t < d = finrank_R(E)`.  The shifted quadratic estimate
dominates

```text
(||x||^2 + a)^(-s)
```

by `||x||^(-2s)` on the punctured interval, for `a >= 0` and `s >= 0`, and
therefore proves integrability under `2*s < d`.  The final theorem only
transfers the real-valued integrability statement to finiteness of the
`ENNReal.ofReal` lower integral.

Boundary: finite side on `1_(0,R)(||x||)` only.  No ball/null-origin transfer,
endpoint theorem, lower/divergence theorem, uniform asymptotic in `a`,
bounded-density theorem, product-coordinate `+k/2` threshold, Aoyagi p.13
analytic chart/Jacobian theorem, normal-crossing construction, pole order, or
RLCT theorem is proved.

## 2026-06-24 A2 null-origin radial integrability

Reproduction:
`reproduction-a2-null-origin-radial-integrability.md`.
Statement card:
`statement-card-a2-null-origin-radial-integrability.md`.
Review:
`review-a2-null-origin-radial-integrability.md`.

Lean now removes the radial puncture at the origin by a.e. congruence in
`RegularSuspensionIntegrability.lean`:

```text
ae_eq_norm_indicator_Ioo_Iio
integrable_norm_sq_add_rpow_neg_indicator_Iio
lintegral_ofReal_norm_sq_add_rpow_neg_indicator_Iio_lt_top
norm_sq_add_rpow_neg_indicator_ball_eq_indicator_Iio
integrable_norm_sq_add_rpow_neg_indicator_ball
lintegral_ofReal_norm_sq_add_rpow_neg_indicator_ball_lt_top
```

The primitive theorem says that for a nonatomic measure, the radial
indicator-extensions by zero for `(0,R)` and `(-infinity,R)` agree almost
everywhere.  The only possible disagreement is at `x=0`, which is null.
The quadratic integrability and `ENNReal.ofReal` lower-integral results then
transfer from the punctured radial theorem under the same finite-side
hypotheses `R>0`, `a>=0`, `s>=0`, and `2*s < finrank`.  The open-ball wrapper
is a pointwise rewrite of `x in Metric.ball 0 R` as `||x|| < R`.

Boundary: a.e. representative transfer only.  No pointwise regularity at the
origin, closed-ball theorem, boundary-sphere nullity, endpoint theorem,
lower/divergence theorem, uniform asymptotic in `a`, bounded-density theorem,
product-coordinate `+k/2` threshold, Aoyagi p.13 analytic chart/Jacobian
theorem, normal-crossing construction, pole order, or RLCT theorem is proved.

## 2026-06-24 A2 product below-critical integrability

Reproduction:
`reproduction-a2-product-below-critical-integrability.md`.
Statement card:
`statement-card-a2-product-below-critical-integrability.md`.
Review:
`review-a2-product-below-critical-integrability.md`.

Lean now proves the first product-coordinate finite-side theorem in
`RegularSuspensionIntegrability.lean`:

```text
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top
```

For a finite base measure `mu`, additive Haar measure `nu` on a nontrivial
finite-dimensional real normed regular space `E`, an a.e. nonnegative base
term `a : alpha -> R`, and `2*s < finrank_R(E)`, the lower integral over
`alpha x E` of

```text
ENNReal.ofReal (1_{ball(0,R)}(u) * (a(x)+||u||^2)^(-s))
```

is finite.  The proof uses a.e. domination by the `a=0` regular-ball integrand:
away from the regular origin, `(a(x)+||u||^2)^(-s) <= (||u||^2)^(-s)`.
Tonelli then factors the majorant as `mu(univ)` times the already-proved
regular open-ball integral.

Boundary: below-regular-critical finite side only.  No `+dim(E)/2` threshold
shift, no theorem for `s >= dim(E)/2`, no endpoint, lower/divergence, uniform
asymptotic in `a`, bounded-density/prior theorem, Aoyagi p.13 analytic
chart/Jacobian theorem, normal-crossing construction, pole order, or RLCT
theorem is proved.

## 2026-06-25 A2 product bounded-away integrability

Reproduction:
`reproduction-a2-product-bounded-away-integrability.md`.
Statement card:
`statement-card-a2-product-bounded-away-integrability.md`.
Review:
`review-a2-product-bounded-away-integrability.md`.
Threshold-shift Lean-route probe:
`scout-a2-regular-square-threshold-shift-lean-route.md`.

Lean now proves the product-coordinate regular-ball estimate away from the
residual zero set in `RegularSuspensionIntegrability.lean`:

```text
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_ae_pos_le
```

For a finite base measure `mu`, additive Haar measure `nu` on a nontrivial
finite-dimensional real normed regular space `E`, a positive constant
`epsilon`, an a.e. lower bound `epsilon <= a(x)`, and `s>=0`, the lower
integral over `alpha x E` of

```text
ENNReal.ofReal (1_{ball(0,R)}(u) * (a(x)+||u||^2)^(-s))
```

is finite.  The proof bounds the integrand by `epsilon^(-s)` on the regular
ball, uses `measure_ball_lt_top`, and factors the constant-ball majorant by
`lintegral_prod_mul`.

Boundary: away-from-zero finite side only.  No singular-base bound where
`a(x)` approaches zero, no `+dim(E)/2` threshold shift, no endpoint,
lower/divergence, uniform asymptotic in `a`, bounded-density/prior theorem,
Aoyagi p.13 analytic chart/Jacobian theorem, normal-crossing construction,
pole order, or RLCT theorem is proved.  The next analytic target is the
Japanese-bracket/Haar-scaling supercritical fiber bound recorded in the scout
route probe.

## 2026-06-25 A2 Japanese-bracket supercritical integrability

Reproduction:
`reproduction-a2-japanese-bracket-supercritical-integrability.md`.
Statement card:
`statement-card-a2-japanese-bracket-supercritical-integrability.md`.
Review:
`review-a2-japanese-bracket-supercritical-integrability.md`.

Lean now proves the global supercritical finite-side model package in
`RegularSuspensionIntegrability.lean`:

```text
integrable_one_add_norm_sq_rpow_neg
lintegral_ofReal_one_add_norm_sq_rpow_neg_lt_top
lintegral_ofReal_norm_sq_add_pos_rpow_neg_lt_top
```

If `finrank_R(E)/2 < s`, the Japanese-bracket model
`(1+||x||^2)^(-s)` is integrable and has finite `ENNReal.ofReal` lower
integral.  For each fixed `a>0`, `(a+||x||^2)^(-s)` has finite lower integral
by comparison with `min(a,1)^(-s)*(1+||x||^2)^(-s)`.

Boundary: fixed-parameter supercritical finite side only.  No sharp
`a^(finrank/2-s)` dependence, no base-product theorem where `a(y)` approaches
zero, no `+dim(E)/2` threshold shift, no endpoint, lower/divergence, uniform
asymptotic in `a`, bounded-density/prior theorem, Aoyagi p.13 analytic
chart/Jacobian theorem, normal-crossing construction, pole order, or RLCT
theorem is proved.

## 2026-06-25 A2 sharp positive-parameter fiber scaling

Reproduction:
`reproduction-a2-sharp-positive-parameter-fiber-scaling.md`.
Statement card:
`statement-card-a2-sharp-positive-parameter-fiber-scaling.md`.
Review:
`review-a2-sharp-positive-parameter-fiber-scaling.md`.

Lean now proves the sharp fixed-positive-parameter scaling package in
`RegularSuspensionIntegrability.lean`:

```text
lintegral_comp_inv_smul_eq_mul_addHaar
ofReal_add_norm_sq_pos_rpow_neg_eq_mul_one_add_norm_sq_inv_sqrt_smul
lintegral_ofReal_add_norm_sq_pos_rpow_neg_eq_scale
lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball_le_scale
lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball_lt_top_of_supercritical
```

For additive Haar measure on a finite-dimensional real normed space and
`a>0`, the whole-space lower integral of `(a+||u||^2)^(-s)` is exactly
`a^(finrank/2-s)` times the Japanese-bracket lower integral.  The equality is
only Haar scaling and positive real-power algebra; the supercritical
hypothesis `finrank/2<s` is used in the last theorem only to make the
Japanese-bracket constant finite.  Restricting to `ball(0,R)` gives the
sharp ball bound by monotonicity.

Boundary: fixed positive parameter only.  No variable-base product theorem
where `a(x)` approaches zero, no proof that the residual base has finite
`a(x)^(finrank/2-s)` integral, no full `+dim(E)/2` threshold shift, no
endpoint or divergent side, no uniform asymptotic statement, no
bounded-density/prior theorem, no Aoyagi p.13 analytic chart/Jacobian theorem,
no normal-crossing construction, pole order, or RLCT theorem is proved.

## 2026-06-25 A2 variable-base product fiber integrability

Reproduction:
`reproduction-a2-variable-base-product-fiber-integrability.md`.
Statement card:
`statement-card-a2-variable-base-product-fiber-integrability.md`.
Review:
`review-a2-variable-base-product-fiber-integrability.md`.

Lean now proves the first variable-base product theorem using the sharp
fiber estimate:

```text
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_scale
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_ae_pos_of_base_lt_top
```

If `a(x)>0` for base-a.e. `x`, `finrank_R(E)/2<s`, and

```text
∫⁻ x, ENNReal.ofReal (a(x)^(finrank_R(E)/2-s)) dmu < infinity,
```

then the product lower integral of `(a(x)+||u||^2)^(-s)` over
`alpha x ball(0,R)` is finite.  The proof uses `lintegral_prod_le`, then the
fixed-fiber sharp bound for a.e. base point, and finally the finite
base-power hypothesis times the finite Japanese-bracket constant.  No finite
base measure or measurability hypothesis on `a` is required.

Boundary: this does not prove the residual-base hypothesis for Aoyagi's
actual residual coordinates, does not cover a positive-measure zero set of
`a`, and does not prove endpoint/divergence, bounded-density/prior transport,
p.13 analytic chart/Jacobian construction, normal crossings, pole order, or
RLCT.

## 2026-06-25 A2 residual-power threshold-shift bridge

Reproduction:
`reproduction-a2-residual-power-threshold-shift-bridge.md`.
Statement card:
`statement-card-a2-residual-power-threshold-shift-bridge.md`.
Review:
`review-a2-residual-power-threshold-shift-bridge.md`.

Lean now proves the finite-side threshold-shift form of the variable-base
product theorem:

```text
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_residual_power_scale
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
```

If `a(x)>0` for base-a.e. `x`, `0<t`, and

```text
∫⁻ x, ENNReal.ofReal (a(x)^(-t)) dmu < infinity,
```

then the product lower integral of
`(a(x)+||u||^2)^(-(t+finrank_R(E)/2))` over `alpha x ball(0,R)` is finite.
This is the substitution `s=t+finrank_R(E)/2` in the variable-base theorem:
`0<t` gives `finrank_R(E)/2<s`, and `finrank_R(E)/2-s=-t`.

Boundary: this does not prove that Aoyagi's reduced residual coordinates
satisfy the residual negative-power hypothesis, does not cover a
positive-measure zero set of `a`, and does not prove endpoint/divergence,
threshold equality, bounded-density/prior transport, p.13 analytic
chart/Jacobian construction, normal crossings, pole order, or RLCT.

## 2026-06-25 A2 residual square-sum integrability socket

Reproduction:
`reproduction-a2-residual-square-sum-integrability-socket.md`.
Statement card:
`statement-card-a2-residual-square-sum-integrability-socket.md`.
Review:
`review-a2-residual-square-sum-integrability-socket.md`.

Lean now specialises the residual-power threshold-shift bridge to Aoyagi's
finite coordinate square-sum convention:

```text
lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_le_residual_power_scale
lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
lintegral_ofReal_residualBlockSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
```

The generic theorem uses
`a(x)=aoyagiCoordinateSquareSum (b x)`.  The residual-block theorem uses
`a(x)=aoyagiCoordinateSquareSum (AoyagiResidualBlockCoordinateIndex.value (D x))`.
In both cases, a.e. positivity and finite residual negative `t`-power lower
integral are hypotheses.

Boundary: this is only an interface socket for the p. 13 residual square-sum.
It does not prove positivity or residual negative-power integrability for
Aoyagi's reduced residual coordinates, does not cover a positive-measure zero
set, and does not prove endpoint/divergence, threshold equality,
bounded-density/prior transport, p.13 analytic chart/Jacobian construction,
normal crossings, pole order, or RLCT.

## 2026-06-25 A2 Euclidean coordinate square-sum base integrability

Reproduction:
`reproduction-a2-euclidean-coordinate-square-sum-base-integrability.md`.
Statement card:
`statement-card-a2-euclidean-coordinate-square-sum-base-integrability.md`.
Review:
`review-a2-euclidean-coordinate-square-sum-base-integrability.md`.

Lean now proves the local negative-power base theorem for the free Euclidean
residual-coordinate model in `RegularSuspensionSquareSumIntegrability.lean`:

```text
aoyagiEuclideanCoordinateSquareSum_pos_of_ne_zero
ae_aoyagiEuclideanCoordinateSquareSum_pos
ae_aoyagiEuclideanCoordinateSquareSum_pos_restrict
lintegral_ofReal_euclideanCoordinateSquareSum_rpow_neg_indicator_ball_lt_top
lintegral_ofReal_euclideanCoordinateSquareSum_rpow_neg_restrict_ball_lt_top
lintegral_ofReal_euclideanCoordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top
```

For `x : EuclideanSpace ℝ eta`, the finite square-sum
`aoyagiCoordinateSquareSum (fun i => x i)` is `||x||^2`.  Hence it is
positive away from the origin, positive a.e. for nonatomic measures, and has
finite local negative `t`-power lower integral on `ball(0,R)` when
`R>0`, `0<=t`, and `2*t < card eta`.  The final theorem composes this base
integrability with the existing square-model product socket.

Boundary: this is only the free Euclidean coordinate model.  It does not prove
residual-base integrability for Aoyagi's product residual `D=prod_s C^(s)`,
does not show that the p.13 residual product map is locally equivalent to free
coordinates, does not cover zero-dimensional residual blocks, and does not
prove endpoint/divergence, threshold equality, bounded-density/prior
transport, p.13 analytic chart/Jacobian construction, normal crossings, pole
order, or RLCT.

## 2026-06-25 A2 negative-power lower-bound comparison

Reproduction:
`reproduction-a2-negative-power-lower-bound-comparison.md`.
Statement card:
`statement-card-a2-negative-power-lower-bound-comparison.md`.
Review:
`review-a2-negative-power-lower-bound-comparison.md`.

Lean now proves a reusable residual-base comparison theorem in
`RegularSuspensionIntegrability.lean`:

```text
lintegral_ofReal_rpow_neg_lt_top_of_ae_pos_of_ae_const_mul_le
```

If `c>0`, `0<=t`, `a(x)>0` a.e., `c*a(x)<=b(x)` a.e., and

```text
∫⁻ x, ENNReal.ofReal (a(x)^(-t)) dmu < infinity,
```

then

```text
∫⁻ x, ENNReal.ofReal (b(x)^(-t)) dmu < infinity.
```

The pointwise calculation is
`b^(-t) <= (c*a)^(-t) = c^(-t)*a^(-t)`, using nonpositive exponent
monotonicity and positive-factor multiplicativity.

Boundary: this is only a comparison theorem.  It does not construct a lower
bound for Aoyagi's product residual, does not prove monomial integrability,
does not prove a finite chart cover theorem, and does not prove
bounded-density/prior transport, endpoint/divergence, threshold equality, p.13
analytic chart/Jacobian construction, normal crossings, pole order, or RLCT.

## 2026-06-25 A2 positive-box monomial integrability

Reproduction:
`reproduction-a2-positive-box-monomial-integrability.md`.
Statement card:
`statement-card-a2-positive-box-monomial-integrability.md`.
Review:
`review-a2-positive-box-monomial-integrability.md`.

Lean now proves the positive-box monomial factor theorem in
`MonomialChartIntegrability.lean`:

```text
lintegral_ofReal_rpow_restrict_Ioo_lt_top
lintegral_ofReal_monomialFactor_restrict_Ioo_lt_top
lintegral_ofReal_fintype_rpow_positiveBox_lt_top
lintegral_ofReal_fintype_monomialFactor_positiveBox_lt_top
```

The general product theorem says that for finite `i`, `R_i>0`, and
`p_i>-1`,

```text
int^- x, ofReal(prod_i x_i^(p_i))
  d Measure.pi (i |-> volume.restrict (0,R_i))
<
infinity.
```

The Aoyagi-specialized theorem sets `p_i=h_i-2*t*k_i`, so the strict
inequality `2*t*k_i<h_i+1` gives the required `p_i>-1`.

Boundary: this is the positive-coordinate model only.  It does not prove a
residual-loss lower bound, density/prior upper bound, signed-box
absolute-value theorem, finite chart cover, endpoint/divergence, threshold
equality, p.13 analytic chart/Jacobian construction, normal crossings, pole
order, or RLCT.

## 2026-06-25 A2 positive-box monomial domination

Reproduction:
`reproduction-a2-positive-box-monomial-domination.md`.
Statement card:
`statement-card-a2-positive-box-monomial-domination.md`.
Review:
`review-a2-positive-box-monomial-domination.md`.

Lean now proves direct positive-box monomial domination transfer in
`MonomialChartIntegrability.lean`:

```text
lintegral_ofReal_le_const_mul_fintype_rpow_positiveBox_lt_top
lintegral_ofReal_le_const_mul_fintype_monomialFactor_positiveBox_lt_top
```

If an arbitrary real integrand `f` is a.e. bounded above by
`A * prod_i x_i^(p_i)` on the positive-box product measure, with `0<=A`,
`R_i>0`, and `p_i>-1`, then `int^- ofReal(f)` is finite.  The Aoyagi wrapper
uses `p_i=h_i-2*t*k_i` under the strict inequalities `2*t*k_i<h_i+1`.

Boundary: this is only a domination-transfer theorem.  It does not derive the
upper bound from residual-loss and density estimates, does not handle
signed/absolute-value boxes, and does not prove chart coverage, endpoint or
divergent behavior, threshold equality, p.13 analytic chart/Jacobian
construction, normal crossings, pole order, or RLCT.

## 2026-06-25 A2 positive-box residual/density comparison

Reproduction:
`reproduction-a2-positive-box-residual-density-comparison.md`.
Statement card:
`statement-card-a2-positive-box-residual-density-comparison.md`.
Review:
`review-a2-positive-box-residual-density-comparison.md`.

Lean now proves the positive-box bridge from separate supplied loss/density
bounds to finite lower-integral control in `MonomialChartIntegrability.lean`:

```text
ae_forall_pos_measure_pi_restrict_Ioo
loss_rpow_neg_mul_density_le_const_mul_monomialFactor_of_pos
lintegral_ofReal_loss_rpow_neg_mul_density_positiveBox_lt_top
```

The finite theorem assumes `c>0`, `C>=0`, `t>=0`, `R_i>0`, the strict
inequalities `2*t*k_i<h_i+1`, and the a.e. positive-box bounds

```text
c * prod_i x_i^(2*k_i) <= loss(x),
0 <= density(x),
density(x) <= C * prod_i x_i^(h_i).
```

It concludes

```text
int^- x, ofReal(loss(x)^(-t) * density(x)) < infinity
```

for the product positive-box measure.  The proof uses a.e. coordinate
positivity, real-power order reversal for exponent `-t`, product power
arithmetic on positive coordinates, and the landed monomial domination theorem.

Boundary: this is still positive-box comparison only.  It does not handle
signed or absolute-value boxes, does not prove the supplied bounds for
Aoyagi's actual charts, and does not prove analytic density/Jacobian
transport, chart coverage, endpoint or divergent behavior, threshold equality,
p.13 analytic chart/Jacobian construction, normal crossings, pole order, or
RLCT.

## 2026-06-25 A2 p.13 half loss lower bound

Reproduction:
`reproduction-a2-p13-half-loss-lower-bound.md`.
Statement card:
`statement-card-a2-p13-half-loss-lower-bound.md`.

Lean now proves the lower-bound corollary of the p.13 source-stratum
literal/cleaned factor-`2` comparison in `RegularSuspensionCoordinates.lean`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source
PaperEndpointFixedBaseRegularCoordinateSourceData.const_mul_literal_squareSum_eventually_le_loss_to_half_regular_add_residual_squareSum_nhdsWithin_source
exists_paperEndpointFixedBaseRegularCoordinateSourceData_literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source_of_rank_eq
```

The first theorem proves eventually on the fixed-base source-rank stratum

```text
(1/2) * (regularSquareSum + residualSquareSum) <= literalSquareSum.
```

The second composes this with a supplied ambient comparison
`c * literalSquareSum <= loss`, with `c>=0`, to get

```text
(c/2) * (regularSquareSum + residualSquareSum) <= loss.
```

Boundary: this is finite p.13 square-sum bookkeeping only.  It does not prove
the original DLN loss comparison, analytic coordinate status, chart coverage,
Jacobian/prior density transport, regular-suspension additivity, normal
crossings, pole order, or RLCT.

## 2026-06-25 A2 signed-box model-loss adapter

Reproduction:
`reproduction-a2-signed-box-model-loss-adapter.md`.
Statement card:
`statement-card-a2-signed-box-model-loss-adapter.md`.

Lean now proves the generic signed-box comparison adapter in
`MonomialChartIntegrability.lean`:

```text
lintegral_ofReal_loss_rpow_neg_mul_density_signedBox_lt_top_of_modelLoss_le_const_mul_loss
```

If `c*M <= modelLoss` and `modelLoss <= K*loss` a.e. with `c>0` and `K>0`,
then `(c/K)*M <= loss` a.e.; the theorem delegates to the existing signed-box
residual/density comparison with constant `c/K`.

Boundary: this is comparison plumbing only.  It does not construct the model
loss, convert p.13 source-filter facts into signed-box a.e. chart hypotheses,
prove density/Jacobian transport, chart coverage, normal crossings, pole
order, or RLCT.

## 2026-06-25 A2 regular-square bounded-density wrapper

Reproduction:
`reproduction-a2-regular-square-bounded-density-wrapper.md`.
Statement card:
`statement-card-a2-regular-square-bounded-density-wrapper.md`.

Lean now proves the bounded-density finite-side regular-square-suspension
wrapper in `RegularSuspensionSquareSumIntegrability.lean`:

```text
lintegral_ofReal_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_residual_power_lt_top
lintegral_ofReal_loss_rpow_neg_mul_density_residualBlockSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_residual_power_lt_top
```

The theorem consumes supplied product-measure hypotheses:

```text
0 < aoyagiCoordinateSquareSum (b x)  a.e.,
int^- x, ofReal(aoyagiCoordinateSquareSum(b x)^(-t)) < infinity,
c * (aoyagiCoordinateSquareSum(b x)+||u||^2) <= loss(x,u),
0 <= density(x,u),
density(x,u) <= C
```

on the regular ball, with `c>0`, `C>=0`, and `t>0`.  It concludes finite
lower integral of `loss^(-(t+dim(E)/2))*density` over the regular ball.

Boundary: this is a one-sided finite-integrability wrapper only.  It does not
prove Aoyagi's p.13 analytic product chart, the lower loss bound,
density/Jacobian transport, residual integrability, endpoint/divergent-side
behavior, threshold equality, normal crossings, pole order, or RLCT.

## 2026-06-25 A2 p.13 regular-coordinate bounded-density adapter

Reproduction:
`reproduction-a2-p13-regular-coordinate-bounded-density-adapter.md`.
Statement card:
`statement-card-a2-p13-regular-coordinate-bounded-density-adapter.md`.
Review:
`review-a2-p13-regular-coordinate-bounded-density-adapter.md`.

Lean now specialises the bounded-density finite-side regular-square theorem to
the fixed-base p.13 regular coordinate index in
`RegularSuspensionSquareSumIntegrability.lean`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.regularCoordinateEuclidean_finrank_eq_regularVariableCount
PaperEndpointFixedBaseRegularCoordinateSourceData.lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residual_power_lt_top
```

The first theorem rewrites the Euclidean regular-coordinate fiber dimension as
`aoyagiTheorem2RegularVariableCount N H r`.  The second consumes supplied
product-measure hypotheses for the residual square-sum, lower loss comparison,
and bounded density, with the p.13 regular term written as
`aoyagiCoordinateSquareSum (fun i => u i)`, and proves finite
lower-integrability at exponent
`t + aoyagiTheorem2RegularVariableCount N H r / 2`.

Boundary: this is source-facing finite-side adapter only.  It does not turn
source-stratum filter facts into product-measure a.e. hypotheses, construct
Aoyagi's p.13 analytic product chart, compare the original DLN loss with the
p.13 literal square-sum, prove Jacobian/prior density transport, prove
residual-base integrability, or prove endpoint/divergence, threshold equality,
normal crossings, pole order, or RLCT.

## 2026-06-25 A2 local measure handoff

Reproduction:
`reproduction-a2-local-measure-handoff.md`.
Statement card:
`statement-card-a2-local-measure-handoff.md`.
Review:
`review-a2-local-measure-handoff.md`.

Lean now proves a generic local support handoff in
`LocalMeasureHandoff.lean`:

```text
exists_open_ae_restrict_inter_of_eventually_nhdsWithin
exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin
```

If a property holds eventually in `nhdsWithin x0 S`, then after shrinking to
some open neighborhood `U` of `x0`, it holds almost everywhere for any measure
restricted to `U ∩ S`.  The product version pulls the same base a.e. fact back
along first projection for `(mu.restrict (U ∩ S)).prod nu`.

Boundary: this is only a filter-to-restricted-measure conversion.  It does not
construct a p.13 product chart, identify source coordinates with
residual-base plus regular-fiber product coordinates, compare losses, transport
density/Jacobian factors, prove integrability, produce normal crossings, pole
order, or RLCT.

## 2026-06-25 A2 regular-suspension local measure handoff

Reproduction:
`reproduction-a2-regular-suspension-local-measure.md`.
Statement card:
`statement-card-a2-regular-suspension-local-measure.md`.
Review:
`review-a2-regular-suspension-local-measure.md`.

Lean now packages two p.13 fixed-base source-filter comparisons as
restricted-measure a.e. facts in `RegularSuspensionLocalMeasure.lean`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_literal_regular_add_residual_squareSum_half_le
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_prod_fst_literal_regular_add_residual_squareSum_half_le
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_const_mul_literal_squareSum_le_loss_to_half_regular_add_residual_squareSum
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_prod_fst_const_mul_literal_squareSum_le_loss_to_half_regular_add_residual_squareSum
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_prod_p13RegularCoordinates_loss_density_bounds
PaperEndpointFixedBaseRegularCoordinateSourceData.residualNegPowerIntegrableOn
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top
```

The inputs are a measurable fixed-base source rank stratum and the already
proved p.13 `nhdsWithin` comparisons.  The conclusions produce an open
neighborhood `U` such that the corresponding inequality holds a.e. for
`mu.restrict (U ∩ sourceStratum)`, and in product form after replacing the
base point by `z.1`.

Boundary: the first product forms are first-coordinate handoffs only.  They do
not identify an auxiliary product fiber with p.13 regular coordinates and do
not derive the product-fiber `regularSquareSum(u)` lower bound needed by the
finite-side integrability adapter.  The uniform-in-fiber theorem transports
such loss/density bounds only when they are separately supplied on the source
filter.  None of these wrappers prove source-stratum measurability, chart
construction, original loss comparison, density/Jacobian transport, residual
positivity/integrability, normal crossings, pole order, or RLCT.

The last theorem handles the stronger case where the source filter already
contains uniform-in-fiber loss and density bounds for all p.13 regular
coordinate vectors in a ball.  It intersects those eventual facts and produces
the three product-measure a.e. hypotheses expected by the finite-side p.13
regular-coordinate adapter.  It still does not prove the uniform bounds,
residual positivity, or residual negative-power integrability.

The finite-integral bridge then adds the residual positivity and residual
negative-power integral as explicit source-stratum hypotheses, restricts them
from `sourceStratum` to `U ∩ sourceStratum`, and invokes the p.13 finite-side
bounded-density adapter.  Its conclusion is finite lower-integrability of
`loss^(-(t + regularCount/2))*density` over the local product measure.  It is
not a chart, original-loss, density/Jacobian, residual-integrability,
normal-crossing, pole-order, or RLCT theorem.

## 2026-06-25 A2 source-rank stratum measurability

Reproduction:
`reproduction-a2-source-rank-stratum-measurability.md`.
Statement card:
`statement-card-a2-source-rank-stratum-measurability.md`.
Review:
`review-a2-source-rank-stratum-measurability.md`.

Lean now proves the measurable-source-stratum input under continuous-family
hypotheses.  The finite matrix bridge in `ChartTopology.lean` proves rank
inequalities by determinantal minors, closedness of finite matrix `rank <= r`
loci, and measurability of exact-rank loci for continuous matrix families:

```text
matrix_rank_le_iff_forall_submatrix_det_eq_zero
isClosed_matrix_rank_le
measurableSet_matrix_rank_le_of_continuous
measurableSet_matrix_rank_eq_of_continuous
```

`ProductReductionBoundary.lean` then proves:

```text
measurableSet_paperEndpointFixedBaseEdgeRankStratum_of_continuous_finBasisMatrix
measurableSet_paperEndpointFixedBaseEdgeRankStratum_of_continuous
measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous_finBasisMatrix
measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous
```

Boundary: this is measurability, not exact-rank openness.  It requires
continuous finite-basis coordinate matrices, or a globally continuous edge
family `Cedge`; it does not derive global measurability from only a
`ContinuousAt Cedge x0` hypothesis.  It does not prove product-chart
construction, original-loss comparison, density/Jacobian transport, residual
positivity/integrability, normal crossings, pole order, or RLCT.

## 2026-06-25 A2 continuous density local bounds

Reproduction:
`reproduction-a2-continuous-density-local-bounds.md`.
Statement card:
`statement-card-a2-continuous-density-local-bounds.md`.
Review:
`review-a2-continuous-density-local-bounds.md`.

Lean now proves a generic topological density-boundedness handoff in
`LocalMeasureHandoff.lean`:

```text
exists_pos_radius_le_eventually_density_bounds_of_continuousAt_pos
exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
```

If a supplied density factor is continuous at `(x0,0)` and positive there,
then for some `R <= Rmax` and `C >= 0`, eventually near `x0` and for every
regular-coordinate vector in `ball(0,R)`, one has `0 <= density <= C`.

`RegularSuspensionLocalMeasure.lean` now also abstracts residual
source-restriction plumbing and gives a p.13 local finite-integral consumer:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_mono
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_continuousAt_pos_density
```

Boundary: this removes only the separate supplied density nonnegativity and
upper-bound filters once the transported density factor is supplied as positive
and continuous at the center.  It does not construct that density/Jacobian
factor, prove source-measure transport, prove the original-loss lower
comparison, or prove residual positivity/integrability, normal crossings, pole
order, or RLCT.

## 2026-06-25 A2 residual zero-locus handoff

Reproduction:
`reproduction-a2-residual-zero-locus-handoff.md`.
Statement card:
`statement-card-a2-residual-zero-locus-handoff.md`.
Review:
`review-a2-residual-zero-locus-handoff.md`.

Lean now proves the generic nonnegative-function handoff

```text
ae_pos_of_forall_nonneg_of_measure_zero_eq_zero
```

and applies it to the Aoyagi residual square-sum:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSquareSum_pos_ae_of_zero_set_null
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_mono_of_zero_set_null
```

This weakens the residual positivity input for downstream local finite-integral
bridges: instead of supplying `0 < residualSquareSum` a.e. directly, it is
enough to supply that the residual zero locus is null for the restricted source
measure.  The residual negative-power integral is still supplied, and the
zero-locus nullity itself is still a real chart/source-measure input.

Boundary: this does not prove residual zero-locus nullity, residual
negative-power integrability, source-measure transport, the original-loss lower
comparison, density/Jacobian transport, normal crossings, pole order, or RLCT.

## 2026-06-25 A2 residual source-measure map handoff

Reproduction:
`reproduction-a2-residual-source-measure-map-handoff.md`.
Statement card:
`statement-card-a2-residual-source-measure-map-handoff.md`.
Review:
`review-a2-residual-source-measure-map-handoff.md`.

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_measure_map
```

This is a source-measure transport constructor for the two residual inputs of
the p.13 local finite-integral bridge.  If `mu.restrict source` is supplied as
`Measure.map chart nu`, and residual positivity plus residual negative-power
integrability are supplied after pulling back along `chart`, then the source
side has:

```text
residualSquareSum > 0 a.e.,
residualNegPowerIntegrableOn ...
```

The proof uses `ae_map_iff` for the a.e. positivity statement and
`lintegral_map_le` for the lower-integral finiteness statement.

Boundary: this does not construct the chart, prove the pushforward identity,
compute a Jacobian, bound a density, prove monomial residual lower control,
compare the original DLN loss, produce normal crossings, compute pole order, or
extract an RLCT.

## 2026-06-25 A2 signed-box residual source-measure handoff

Opened a density-free residual source-measure slice after the generic
pushforward handoff.  Scope is only an unweighted signed-box product measure:
given a supplied pushforward identity and a supplied chart-side lower bound
`c * product_i |y_i|^(2*k_i) <= residualSq(chart y)`, derive chart-side
residual positivity and finite `ofReal(residualSq^(-t))` integral under
`t >= 0` and the strict coordinate conditions `2*t*k_i < 1`, then transport
the pair to the source.

Lean adds
`lintegral_ofReal_loss_rpow_neg_signedBox_lt_top` in
`MonomialChartIntegrability.lean` and
`residualSourceHypotheses_of_measure_map_signedBox_monomialLower` in
`RegularSuspensionLocalMeasure.lean`.

This remains unweighted product-measure plumbing.  It does not construct the
chart, prove the pushforward identity, transport Jacobian/density factors,
compare the original DLN loss, prove the density-weighted Aoyagi
`2*t*k_i < h_i+1` calculation for source measures, produce normal crossings,
or extract an RLCT.  Reproduction and statement card:
`reproduction-a2-signed-box-residual-source-measure-handoff.md` and
`statement-card-a2-signed-box-residual-source-measure-handoff.md`.
Review:
`review-a2-signed-box-residual-source-measure-handoff.md`.

Controller verified targeted builds for
`DLNFibre.DLN.Aoyagi.MonomialChartIntegrability` and
`DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure`, full `DLNFibre` build,
`scripts/sorries`, and `git diff --check`.  The full build still emits many
pre-existing style/Core warnings, but no failures.

## 2026-06-25 A2 weighted signed-box residual source-measure handoff

Opened the density-weighted version of the signed-box source-measure handoff.
Scope is still measure plumbing: if the source measure is supplied as the
pushforward of
`signedBox.withDensity (fun y => ENNReal.ofReal (density y))`, and the
residual lower bound plus density nonnegativity/monomial upper bound are
supplied a.e. on the underlying signed box, then the residual source
positivity/integrability pair follows under the Aoyagi-style strict
inequalities `2*t*k_i < h_i+1`.

Lean adds
`residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower`
in `RegularSuspensionLocalMeasure.lean`, reusing the previously landed
`lintegral_ofReal_loss_rpow_neg_mul_density_signedBox_lt_top` and generic
pushforward handoff.

This still does not construct the chart, prove the weighted pushforward
identity, compute or regularize a Jacobian/density factor, compare the original
DLN loss, produce normal crossings, compute pole order, or extract an RLCT.
Reproduction and statement card:
`reproduction-a2-weighted-signed-box-residual-source-measure-handoff.md` and
`statement-card-a2-weighted-signed-box-residual-source-measure-handoff.md`.
Review:
`review-a2-weighted-signed-box-residual-source-measure-handoff.md`.

Controller verified the focused
`DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure` build, full `DLNFibre`
build, `scripts/sorries`, and `git diff --check`.  The full build still emits
many pre-existing style/Core warnings, but no failures.

## 2026-06-25 A2 fixed-base triangular multiplier local boundedness

Reproduction:
`reproduction-a2-fixed-base-triangular-multiplier-local-boundedness.md`.
Statement card:
`statement-card-a2-fixed-base-triangular-multiplier-local-boundedness.md`.
Review:
`review-a2-fixed-base-triangular-multiplier-local-boundedness.md`.

Lean now proves generic local-boundedness helpers for continuous real
functions and finite square-sums, then applies them to the deterministic p.13
triangular multiplier product:

```text
paperEndpointFixedBaseTriangularMultiplierSquareSumProduct_exists_pos_eventually_le
paperEndpointFixedBaseTriangularMultiplierSquareSumProduct_exists_pos_eventually_le_nhdsWithin_source
```

The source-data consumer

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceSquareSum_selfBase_nhdsWithin_source
```

derives both the self-base product-reduction certificate and the multiplier
bound from `hCedge`/`hbase`, chooses `c=Kmul^{-1}`, and returns a positive
constant for the adapted fixed-base product-difference square-sum lower bound
on the source-rank filter.

Boundary: this is not an original DLN/statistical loss comparison, not
source-rank openness, not analytic chart or measure transport, not normal
crossings, not pole order, and not RLCT extraction.

## 2026-06-25 A2 adapted product-difference local-measure handoff

Reproduction:
`reproduction-a2-adapted-product-difference-local-measure-handoff.md`.
Statement card:
`statement-card-a2-adapted-product-difference-local-measure-handoff.md`.
Review:
`review-a2-adapted-product-difference-local-measure-handoff.md`.

Lean now proves the restricted-measure and product first-projection a.e.
wrappers for the positive self-base adapted fixed-base product-difference
lower bound:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_half_regular_add_residual_squareSum_le_adaptedProductDifferenceSquareSum_selfBase
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_prod_fst_half_regular_add_residual_squareSum_le_adaptedProductDifferenceSquareSum_selfBase
```

The proof preserves the upstream positive constant and applies the existing
local-measure handoff from `nhdsWithin` eventual predicates to a.e. predicates
on `mu.restrict (U inter sourceStratum)`, and its product-measure
first-projection version.

Boundary: the right-hand side is still only
`paperEndpointFixedBaseAdaptedProductDifferenceSquareSum`.  This does not
compare with original `lossDLN`, construct the p.13 product chart, transport
Jacobian/prior density, prove residual positivity/integrability, produce normal
crossings, compute pole order, or extract an RLCT.

An xhigh original-loss audit is recorded at
`audit-a2-original-loss-to-p13-boundary.md`: any future theorem connecting
original DLN/statistical loss to p.13 coordinates must either prove or assume a
positive local comparison from original loss to the adapted product-difference
square-sum.  Aoyagi p.13 alone is not being treated as that bridge.

## 2026-06-25 A2 adapted product-difference local finite-integral handoff

Reproduction:
`reproduction-a2-adapted-product-difference-local-finite-integral-handoff.md`.
Statement card:
`statement-card-a2-adapted-product-difference-local-finite-integral-handoff.md`.
Review:
`review-a2-adapted-product-difference-local-finite-integral-handoff.md`.

Lean now proves the conditional finite-integral handoff

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_chartLoss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_adaptedProductDifferenceSquareSum_identified
```

in `RegularSuspensionLocalMeasure.lean`.

The theorem takes an independent product edge-family `CedgeProd`, a supplied
product-coordinate adapted lower bound

```text
c * (residualSquareSumBase(x) + squareSum(u))
  <= paperEndpointFixedBaseAdaptedProductDifferenceSquareSum(CedgeProd(x,u)),
```

and a supplied identification of that adapted square-sum with `chartLoss(x,u)`.
It then delegates to the existing p.13 local finite-integral theorem and
returns a ball-local, indicator-supported finite integral for
`chartLoss^(-(t+regularCount/2))*density`.

Boundary: this does not derive the product-coordinate lower bound from the
base-only self-base comparison, construct a product chart, prove source
coverage, transport Jacobian/prior density, prove residual
positivity/integrability, compare original `lossDLN`, produce normal crossings,
compute pole order, or extract an RLCT.

## 2026-06-25 A2 residual positive-set measurability handoff

Reproduction:
`reproduction-a2-residual-positive-set-measurability-handoff.md`.
Statement card:
`statement-card-a2-residual-positive-set-measurability-handoff.md`.
Review:
`review-a2-residual-positive-set-measurability-handoff.md`.

Lean now proves

```text
measurable_aoyagiCoordinateSquareSum
PaperEndpointFixedBaseRegularCoordinateSourceData.measurableSet_residualSquareSum_pos_of_measurable
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_residual
```

The first theorem is generic finite square-sum measurability.  The second
derives measurability of the residual square-sum positive set from global
measurability of the p.13 residual coordinate map.  The third removes the
explicit `hpos_meas` premise from the weighted signed-box residual source
constructor under that same residual-coordinate measurability assumption.

Boundary: this does not prove global residual-coordinate measurability from the
edge family or suffix-state recursion, residual positivity/integrability by
itself, the weighted pushforward identity, chart construction, density/Jacobian
transport, original-loss comparison, normal crossings, pole order, or RLCT.

## 2026-06-25 A2 residual-coordinate map measurability

Reproduction:
`reproduction-a2-residual-coordinate-map-measurability.md`.
Statement card:
`statement-card-a2-residual-coordinate-map-measurability.md`.
Review:
`review-a2-residual-coordinate-map-measurability.md`.

Lean now proves the deterministic suffix-recursion measurability bridge:

```text
measurable_matrix_inv_real
measurable_chartLocalSuffixState_suffixState_fields_real
measurable_paperEndpointFixedBaseResidualBlockCoordinateMap_of_measurable_edgeMatrix
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix
```

The edge hypothesis is the measurable Pi-valued fixed-basis matrix family
`x |-> paperEndpointFixedBaseEdgeMatrixOfReverseEdges ... (fun p => Cedge x p)`.
This is the matrix family actually consumed by the p.13 deterministic suffix
state.  The proof uses finite real matrix Borel operations, including global
measurability of totalized matrix inverse, and then projects the final `D`
block.

Boundary: this deliberately does not assert raw `Measurable Cedge` for
arbitrary non-normed continuous-linear-map spaces.  It also does not prove
source-rank openness, analytic chart construction, pushforward, density or
Jacobian transport, original-loss comparison, residual positivity or
integrability by itself, normal crossings, pole order, or RLCT.

## 2026-06-25 A2 signed-box residual source finite-integral bridge

Reproduction:
`reproduction-a2-signed-box-residual-source-finite-integral-bridge.md`.
Statement card:
`statement-card-a2-signed-box-residual-source-finite-integral-bridge.md`.
Review:
`review-a2-signed-box-residual-source-finite-integral-bridge.md`.

Lean now proves the direct p.13 finite-integral handoff

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
```

in `RegularSuspensionLocalMeasure.lean`.

The theorem first invokes
`residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix`
to obtain residual positivity and residual negative-power integrability on
the source-rank stratum, then passes those two hypotheses to
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top`.

Boundary: source-stratum measurability, fixed-basis edge-matrix
measurability, `0 < t`, signed-box chart a.e.-measurability, source-density
a.e.-measurability, weighted source pushforward, signed-box residual monomial
lower bound, source-density a.e. nonnegativity, signed-box density monomial
upper bound, and local regular-fiber loss/density bounds remain explicit
inputs.  This does not construct a p.13 chart, prove the pushforward, transport
Jacobian/prior density, compare original `lossDLN`, produce normal crossings,
compute pole order, or extract an RLCT.

## 2026-06-25 A2 signed-box residual continuous-density finite-integral bridge

Reproduction:
`reproduction-a2-signed-box-residual-continuous-density-finite-integral-bridge.md`.
Statement card:
`statement-card-a2-signed-box-residual-continuous-density-finite-integral-bridge.md`.
Review:
`review-a2-signed-box-residual-continuous-density-finite-integral-bridge.md`.

Lean now proves the radius-shrinking p.13 finite-integral handoff

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_continuousAt_pos_density
```

in `RegularSuspensionLocalMeasure.lean`.

The theorem first obtains residual positivity and residual negative-power
integrability from the measurable-edge weighted signed-box residual-source
constructor, then passes those to
`exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_continuousAt_pos_density`.
The second theorem shrinks the regular-coordinate radius using positivity and
continuity of the supplied product density at `(x₀,0)`.

Boundary: source-stratum measurability, fixed-basis edge-matrix
measurability, `0 < t`, signed-box chart a.e.-measurability, source-density
a.e.-measurability/nonnegativity/upper bound, weighted source pushforward,
signed-box residual monomial lower bound, positive continuous product density,
and the local regular-fiber loss lower bound remain explicit inputs.  This
does not construct a chart, prove the pushforward, transport Jacobian/prior
density, compare original `lossDLN`, produce normal crossings, compute pole
order, or extract an RLCT.

## 2026-06-25 A2 continuous-edge signed-box continuous-density finite-integral bridge

Reproduction:
`reproduction-a2-continuous-edge-signed-box-continuous-density-finite-integral-bridge.md`.
Statement card:
`statement-card-a2-continuous-edge-signed-box-continuous-density-finite-integral-bridge.md`.
Review:
`review-a2-continuous-edge-signed-box-continuous-density-finite-integral-bridge.md`.

Lean now proves the global-continuous-edge variant

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_continuousAt_pos_density
```

in `RegularSuspensionLocalMeasure.lean`.

The theorem derives source-rank-stratum measurability from
`measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous`, derives
fixed-basis endpoint edge-matrix measurability by composing `Continuous Cedge`
with `continuous_linearMap_toMatrix`, and then delegates to the signed-box
continuous-density finite-integral bridge.

Boundary: this assumes global `Continuous Cedge`; it does not derive the
result from only `ContinuousAt Cedge x₀`, does not assert source-rank openness,
and does not introduce a raw `Measurable Cedge` interface.  The signed-box
chart, weighted pushforward, source-density hypotheses, residual lower bound,
positive continuous product density, and local regular-fiber loss lower bound
remain explicit inputs.  This does not construct a chart, prove the
pushforward, transport Jacobian/prior density, compare original `lossDLN`,
produce normal crossings, compute pole order, or extract an RLCT.

## 2026-06-25 A2 adapted product-difference loss-comparison finite integral

Reproduction:
`reproduction-a2-adapted-product-difference-loss-comparison-finite-integral.md`.
Statement card:
`statement-card-a2-adapted-product-difference-loss-comparison-finite-integral.md`.
Review:
`review-a2-adapted-product-difference-loss-comparison-finite-integral.md`.

Lean now proves the conditional comparison handoff

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_const_mul_adaptedProductDifferenceSquareSum_le_loss
```

in `RegularSuspensionLocalMeasure.lean`.

The theorem assumes a product-coordinate lower bound
`c * (residualSquareSum(x)+squareSum(u)) <= adaptedSquareSum(x,u)` and a
positive comparison `c0 * adaptedSquareSum(x,u) <= loss(x,u)`.  It multiplies
constants to obtain the existing p.13 local finite-integral input with
constant `c0 * c`.

Boundary: the comparison with `loss` is supplied, not proved.  This does not
identify the original DLN/statistical loss with the p.13 adapted square-sum,
construct a product chart, prove source coverage, transport Jacobian/prior
density, prove residual source hypotheses, produce normal crossings, compute
pole order, or extract an RLCT.

## 2026-06-25 A2 adapted loss-comparison continuous-density finite integral

Reproduction:
`reproduction-a2-adapted-loss-comparison-continuous-density-finite-integral.md`.
Statement card:
`statement-card-a2-adapted-loss-comparison-continuous-density-finite-integral.md`.
Review:
`review-a2-adapted-loss-comparison-continuous-density-finite-integral.md`.

Lean now proves the radius-shrinking helper

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density
```

in `RegularSuspensionLocalMeasure.lean`.

It combines the adapted-to-loss comparison finite-integral bridge with the
existing continuous-density local-bounds theorem.  The theorem assumes
positive continuous product density at `(x₀,0)` and shrinks from `Rmax` to
some `R <= Rmax`.

Boundary: this is a helper for the composed front end below.  It still assumes
residual source hypotheses, the product-coordinate adapted lower bound, and
the adapted-to-loss comparison.  It does not construct a chart, prove
density/Jacobian transport, compare original `lossDLN`, produce normal
crossings, compute pole order, or extract an RLCT.

## 2026-06-25 A2 continuous-edge signed-box adapted-loss finite integral

Reproduction:
`reproduction-a2-continuous-edge-signed-box-adapted-loss-finite-integral.md`.
Statement card:
`statement-card-a2-continuous-edge-signed-box-adapted-loss-finite-integral.md`.
Review:
`review-a2-continuous-edge-signed-box-adapted-loss-finite-integral.md`.

Lean now proves the composed front end

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density
```

in `RegularSuspensionLocalMeasure.lean`.

The theorem derives source-stratum measurability and fixed-basis edge-matrix
measurability from global `Continuous Cedge`, obtains residual positivity and
negative-power integrability from the supplied weighted signed-box residual
chart, obtains density bounds from positive continuous product density, and
uses the supplied product-coordinate adapted lower bound plus
`c0 * adapted <= loss` to produce the p.13 finite-integral comparison.

Boundary: the signed-box chart, weighted pushforward, residual monomial lower
bound, source-density bounds, product-coordinate adapted lower bound, and
adapted-to-loss comparison remain explicit.  No product chart,
density/Jacobian transport, original-loss comparison, normal crossings, pole
order, or RLCT is proved.

## 2026-06-25 A2 fixed-base adapted endpoint Frobenius comparison

Reproduction:
`reproduction-a2-fixed-base-adapted-endpoint-frobenius-comparison.md`.
Statement card:
`statement-card-a2-fixed-base-adapted-endpoint-frobenius-comparison.md`.
Review:
`review-a2-fixed-base-adapted-endpoint-frobenius-comparison.md`.

Lean now proves the fixed-basis endpoint Frobenius identity

```text
paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum
```

in `RegularSuspensionCoordinates.lean`, plus the base matrix identity

```text
paperEndpointFixedBaseTotalMatrixOfReverseEdges_selfBase_eq_fromBlocks_one_zero_zero
paperEndpointFixedBaseAdaptedProductDifferenceSquareSum_eq_baseRelative_totalMatrix_squareSum
```

and Frobenius-form wrappers for the existing p.13 product-reduction bounds:

```text
PaperEndpointFixedBaseProductReductionCertificate.const_mul_literalProductDifferenceCoordinateMap_squareSum_le_adaptedProductDifferenceFrobeniusLoss
PaperEndpointFixedBaseProductReductionCertificate.const_mul_literalProductDifferenceCoordinateMap_squareSum_eventually_le_adaptedProductDifferenceFrobeniusLoss_nhdsWithin_source
PaperEndpointFixedBaseRegularCoordinateSourceData.half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceFrobeniusLoss_of_productReductionCertificate_nhdsWithin_source
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceFrobeniusLoss_selfBase_nhdsWithin_source
```

The key finite arithmetic theorem is
`matrix_trace_transpose_mul_self_eq_aoyagiCoordinateSquareSum`: for a real
finite matrix `M`, `trace(M^T*M)` is the entrywise square-sum.  Applying this
to `M = T(x)-[[I,0],[0,0]]` identifies the adapted square-sum with the fixed
adapted endpoint Frobenius square.

Boundary: this is not the original `lossDLN`, not a statistical loss, and not a
basis-change comparison with original network-coordinate Frobenius norm.  No
product chart, density/Jacobian transport, source-rank openness,
regular-suspension theorem, normal crossings, pole order, or RLCT is proved.

## 2026-06-25 A2 finite basis-change square-sum comparison

Reproduction:
`reproduction-a2-finite-basis-change-square-sum-comparison.md`.
Statement card:
`statement-card-a2-finite-basis-change-square-sum-comparison.md`.
Review:
`review-a2-finite-basis-change-square-sum-comparison.md`.

Lean now proves the finite coordinate comparison

```text
exists_pos_const_matrixCoordinateSquareSum_le_of_mul_eq
exists_pos_const_forall_matrixCoordinateSquareSum_le_mul
exists_pos_const_linearMap_toMatrix_squareSum_le_of_basis_change
exists_pos_const_forall_linearMap_toMatrix_squareSum_le_of_basis_change
```

in `RegularSuspensionCoordinates.lean`.

The pointwise matrix theorem says that if `T = L*M*R`, then some `c > 0`
satisfies `c*squareSum(T) <= squareSum(M)`.  The proof uses the existing
submultiplicativity estimate and the constant
`c = max(1, squareSum(L)*squareSum(R))^{-1}`, so zero-dimensional matrix-index
cases are covered.  The uniform matrix theorem fixes `L` and `R` once and for
all.  The basis-change theorems apply these estimates to two fixed pairs of
bases for the source and target of a real linear map, with the uniform version
recording that the comparison constant does not depend on the map.

Boundary: this is global finite-dimensional coordinate algebra.  It is not a
`lossDLN` theorem, not a tuple/product bridge, not a statistical/KL/covariance
comparison, and not an analytic chart, density/Jacobian, normal-crossing,
pole-order, or RLCT theorem.  The next bridge prerequisite is a theorem that a
tuple built from chosen bases has `mult` equal to the corresponding chain-map
matrix.

## 2026-06-25 A2 chain-map tuple product bridge

Reproduction:
`reproduction-a2-chainmap-tuple-product-bridge.md`.
Statement card:
`statement-card-a2-chainmap-tuple-product-bridge.md`.
Review:
`review-a2-chainmap-tuple-product-bridge.md`.

Lean now proves the product-coordinate bridge in the new module
`DLNFibre.DLN.Aoyagi.ChainMapTupleBridge`:

```text
chainMapMatrixTuple
submult_chainMapMatrixTuple
multPrefix_chainMapMatrixTuple
mult_chainMapMatrixTuple
mult_toMatrix_chainMap
mult_toMatrix_chainMap_reverseVertex
```

For a chain `A p : V p.castSucc -> V p.succ` and fixed bases
`b j : Basis (Fin (d j)) K (V j)`, `chainMapMatrixTuple b A` is the core
`Tuple d` whose factors are the edge matrices.  The interval theorem proves
`submult d (chainMapMatrixTuple b A) i j = [chainMap(i,j)]_{b_i,b_j}`, and the
total theorem specializes this to
`mult d (chainMapMatrixTuple b A) = [chainMap(0,last)]_{b_0,b_last}`.  The
reverse-vertex wrapper instantiates this with `V = reverseVertex W`.

Boundary: this is only the finite product-coordinate identity.  It does not
unfold `lossDLN`, choose the target matrix, compare fixed adapted endpoint
coordinates with original endpoint coordinates, prove a statistical/KL or
covariance loss comparison, construct a product chart, transport
density/Jacobian factors, produce normal crossings, compute pole order, or
extract an RLCT.

## 2026-06-25 A2 chain-map loss bridge

Reproduction:
`reproduction-a2-chainmap-loss-bridge.md`.
Statement card:
`statement-card-a2-chainmap-loss-bridge.md`.
Review:
`review-a2-chainmap-loss-bridge.md`.

Lean now proves the `lossDLN` rewrite in the new module
`DLNFibre.DLN.Aoyagi.ChainMapLossBridge`:

```text
chainMapMatrixFrobeniusLossAgainst
chainMapMatrixFrobeniusLoss
lossDLN_chainMapMatrixTuple_eq_trace
lossDLN_chainMapMatrixTuple_eq_chainMapFrobenius
lossDLN_reverseVertex_chainMapMatrixTuple_eq_baseFrobenius
```

For a tuple `chainMapMatrixTuple b A`, `lossDLN` against any endpoint matrix
`B` is the Frobenius trace of
`[chainMap_A(0,last)]_{b_0,b_last} - B`.  When `B` is the endpoint matrix of a
target chain `A0`, the loss is the Frobenius trace of the difference of the
two endpoint chain-map matrices.  The reverse-vertex wrapper specializes this
to the Aoyagi base paper-order chain `reverseEdge W Bpaper`.

Boundary: this is only an equality rewrite of `lossDLN`.  It does not compare
original endpoint bases with fixed adapted endpoint bases, prove a positive
basis-change lower bound for this loss, identify a statistical/KL/covariance
loss, construct a product chart, transport density/Jacobian factors, produce
normal crossings, compute pole order, or extract an RLCT.

## 2026-06-25 A2 endpoint loss comparison

Reproduction:
`reproduction-a2-endpoint-loss-comparison.md`.
Statement card:
`statement-card-a2-endpoint-loss-comparison.md`.
Review:
`review-a2-endpoint-loss-comparison.md`.

Lean now proves the finite endpoint basis-comparison bridge in the new module
`DLNFibre.DLN.Aoyagi.EndpointLossComparison`:

```text
chainMapMatrixFrobeniusLoss_eq_toMatrix_sub_squareSum
exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_chainMapFrobeniusLoss
exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_lossDLN_chainMapMatrixTuple
```

For a variable reversed-edge family `E` and base chain `B`, the fixed adapted
endpoint Frobenius loss is the square-sum of the endpoint matrix of
`T(E)-T(B)` in the fixed adapted endpoint bases.  The finite basis-change
comparison gives a constant `c > 0` such that this adapted loss times `c` is
bounded by the same endpoint Frobenius square in any fixed original endpoint
bases.  The `lossDLN` corollary then applies the chain-map loss bridge to the
tuple `chainMapMatrixTuple b E`.

Boundary: this is a square-Frobenius endpoint loss theorem only.  The target
matrix in `lossDLN` is the base endpoint map expressed in the same original
endpoint bases; it is not the adapted block matrix reused in original
coordinates.  There is no arbitrary-tuple comparison, no statistical/KL or
covariance loss comparison, no chart construction, no density/Jacobian
transport, no normal crossings, no pole order, and no RLCT extraction.

## 2026-06-25 A2 original loss local measure handoff

Reproduction:
`reproduction-a2-original-loss-local-measure.md`.
Statement card:
`statement-card-a2-original-loss-local-measure.md`.
Review:
`review-a2-original-loss-local-measure.md`.

Lean now proves the concrete original square-Frobenius local-measure bridge in
the new module `DLNFibre.DLN.Aoyagi.OriginalLossLocalMeasure`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_adaptedProductDifferenceSquareSum_lower_continuousAt_pos_density

PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_adaptedProductDifferenceSquareSum_lower_continuousAt_pos_density
```

The wrappers instantiate the existing adapted-loss finite-integral handoffs
with

```text
loss z = lossDLN d [T(B)]_b (chainMapMatrixTuple b (CedgeProd z)).
```

The missing comparison hypothesis is proved from the endpoint loss comparison
and the fixed adapted Frobenius/square-sum identification.  The top theorem is
now the preferred A2 finite-integral front end when the tuple really comes
from the product-coordinate edge family and the desired loss is original
`lossDLN`.

Boundary: the p.13 product-coordinate adapted lower bound, signed-box source
chart and weighted pushforward, residual monomial lower bound,
source-density bounds, positive continuous transported density, and global
`Continuous Cedge` hypothesis remain explicit.  This does not handle
arbitrary tuples, statistical/KL/covariance losses, product-chart
construction, density/Jacobian transport, normal crossings, pole order, or
RLCT extraction.

## 2026-06-25 A2 original loss self-base lower bound

Reproduction:
`reproduction-a2-original-loss-self-base-lower-bound.md`.
Statement card:
`statement-card-a2-original-loss-self-base-lower-bound.md`.
Review:
`review-a2-original-loss-self-base-lower-bound.md`.

Lean now proves the one-parameter self-base source-filter lower bound in
`DLNFibre.DLN.Aoyagi.EndpointLossComparison`:

```text
exists_pos_const_half_regular_add_residual_squareSum_eventually_le_lossDLN_chainMapMatrixTuple_selfBase_nhdsWithin_source
```

The theorem composes the existing self-base p.13 lower bound into fixed
adapted endpoint Frobenius loss with the endpoint basis comparison into
original square-Frobenius `lossDLN`.  If the p.13 lower-bound constant is
`a > 0` and the endpoint comparison constant is `b > 0`, Lean uses
`c = a*b` and rewrites `b*((a/2)*S)` as `(c/2)*S`.

Boundary: this is not the product-coordinate chart theorem.  It treats only
the actual edge family `Cedge x` near the self-base point, not an independent
regular fiber variable `u`.  It does not prove chart construction,
signed-box/product source-measure transport, density/Jacobian transport,
normal crossings, pole order, or RLCT extraction.

## 2026-06-25 A2 original loss source-measure handoff

Reproduction:
`reproduction-a2-original-loss-source-measure-handoff.md`.
Statement card:
`statement-card-a2-original-loss-source-measure-handoff.md`.
Review:
`review-a2-original-loss-source-measure-handoff.md`.

Lean now proves the restricted-source a.e. handoff for the self-base original
square-Frobenius lower bound in
`DLNFibre.DLN.Aoyagi.OriginalLossSourceMeasure`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_prod_fst_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase
```

These theorems apply the generic `nhdsWithin`-to-restricted-a.e. local-measure
handoffs to the self-base original-loss source-filter theorem.  The measure is
restricted to `U ∩ sourceStratum`; the product form is only a first-projection
statement over `(mu.restrict (U ∩ sourceStratum)).prod nu`.

Boundary: this is source-measure plumbing only.  It does not construct the
p.13 product chart, identify an independent regular fiber variable, prove
signed-box pushforward, transport density/Jacobian factors, produce normal
crossings, compute pole order, or extract an RLCT.

## 2026-06-25 A2 original loss source-measure continuous-edge wrapper

Reproduction:
`reproduction-a2-original-loss-source-measure-continuous-edge-wrapper.md`.
Statement card:
`statement-card-a2-original-loss-source-measure-continuous-edge-wrapper.md`.
Review:
`review-a2-original-loss-source-measure-continuous-edge-wrapper.md`.

Lean now proves continuous-edge convenience wrappers in
`DLNFibre.DLN.Aoyagi.OriginalLossSourceMeasure`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase_of_continuousEdge
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_prod_fst_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase_of_continuousEdge
```

The wrappers replace the separate `ContinuousAt Cedge x0` and source-stratum
measurability inputs by global `Continuous Cedge`.  The measurable-set input is
discharged by `measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous`;
the source-filter lower bound receives `hCedge.continuousAt`.

Boundary: this is only a measurability/continuity convenience wrapper around
the restricted-source a.e. handoff.  It does not prove source-rank openness,
construct the product chart, identify an independent regular fiber variable,
prove signed-box pushforward, transport density/Jacobian factors, produce
normal crossings, compute pole order, or extract an RLCT.

## 2026-06-25 A2 edge-matrix signed-box adapted-loss finite integral

Reproduction:
`reproduction-a2-edge-matrix-signed-box-adapted-loss-finite-integral.md`.
Statement card:
`statement-card-a2-edge-matrix-signed-box-adapted-loss-finite-integral.md`.
Review:
`review-a2-edge-matrix-signed-box-adapted-loss-finite-integral.md`.

Lean now proves the edge-matrix-measurable variant of the signed-box
adapted-loss finite-integral front end:

```text
measurableSet_matrix_rank_eq_of_measurable_finite
measurableSet_paperEndpointFixedBaseEdgeRankStratum_of_measurable_edgeMatrix
measurableSet_paperEndpointFixedBaseSourceRankStratum_of_measurable_edgeMatrix
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density
```

It also proves the corresponding original square-Frobenius consumer:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_adaptedProductDifferenceSquareSum_lower_continuousAt_pos_density
```

The source-rank stratum is measurable from the same fixed-base edge-matrix
family used by the deterministic p.13 suffix recursion, using finite matrix
exact-rank measurability and
`rank_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_eq_finrank_range`.
The adapted-loss theorem then obtains residual source hypotheses from the
weighted signed-box residual constructor and delegates to the existing
continuous-density adapted-loss comparison theorem.  The original-loss theorem
discharges the adapted-to-loss comparison by endpoint basis comparison for
`chainMapMatrixTuple`.

Boundary: the signed-box chart and weighted pushforward, residual monomial
lower bound, source-density bounds, positive continuous product density,
product-coordinate adapted lower bound, and for the abstract loss theorem the
adapted-to-loss comparison remain explicit.  This does not construct the
product chart, derive source coverage, transport density/Jacobian factors,
derive the product-coordinate adapted lower bound, produce normal crossings,
compute pole order, or extract an RLCT.

## 2026-06-25 A2 product-coordinate adapted lower-bound socket

Reproduction:
`reproduction-a2-product-coordinate-adapted-lower-bound-socket.md`.
Statement card:
`statement-card-a2-product-coordinate-adapted-lower-bound-socket.md`.
Review:
`review-a2-product-coordinate-adapted-lower-bound-socket.md`.

Lean now proves the conditional independent regular-fiber lower-bound socket in
`DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_productCoordinateShape_nhdsWithin_source
```

The theorem assumes a positive regular radius, product-coordinate shape

```text
cleaned(CedgeProd(x,u)) = residual(CedgeBase x) + squareSum(u),
```

the cleaned-to-literal p.13 comparison `cleaned <= 2*literal`, a
product-reduction certificate, `0 < Kmul`, and a uniform triangular multiplier
bound with that `Kmul`.  It
then produces the exact `hadapted_lower` shape consumed by the local-measure
and original-loss finite-integral front ends.

Review caught and fixed two fidelity issues: the Lean statement now requires
`0 < Rmax`, and the notes now say the theorem assumes the cleaned-to-literal
comparison directly rather than exposing `F2/F3` smallness.

Boundary: this is a conditional socket only.  It does not construct
`CedgeProd`, identify analytic product coordinates, derive `F2/F3` smallness
for the product family, prove source coverage, prove signed-box pushforward,
transport density/Jacobian factors, produce normal crossings, compute pole
order, or extract an RLCT.

## 2026-06-25 A2 product-family assumption-reduction sockets

Reproduction:
`reproduction-a2-product-family-assumption-reduction-sockets.md`.
Statement card:
`statement-card-a2-product-family-assumption-reduction-sockets.md`.
Review:
`review-a2-product-family-assumption-reduction-sockets.md`.

Lean now reduces two opaque hypotheses behind the product-coordinate adapted
lower-bound socket in `DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates`:

```text
paperEndpointFixedBaseRegularBlockF2F3SquareSum
PaperEndpointFixedBaseRegularCoordinateSourceData.productDifferenceCoordinateMap_squareSum_le_two_mul_literalProductDifferenceCoordinateMap_squareSum_of_regularBlockF2F3SquareSum_le_one
PaperEndpointFixedBaseRegularCoordinateSourceData.productDifferenceCoordinateMap_squareSum_eventually_le_two_mul_literalProductDifferenceCoordinateMap_squareSum_nhdsWithin_source_prod_of_regularBlockF2F3SquareSum_le_one
PaperEndpointFixedBaseRegularCoordinateSourceData.productCoordinateShape_nhdsWithin_source_of_regular_residual_coordinateMap_eq
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_productCoordinateShape_regularBlockF2F3Small_nhdsWithin_source
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_regular_residual_coordinateMap_eq_regularBlockF2F3Small_nhdsWithin_source
```

The first bridge derives the socket's cleaned-to-literal comparison from
supplied product-family `F2/F3` smallness.  The second derives the
product-coordinate square-sum shape from supplied component identities:
regular coordinates equal `u`, and residual coordinates equal the base
residual block.  The composed wrapper replaces the direct
cleaned-to-literal hypothesis by the `F2/F3` smallness hypothesis while
leaving product shape, certificates, multiplier bound, and `0 < Rmax`
explicit.  The fully composed wrapper also replaces the direct product-shape
hypothesis by the regular/residual component identities.

Extended same day: Lean now also derives the product-family `F2/F3` smallness
from literal regular-coordinate equality and the radius bound `Rmax <= 1`:

```text
aoyagiCoordinateSquareSum_le_one_of_mem_ball_le_one
AoyagiRegularBlockCoordinateIndex.f2_f3_squareSum_add_le_coordinateSquareSum
PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseRegularBlockF2F3SquareSum_le_regularBlockCoordinateMap_squareSum
PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseRegularBlockF2F3SquareSum_le_one_of_regularBlockCoordinateMap_eq_of_mem_ball_le_one
PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseRegularBlockF2F3SquareSum_eventually_le_one_nhdsWithin_source_of_regularBlockCoordinateMap_eq_of_mem_ball_le_one
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_regular_residual_coordinateMap_eq_regularRadius_le_one_nhdsWithin_source
```

The finite smallness proof uses
`F2/F3 squareSum <= full regular squareSum`, the identity
`regularBlock(CedgeProd(x,u)) = u`, and
`u in ball(0,Rmax), Rmax <= 1 => squareSum(u) <= 1`.  The final wrapper keeps
`0 < Rmax` because the existing adapted lower-bound socket carries a positive
regular-radius interface/nonvacuity condition.  Literal coordinate equality is
essential; a hidden permutation, scaling, or linear change would require a
separate norm bound.

Boundary: no product family is constructed, no analytic coordinate chart is
proved, and no source coverage, signed-box pushforward, density/Jacobian
transport, normal crossings, pole order, or RLCT extraction is proved.

## 2026-06-25 A2 product-family suffix-field construction

Reproduction:
`reproduction-a2-product-family-suffix-field-construction.md`.
Statement card:
`statement-card-a2-product-family-suffix-field-construction.md`.
Review:
`review-a2-product-family-suffix-field-construction.md`.

Lean now proves the first finite matrix layer toward an actual product-family
constructor.  In `DLNFibre.DLN.Aoyagi.ProductReduction`, the new one-step
suffix-field lemmas are:

```text
ChartLocalSuffixState.step_finalF3_fromBlocks
ChartLocalSuffixState.step_middleResidualFactor_fromBlocks
ChartLocalSuffixState.step_leftEndpointF2Ctop_fromBlocks
ChartLocalSuffixState.step_singleEdgeF2F3Ctop_fromBlocks
ChartLocalSuffixState.suffixState_tail_fields_of_productFamily_transformedEdges
ChartLocalSuffixState.suffixState_productFamily_fields_fromBlocks_one
ChartLocalSuffixState.suffixState_productFamily_fields_fromBlocks_succSucc
```

They verify and assemble the block shapes from the p.13 construction: a
right-endpoint edge creates `F3`, middle block-diagonal edges preserve the
regular fields and multiply the residual factor, a left endpoint edge creates
`B = -F2` and `Ctop`, and the one-edge case creates all regular fields while
preserving the supplied Schur residual `C0`.  For chains with at least two
edges, the global theorem proves final fields `B = -F2`, `Ctop = Ctop`,
`D = residualProduct E last 0`, and `L = [I, 0; F3, I]` from the corresponding
transformed-edge shape hypotheses.  The determinant-unit hypothesis appears
only where the `Ctop` inverse is cancelled.

Also in `RegularSuspensionCoordinates.lean`,
`paperEndpointFixedBaseRegularBlockF2F3SquareSum_eq_suffixState_B_lowerLeftBlock`
expands the fixed-base `F2/F3` square-sum as exactly the square-sum of the
suffix fields `-S.B` and `lowerLeftBlock S.L`.

Independent review found no sign error or overclaim.  Boundary: this is still
finite transformed-edge matrix algebra.  It does not construct fixed-base
continuous edge maps, prove those maps realize the transformed-edge shapes,
prove source coverage, signed-box pushforward, density/Jacobian transport,
normal crossings, pole order, or RLCT extraction.

## 2026-06-25 A2 fixed-base product-family coordinate readout

Reproduction:
`reproduction-a2-fixed-base-product-family-coordinate-readout.md`.
Statement card:
`statement-card-a2-fixed-base-product-family-coordinate-readout.md`.
Review:
`review-a2-fixed-base-product-family-coordinate-readout.md`.

Lean now connects the matrix-level product-family suffix fields to the
fixed-base p.13 coordinate maps.  In `RegularSuspensionCoordinates.lean`,

```text
paperEndpointFixedBaseSuffixState_fields_of_productFamily_transformedEdges_succSucc
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productFamily_transformedEdges_succSucc
```

specialize the generic suffix-field theorem to the endpoint bases used by
`paperEndpointFixedBaseEdgeMatrixOfReverseEdges`, then read the cleaned
product-difference coordinate map as

```text
value(Ctop - I, F2, F3, residualProduct EMat last 0).
```

The signs are the p.13 signs: `S.B = -F2` is read as the coordinate `F2`, and
`S.L = [I,0;F3,I]` is read as `F3`.  The residual coordinate remains the
edgewise residual product, not an arbitrary final residual matrix.

Boundary: the theorem still assumes the transformed-edge block shapes.  It
does not construct `CedgeProd`, prove fixed-base continuous maps realize those
shapes, prove source coverage, signed-box pushforward, density/Jacobian
transport, normal crossings, pole order, or RLCT extraction.

## 2026-06-25 A2 fixed-base prescribed edge-matrix realisation

Reproduction:
`reproduction-a2-fixed-base-prescribed-edge-matrix-realisation.md`.
Statement card:
`statement-card-a2-fixed-base-prescribed-edge-matrix-realisation.md`.
Review:
`review-a2-fixed-base-prescribed-edge-matrix-realisation.md`.

Lean now turns prescribed fixed-base edge matrices back into actual reversed
edge maps.  In `FixedBasepointChart.lean`:

```text
paperEndpointFixedBaseReverseEdgeFamilyOfMatrices
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_reverseEdgeFamilyOfMatrices
paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOfMatrices
```

The algebraic statement is the basis inverse law
`toMatrix(toLin(G)) = G`; the continuous statement uses
`LinearMap.toContinuousLinearMap` in finite dimensions and reads back the same
matrix.

In `RegularSuspensionCoordinates.lean`,

```text
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_prescribedProductFamilyEdgeMatrices_succSucc
```

packages this with the product-family coordinate readout: if the prescribed
matrices `G` satisfy the transformed-edge block-shape hypotheses, the
continuous fixed-base edge family realised from `G` has coordinates
`value(Ctop - I, F2, F3, residualProduct G last 0)`.

Boundary: this is pointwise.  It does not construct a product-coordinate
matrix family `G(x,u)`, prove transformed-edge block shapes for such a family,
prove parameter-continuity, source coverage, signed-box pushforward,
density/Jacobian transport, normal crossings, pole order, or RLCT extraction.
An attempted fully parameterized convenience wrapper was removed because it
caused pathological elaboration by unfolding the large coordinate map; use the
pointwise theorem as the next API.

## 2026-06-25 A2 fixed-base single-edge product-family coordinate readout

Reproduction:
`reproduction-a2-fixed-base-single-edge-product-family-coordinate-readout.md`.
Statement card:
`statement-card-a2-fixed-base-single-edge-product-family-coordinate-readout.md`.
Review:
`review-a2-fixed-base-single-edge-product-family-coordinate-readout.md`.

Lean now covers the one-edge product-family coordinate case in
`RegularSuspensionCoordinates.lean`:

```text
paperEndpointFixedBaseSuffixState_fields_of_productFamily_transformedEdge_one
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productFamily_transformedEdge_one
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_prescribedProductFamilyEdgeMatrix_one
```

The transformed edge shape is the endpoint-collapse block

```text
[ Ctop,       -Ctop F2
  -F3 Ctop,   C0 + F3 Ctop F2 ],
```

and the cleaned coordinate readout is
`value(Ctop - I, F2, F3, C0)`.  The prescribed-matrix theorem realises the
single fixed-base matrix as a continuous edge map and then reads it back.

Boundary: still finite and pointwise.  No product-coordinate matrix family,
parameter-continuity, transformed-edge production, source coverage,
density/Jacobian transport, normal crossings, pole order, or RLCT extraction is
proved.

## 2026-06-25 A2 fixed-base product-coordinate edge matrices

Reproduction:
`reproduction-a2-fixed-base-product-coordinate-edge-matrices.md`.
Statement card:
`statement-card-a2-fixed-base-product-coordinate-edge-matrices.md`.
Review:
`review-a2-fixed-base-product-coordinate-edge-matrices.md`.

Lean now replaces the supplied transformed-edge hypotheses by raw p.13
product-coordinate edge-matrix hypotheses.  In `ProductReduction.lean`:

```text
ChartLocalSuffixState.productCoordinateRightEndpointMatrix
ChartLocalSuffixState.productCoordinateMiddleMatrix
ChartLocalSuffixState.productCoordinateLeftEndpointMatrix
ChartLocalSuffixState.productCoordinateSingleEdgeMatrix
ChartLocalSuffixState.suffixState_tail_fields_of_productCoordinateEdges
ChartLocalSuffixState.suffixState_productCoordinate_fields_one
ChartLocalSuffixState.suffixState_productCoordinate_fields_succSucc
```

The multi-edge theorem proves the required tail induction: after the right
endpoint, and through the middle edges, the suffix state carries `B=0`; only
with that invariant do the raw middle and left edge matrices become the
displayed transformed-edge matrices.

In `RegularSuspensionCoordinates.lean`:

```text
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productCoordinateEdgeMatrix_one
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productCoordinateEdges_succSucc
```

read those raw edge patterns through the fixed-base p.13 coordinate map.  The
single-edge readout is `value(Ctop - I, F2, F3, C0)`.  The multi-edge readout
is `value(Ctop - I, F2, F3, residualProduct EMat last 0)`.

Boundary: still pointwise finite algebra.  No dependent product-family
constructor `G(x,u)`, parameter-continuity, source coverage, signed-box
pushforward, density/Jacobian transport, normal crossings, pole order, or RLCT
extraction is proved.

## 2026-06-25 A2 regular coordinate-vector block reconstruction

Reproduction:
`reproduction-a2-regular-coordinate-vector-block-reconstruction.md`.
Statement card:
`statement-card-a2-regular-coordinate-vector-block-reconstruction.md`.
Review:
`review-a2-regular-coordinate-vector-block-reconstruction.md`.

Lean now has the finite inverse to the regular-coordinate readout in
`RegularSuspensionCoordinates.lean`:

```text
AoyagiRegularBlockCoordinateIndex.ctopMinusIdentityMatrix
AoyagiRegularBlockCoordinateIndex.ctopMatrix
AoyagiRegularBlockCoordinateIndex.f2Matrix
AoyagiRegularBlockCoordinateIndex.f3Matrix
AoyagiRegularBlockCoordinateIndex.ctopMatrix_sub_one
AoyagiRegularBlockCoordinateIndex.value_coordinateMatrices
AoyagiRegularBlockCoordinateIndex.exists_value_eq
AoyagiRegularBlockCoordinateIndex.value_euclideanCoordinateMatrices
AoyagiRegularBlockCoordinateIndex.value_euclideanCtopMatrixCoordinateMatrices
```

For any scalar regular-coordinate family `coord`, the three matrices obtained
by reading the three tagged summands satisfy
`value(X,F2,F3)=coord`.  For a Euclidean regular-coordinate vector `u`, apply
this to `coord c = u c`.  When the actual top-left block is needed, the helper
`ctopMatrix` gives `Ctop=I+X` and proves `Ctop-I=X`.

Boundary: this supplies the target `Ctop - I`, `F2`, and `F3` blocks for a
future `G(x,u)` constructor.  It does not choose residual blocks, assemble edge
matrices, prove raw edge-pattern hypotheses, prove continuity in `(x,u)`,
construct a product chart, transport measures, produce normal crossings, prove
pole order, or extract RLCT.

## 2026-06-25 A2 single-edge product-coordinate family constructor

Reproduction:
`reproduction-a2-single-edge-product-coordinate-family-constructor.md`.
Statement card:
`statement-card-a2-single-edge-product-coordinate-family-constructor.md`.
Review:
`review-a2-single-edge-product-coordinate-family-constructor.md`.

Lean now has the one-edge constructor/readout in
`RegularSuspensionCoordinates.lean`:

```text
AoyagiResidualBlockCoordinateIndex.matrix
AoyagiResidualBlockCoordinateIndex.value_matrix
AoyagiResidualBlockCoordinateIndex.exists_value_eq
AoyagiProductDifferenceCoordinateIndex.value_euclideanCtopMatrixCoordinateMatrices_residual
paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_singleEdgeProductCoordinateEuclidean
```

Given a Euclidean regular-coordinate vector `u`, the constructor forms
`X,F2,F3` by tagged projection, sets `Ctop=I+X`, and builds the raw one-edge
p.13 matrix

```text
[ Ctop,       -Ctop F2
  -F3 Ctop,   D + F3 Ctop F2 ].
```

Under the explicit determinant-chart hypothesis `IsUnit Ctop.det`, the
fixed-base product-difference coordinate map reads exactly
`Sum.elim (fun c => u c) (AoyagiResidualBlockCoordinateIndex.value D)`.

Verification passed: focused `RegularSuspensionCoordinates` build, full
`DLNFibre` build via local `LAKE_SHARED=.lake-local-shared`, `scripts/sorries`,
and `git diff --check`.

Boundary: this is still one-edge, finite, and pointwise.  It does not choose
`D` from a base source family, prove multi-edge residual-product preservation,
prove parameter-continuity, construct a product chart, transport measures,
produce normal crossings, prove pole order, or extract RLCT.

## 2026-06-25 A2 single-edge residual-product realisation

Reproduction:
`reproduction-a2-single-edge-residual-product-realisation.md`.
Statement card:
`statement-card-a2-single-edge-residual-product-realisation.md`.
Review:
`review-a2-single-edge-residual-product-realisation.md`.

Lean now proves that the one-edge p.13 product-coordinate matrix realizes the
supplied residual matrix as the raw suffix residual product:

```text
ChartLocalSuffixState.residualProduct_productCoordinateSingleEdge_eq
paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean_residualProduct_eq
```

For the unique edge, the block matrix is

```text
[ Ctop,       -Ctop F2
  -F3 Ctop,   D + F3 Ctop F2 ].
```

Under `IsUnit Ctop.det`, its transformed Schur residual is `D`; the existing
suffix-state bridge identifies the suffix state's `D` field with
`residualProduct`.

Boundary: this is a one-edge transformed-residual-product theorem, not a raw
lower-right-block identity and not a multi-edge arbitrary-terminal-residual
realisation theorem.  It does not choose `D` from source data, construct a
source chart, transport measures, produce normal crossings, prove pole order,
or extract RLCT.

## 2026-06-25 A2 single-edge source-dependent residual-matrix family

Reproduction:
`reproduction-a2-single-edge-source-dependent-residual-matrix-family.md`.
Statement card:
`statement-card-a2-single-edge-source-dependent-residual-matrix-family.md`.
Review:
`review-a2-single-edge-source-dependent-residual-matrix-family.md`.

Lean now packages the one-edge p.13 product-coordinate family when the
residual matrix is allowed to depend on a base point:

```text
continuous_productCoordinateSingleEdgeMatrix
paperEndpointFixedBaseSingleEdgeProductCoordinateEdgeFamilyOfResidualMatrixEuclidean
paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_singleEdgeProductCoordinateEuclidean_residualMatrix
continuousAt_paperEndpointFixedBaseSingleEdgeProductCoordinateEdgeFamilyOfResidualMatrixEuclidean
```

At `(x,u)`, the raw edge matrix uses `Dbase x`, and under
`IsUnit det(Ctop(u))` the fixed-base coordinate readout has regular part `u`
and residual part `AoyagiResidualBlockCoordinateIndex.value (Dbase x)`.
If `Dbase` is continuous, the realised fixed-base edge family is continuous at
`(x₀,u₀)`.

Boundary: this is one-edge finite algebra plus continuity under a supplied
`Continuous Dbase` hypothesis.  It does not construct `Dbase`, prove source
coverage, source-measure transport, normal crossings, pole order, or RLCT.  It
also does not weaken the multi-edge intermediate-factor obstruction.

## 2026-06-25 A2 single-edge selected-entry product-coordinate readout

Reproduction:
`reproduction-a2-single-edge-selected-entry-product-coordinate-readout.md`.
Statement card:
`statement-card-a2-single-edge-selected-entry-product-coordinate-readout.md`.
Review:
`review-a2-single-edge-selected-entry-product-coordinate-readout.md`.

Lean now specializes the one-edge residual-matrix family to the finite
selected-entry chart coordinates:

```text
paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean
paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_singleEdgeSelectedEntryProductCoordinateEuclidean
continuousAt_paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean
```

The supplied residual matrix is
`AoyagiResidualBlockCoordinateIndex.matrix (fun c =>
SelectedEntrySignedBox.CenterCoord.chartMap pivot y (residualCoordEquiv c))`.
Under `IsUnit det(Ctop(u))`, the readout has regular part `u` and residual
coordinate `c` equal to the selected-entry chart coordinate at
`residualCoordEquiv c`.  The family is continuous because `CenterCoord.chartMap`
is continuous and matrices are continuous entrywise.

Boundary: this is one-edge finite coordinate readout only.  The
`residualCoordEquiv` alignment and determinant-unit hypothesis are explicit.
It does not invert the selected-entry chart, construct source coverage,
transport measures, produce normal crossings, prove pole order, or extract
RLCT.

## 2026-06-25 A2 single-edge selected-entry square-sum readout

Reproduction:
`reproduction-a2-single-edge-selected-entry-square-sum-readout.md`.
Statement card:
`statement-card-a2-single-edge-selected-entry-square-sum-readout.md`.
Review:
`review-a2-single-edge-selected-entry-square-sum-readout.md`.

Lean now proves:

```text
aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_singleEdgeSelectedEntryProductCoordinateEuclidean
```

The theorem turns the previous one-edge selected-entry coordinate readout into
the scalar residual equality

```text
aoyagiCoordinateSquareSum (residualBlockCoordinateMap (y,u))
  = SelectedEntrySignedBox.CenterCoord.residual pivot y.
```

The proof is finite: use the pointwise readout through the supplied
`residualCoordEquiv`, reindex the finite sum of squares, and apply
`CenterCoord.residual_eq_aoyagiCoordinateSquareSum_chartMap`.  The determinant
unit hypothesis is inherited from the coordinate readout.

Boundary: this is source-neutral one-edge finite square-sum algebra.  It does
not construct source coverage, source-stratum equality, source-measure
transport, local lower bounds, normal crossings, pole order, RLCT, or a
multi-edge selected-entry residual product.

## 2026-06-25 A2 single-edge selected-entry determinant-ball readout

Reproduction:
`reproduction-a2-single-edge-selected-entry-determinant-ball-readout.md`.
Statement card:
`statement-card-a2-single-edge-selected-entry-determinant-ball-readout.md`.
Review:
`review-a2-single-edge-selected-entry-determinant-ball-readout.md`.

Lean now proves:

```text
exists_pos_radius_le_forall_paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEuclidean_readout
```

For any positive `Rmax`, the theorem chooses `0<R<=Rmax` so that every regular
coordinate `u` in `ball(0,R)` satisfies the determinant-chart condition for
`Ctop(u)`.  On that ball, the previous one-edge selected-entry pointwise
readouts apply uniformly in the selected-entry parameter `y`: regular
coordinates read as `u`, residual coordinates read as
`chartMap pivot y (residualCoordEquiv c)`, and the residual square-sum is
`SelectedEntrySignedBox.CenterCoord.residual pivot y`.

Boundary: this is one-edge determinant-neighborhood plumbing.  It does not
construct the residual-index equivalence, source coverage, source-stratum
equality, source-measure transport, local lower bounds, normal crossings, pole
order, RLCT, or a multi-edge selected-entry residual product.

## 2026-06-25 A2 multi-edge residual-product preservation

Reproduction:
`reproduction-a2-multi-edge-residual-product-preservation.md`.
Statement card:
`statement-card-a2-multi-edge-residual-product-preservation.md`.
Review:
`review-a2-multi-edge-residual-product-preservation.md`.

Lean now proves the finite multi-edge residual-product preservation theorem in
`ProductReduction.lean`:

```text
ChartLocalSuffixState.schurResidualBlock_fromBlocks_upperRight_zero
ChartLocalSuffixState.schurResidualBlock_fromBlocks_lowerLeft_zero
ChartLocalSuffixState.residualProduct_eq_of_residualBlock_eq
ChartLocalSuffixState.suffixState_tail_fields_of_productCoordinateEdges_from
ChartLocalSuffixState.residualBlock_productCoordinateEdges_succSucc
ChartLocalSuffixState.residualProduct_productCoordinateEdges_succSucc_eq_base
```

For a chain with at least two edges, if the new raw p.13 product-coordinate
edge matrices use residual factors
`residualBlock Ebase (Fin.last (N+2)) p`, then every transformed Schur
residual block visited by the new suffix recursion agrees with the base one,
and therefore the ordered residual product agrees with the base residual
product.

Boundary: finite pointwise matrix algebra only.  This does not build the
dependent `G(x,u)` family, prove parameter-continuity, construct a product
chart, transport measures, produce normal crossings, prove pole order, or
extract RLCT.

## 2026-06-25 A2 multi-edge product-coordinate family constructor

Reproduction:
`reproduction-a2-multi-edge-product-coordinate-family-constructor.md`.
Statement card:
`statement-card-a2-multi-edge-product-coordinate-family-constructor.md`.
Review:
`review-a2-multi-edge-product-coordinate-family-constructor.md`.

Lean now proves the fixed-`Ebase` multi-edge product-coordinate constructor in
`RegularSuspensionCoordinates.lean`:

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_multiEdgeProductCoordinateEuclidean
```

For a chain with at least two edges, the constructor reads a Euclidean regular
coordinate vector `u` into `Ctop=I+X`, `F2`, and `F3`, chooses each new
residual factor as `residualBlock Ebase last p`, and assembles the raw p.13
edge matrices.  The fixed-base product-difference coordinate map of the
realised continuous edge family is

```text
Sum.elim (fun c => u c)
  (AoyagiResidualBlockCoordinateIndex.value (residualProduct Ebase last 0)).
```

The determinant hypothesis `IsUnit (Ctop(u)).det` is explicit and belongs to
the coordinate-readout theorem.  The proof reuses the raw
product-coordinate suffix-field theorem and the multi-edge residual-product
preservation theorem.

Boundary: still pointwise in a fixed base matrix family `Ebase`.  This does
not yet construct the source-dependent family `G(x,u)` from a base source edge
family, prove parameter-continuity, construct a product chart, transport
measures, produce normal crossings, prove pole order, or extract RLCT.

## 2026-06-25 A2 multi-edge source-dependent product-coordinate family

Reproduction:
`reproduction-a2-multi-edge-source-dependent-product-coordinate-family.md`.
Statement card:
`statement-card-a2-multi-edge-source-dependent-product-coordinate-family.md`.
Review:
`review-a2-multi-edge-source-dependent-product-coordinate-family.md`.

Lean now specializes the fixed-`Ebase` constructor to the fixed-base matrices
of a base source edge family `CedgeBase x`.  New names in
`RegularSuspensionCoordinates.lean`:

```text
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_residualProduct
paperEndpointFixedBaseRegularBlockCoordinateMap_congr_point
paperEndpointFixedBaseResidualBlockCoordinateMap_congr_point
paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily
```

At each point `(x,u)`, under `IsUnit (det(Ctop(u)))`, the constructed product
family has regular coordinates exactly `u` and residual coordinates equal to
the base residual coordinate map of `CedgeBase x`.

Boundary: pointwise finite coordinate algebra for at-least-two-edge chains.
The determinant-unit hypothesis is still explicit; no small-ball determinant
chart, parameter-continuity, source coverage, product chart, measure
transport, normal crossings, pole order, or RLCT extraction is proved.

## 2026-06-25 A2 Ctop determinant neighborhood

Reproduction:
`reproduction-a2-ctop-determinant-neighborhood.md`.
Statement card:
`statement-card-a2-ctop-determinant-neighborhood.md`.
Review:
`review-a2-ctop-determinant-neighborhood.md`.

Lean now proves the elementary determinant-neighborhood lemmas in
`RegularSuspensionCoordinates.lean`:

```text
AoyagiRegularBlockCoordinateIndex.continuous_ctopMatrix_euclidean
AoyagiRegularBlockCoordinateIndex.continuous_det_ctopMatrix_euclidean
AoyagiRegularBlockCoordinateIndex.ctopMatrix_zero
AoyagiRegularBlockCoordinateIndex.ctopMatrix_euclidean_zero
AoyagiRegularBlockCoordinateIndex.det_ctopMatrix_zero
AoyagiRegularBlockCoordinateIndex.det_ctopMatrix_euclidean_zero
AoyagiRegularBlockCoordinateIndex.isUnit_det_ctopMatrix_euclidean_zero
AoyagiRegularBlockCoordinateIndex.eventually_isUnit_det_ctopMatrix_euclidean_nhds_zero
AoyagiRegularBlockCoordinateIndex.exists_pos_ball_forall_isUnit_det_ctopMatrix_euclidean
AoyagiRegularBlockCoordinateIndex.exists_pos_radius_le_forall_isUnit_det_ctopMatrix_euclidean
```

The proof is the direct p.13 calculation: `Ctop(u)=I+X(u)`, so
`Ctop(0)=I`, `det(Ctop(0))=1`, the determinant is continuous in `u`, and the
real unit locus is open.  Therefore `IsUnit(det(Ctop(u)))` holds eventually
near `u=0` and on a positive Euclidean ball, shrinkable below any prescribed
positive radius.

Boundary: this only supplies the determinant-unit chart hypothesis near the
centered regular coordinate.  It does not prove product-family continuity in
`(x,u)`, source coverage, rank-stratum openness, signed-box pushforward,
density/Jacobian transport, normal crossings, pole order, or RLCT extraction.

## 2026-06-25 A2 residual block continuity support

Reproduction:
`reproduction-a2-residual-block-continuity-support.md`.
Statement card:
`statement-card-a2-residual-block-continuity-support.md`.
Review:
`review-a2-residual-block-continuity-support.md`.

Lean now proves the local continuity support for transformed Schur residual
blocks and residual products, and the resulting source-dependent
product-coordinate family continuity:

```text
continuous_productCoordinateRightEndpointMatrix
continuous_productCoordinateMiddleMatrix
continuous_productCoordinateLeftEndpointMatrix
continuousAt_chartLocalSuffixState_residualBlock
continuousAt_chartLocalSuffixState_residualProduct
continuous_matrix_toContinuousLinearMap
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousAt
paperEndpointFixedBaseContinuousEdges_residualBlock_continuousAt
paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_continuous
paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_continuousAt
AoyagiRegularBlockCoordinateIndex.continuous_f2Matrix_euclidean
AoyagiRegularBlockCoordinateIndex.continuous_f3Matrix_euclidean
continuousAt_paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
continuousAt_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
continuousAt_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase
```

The key mathematical point is that source residual factors are continuous only
under the recursive determinant-chart hypotheses for the base transformed
edges, because the Schur complement uses matrix inversion.  The residual
product continuity is obtained by rewriting the suffix-state `D` field with
`suffixState_D_eq_residualProduct`.

The product-coordinate matrix family is continuous at `(x0,u0)` by the
right-endpoint, middle-edge, and left-endpoint p.13 matrix formulas: `F2`,
`F3`, and `Ctop` are continuous in `u`, and the residual blocks are continuous
in `x` under the recursive chart hypotheses.  The realised edge family is then
continuous by composing with the fixed-base matrix-realisation map.  In the
self-base case `CedgeBase x0 = reverseEdge B`, the recursive chart hypotheses
are discharged by the existing fixed-base self-base determinant-chart theorem.

Boundary: this is a local conditional continuity theorem.  It does not prove
automatic recursive chart neighborhoods, product charts, source coverage,
signed-box pushforward, density/Jacobian transport, normal crossings, pole
order, or RLCT.

## 2026-06-25 A2 source-dependent product family small-ball coordinate identities

Reproduction:
`reproduction-a2-source-dependent-product-family-small-ball-coordinate-identities.md`.
Statement card:
`statement-card-a2-source-dependent-product-family-small-ball-coordinate-identities.md`.
Review:
`review-a2-source-dependent-product-family-small-ball-coordinate-identities.md`.

Lean now proves the small-radius wrapper

```text
exists_pos_radius_le_regular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily_nhdsWithin_source
```

for the multi-edge source-dependent product family.  Given any positive
regular-coordinate outer radius `Rmax`, it chooses `0 < R <= Rmax` such that,
eventually on the base source-rank stratum and uniformly for
`u in ball(0,R)`, the constructed product family has regular coordinates
exactly `u` and residual coordinates equal to those of the base source family.

The proof is intentionally pointwise in the source variable: the determinant
small-ball theorem supplies `IsUnit(det(Ctop(u)))`, and the existing
source-dependent product-family readout supplies the two coordinate
identities.  The source-filter statement follows from a pointwise-in-`x`
assertion.

Boundary: this does not prove product-family continuity, source coverage,
product-reduction certificates, triangular multiplier bounds, measure
transport, normal crossings, pole order, or RLCT.

## 2026-06-25 A2 product-family certificate and adapted lower bound

Reproduction:
`reproduction-a2-product-family-certificate-and-adapted-lower-bound.md`.
Statement card:
`statement-card-a2-product-family-certificate-and-adapted-lower-bound.md`.
Review:
`review-a2-product-family-certificate-and-adapted-lower-bound.md`.

Lean now proves the finite p.13 certificate and adapted lower-bound package for
the explicit source-dependent multi-edge product family:

```text
ChartLocalSuffixState.recursiveDetCharts_productCoordinateEdges_succSucc
paperEndpointFixedBaseProductReductionCertificate_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
exists_pos_radius_le_productReductionCertificate_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_nhdsWithin_source
paperEndpointFixedBaseTriangularMultiplierSquareSumProduct_exists_pos_eventually_le_of_recursiveDetCharts
exists_pos_radius_le_pos_const_triangularMultiplierSquareSumProduct_eventually_le_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase_nhdsWithin_source
exists_pos_radius_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase_nhdsWithin_source
```

The key calculation is that the explicit product-coordinate edge matrices have
recursive determinant charts whenever `det(Ctop(u))` is a unit.  In the
self-base case, the constructed product family is continuous at `(x0,0)`;
the pointwise certificate supplies determinant charts there, so the p.13
triangular multiplier square-sum product is locally bounded.  Combining this
with the small-ball coordinate identities and the existing adapted lower-bound
socket gives a positive constant `c` and a small radius `R` such that

```text
c * (squareSum(residual(CedgeBase x)) + squareSum(u))
  <= adaptedProductDifferenceSquareSum(CedgeProd(x,u))
```

eventually on the base source stratum and uniformly for `u in ball(0,R)`.

Boundary: this is still an adapted fixed-base product-difference lower bound,
not an original-loss comparison, product chart, source coverage result,
measure-transport theorem, normal-crossing certificate, pole-order theorem, or
RLCT extraction.

## 2026-06-25 A2 original-loss local integrability for the product family

Reproduction:
`reproduction-a2-original-loss-local-integrability-product-family.md`.
Statement card:
`statement-card-a2-original-loss-local-integrability-product-family.md`.
Review:
`review-a2-original-loss-local-integrability-product-family.md`.

Lean now composes the explicit self-base multi-edge product-family adapted
lower bound with the original square-Frobenius local finite-integral front end:

```text
exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_multiEdgeProductCoordinateEdgeFamily_selfBase_continuousAt_pos_density
```

For the concrete product-coordinate family
`paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean`,
the theorem no longer requires a supplied adapted product-difference lower
bound.  It obtains a radius `Rprod <= Rmax` and a positive constant from the
product-family theorem, then applies the existing original-loss local
integrability theorem at radius `Rprod`; the final radius is therefore still
bounded by the original `Rmax`.

Boundary: the signed-box source chart, weighted pushforward, residual
monomial lower bound, source-density monomial bound, transported density
factor, and positive exponent input remain supplied.  This is not source
coverage, density/Jacobian transport, normal crossings, pole order, or RLCT
extraction.

## 2026-06-25 A2 original-loss local integrability for the product family, edge-matrix form

Reproduction:
`reproduction-a2-original-loss-local-integrability-product-family-edge-matrix.md`.
Statement card:
`statement-card-a2-original-loss-local-integrability-product-family-edge-matrix.md`.
Review:
`review-a2-original-loss-local-integrability-product-family-edge-matrix.md`.

Lean now proves the measurable-edge-matrix variant:

```text
exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase_continuousAt_pos_density
```

This removes the global `Continuous CedgeBase` input from the previous
product-family original-loss front end.  The adapted lower bound still uses
only `ContinuousAt CedgeBase x0` plus the self-base equality, while
source-stratum and residual measurability are kept explicit through the
fixed-base edge-matrix measurability hypothesis.

Boundary: this is still not signed-box chart construction, pushforward
transport, residual monomial lower-bound production, density/Jacobian
computation, normal crossings, pole order, or RLCT extraction.

## 2026-06-25 A2 local-source signed-box and monomial-unit boundary

Reproduction:
`reproduction-a2-local-source-signed-box-monomial-unit-boundary.md`.
Statement card:
`statement-card-a2-local-source-signed-box-monomial-unit-boundary.md`.
Review:
`review-a2-local-source-signed-box-monomial-unit-boundary.md`.

Lean now proves a local-source version of the p.13 local finite-integral front
end and the chart-side monomial-unit bound package:

```text
exists_open_ae_restrict_localSource_prod_p13RegularCoordinates_loss_density_bounds
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource
signedBox_monomialLower_sourceDensityBounds_of_monomialUnits
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
```

The local-source theorem replaces the hard-coded full source-rank stratum by a
measurable source set `source`, so future p.13 chart work only needs to prove a
pushforward identity for the local chart image.  The monomial-unit theorem
derives the residual lower bound, source-density a.e.-measurability,
nonnegativity, and monomial upper bound from identities
`residual = unit * monomial` and `sourceDensity = unit * monomial` plus
a.e. unit bounds.

Boundary: this does not construct the local chart, prove source coverage,
prove the weighted pushforward/Jacobian formula, produce the monomial-unit
identities, extract normal crossings, compute pole order, or prove an RLCT
claim.

## 2026-06-25 A2 local-source monomial-unit finite-integral wrapper

Reproduction:
`reproduction-a2-local-source-monomial-unit-finite-integral-wrapper.md`.
Statement card:
`statement-card-a2-local-source-monomial-unit-finite-integral-wrapper.md`.
Review:
`review-a2-local-source-monomial-unit-finite-integral-wrapper.md`.

Lean now proves the local-source signed-box finite-integral handoff directly
from supplied monomial-times-unit residual and source-density data:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialUnits_edgeMatrix
```

This is a consumer theorem for a supplied local residual chart.  The theorem
uses the earlier monomial-unit inequality package to derive the residual lower
bound, source-density a.e.-measurability, source-density nonnegativity, and
source-density monomial upper bound required by the local-source signed-box
finite-integral theorem.

Boundary: the measurable local source, signed-box source chart, weighted
pushforward, residual monomial-unit identity, source-density monomial-unit
identity, density/Jacobian formula, normal-crossing extraction, pole order, and
RLCT extraction remain supplied or cited outside this slice.

## 2026-06-25 A2 local-source adapted-loss finite-integral socket

Reproduction:
`reproduction-a2-local-source-adapted-loss-finite-integral-socket.md`.
Statement card:
`statement-card-a2-local-source-adapted-loss-finite-integral-socket.md`.
Review:
`review-a2-local-source-adapted-loss-finite-integral-socket.md`.

Lean now proves the local-source analogue of the adapted-loss comparison
finite-integral socket:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_const_mul_adaptedProductDifferenceSquareSum_le_loss
```

It multiplies the adapted product-difference lower bound by the positive
adapted-to-loss comparison constant, then applies the local-source p.13
finite-integral theorem.  The residual positivity/integrability and density
bounds remain local-source hypotheses.

Boundary: this does not prove the adapted product-coordinate lower bound, the
adapted-to-original loss comparison, local chart construction, source coverage,
density/Jacobian transport, normal crossings, pole order, or RLCT.

## 2026-06-25 A2 original-loss local-source finite-integral socket

Reproduction:
`reproduction-a2-original-loss-local-source-finite-integral-socket.md`.
Statement card:
`statement-card-a2-original-loss-local-source-finite-integral-socket.md`.
Review:
`review-a2-original-loss-local-source-finite-integral-socket.md`.

Lean now proves the local-source original square-Frobenius loss specialization:

```text
exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_adaptedProductDifferenceSquareSum_lower
```

The theorem defines the concrete endpoint `lossDLN` on the product chart,
uses the finite endpoint basis comparison to prove
`c0 * adaptedSquareSum <= lossDLN`, and delegates to the local-source
adapted-loss finite-integral socket.  The measurable source set, residual
positivity/integrability, adapted lower bound, and density bounds remain
explicit hypotheses.

Boundary: this is a Lean plumbing theorem, not a source-stated p.13 chart
construction.  It does not construct the local source, prove source coverage,
prove signed-box pushforward or Jacobian/density transport, produce residual
or source-density monomial-unit identities, prove normal crossings, compute
pole order, or extract RLCT.

## 2026-06-25 A2 measurable local source from source certificate

Reproduction:
`reproduction-a2-measurable-local-source-from-source-certificate.md`.
Statement card:
`statement-card-a2-measurable-local-source-from-source-certificate.md`.
Review:
`review-a2-measurable-local-source-from-source-certificate.md`.

Lean now proves the certificate-level and source-data-level measurable local
source package:

```text
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_measurable_localSource
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_measurable_localSource_of_measurable_edgeMatrix
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_measurable_localSource_nhdsWithin_of_measurable_edgeMatrix
```

The local source is `U inter sourceRankStratum`, with `U` an open neighborhood
of the basepoint extracted from the certificate's `nhdsWithin` data.  The
source-data wrapper derives source-rank-stratum measurability from fixed-base
edge-matrix measurability and proves that the local source has the same
`nhdsWithin x0` filter as the full source-rank stratum.

Boundary: this moves source packaging, not the chart itself.  It does not
construct a signed-box chart, prove source coverage/image, prove pushforward or
Jacobian/source-density transport, produce residual/source-density monomial
units, prove normal crossings, compute pole order, or extract RLCT.

## 2026-06-25 A2 local-source product-family adapted lower bound

Reproduction:
`reproduction-a2-local-source-product-family-adapted-lower-bound.md`.
Statement card:
`statement-card-a2-local-source-product-family-adapted-lower-bound.md`.
Review:
`review-a2-local-source-product-family-adapted-lower-bound.md`.

Lean now packages the explicit self-base multi-edge p.13 product-coordinate
adapted lower bound over the measurable local source extracted from the source
certificate:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_measurable_localSource_pos_radius_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase
```

The theorem returns `source = sourceU inter sourceRankStratum`,
`MeasurableSet source`, `x0 in source`, `source subset sourceRankStratum`,
source-rank conclusions on `source`, the equality
`nhdsWithin x0 source = nhdsWithin x0 sourceRankStratum`, positive `R <= Rmax`
and `c`, and the adapted product-family lower bound on `nhdsWithin x0 source`.

Boundary: this is finite/local-coordinate packaging.  It does not construct a
signed-box chart, prove source image/coverage, prove weighted pushforward or
Jacobian/source-density transport, compare to original/KL loss, produce
residual/source-density monomial units, prove normal crossings, compute pole
order, or extract RLCT.

## 2026-06-25 A2 local-source original-loss product-family continuation

Reproduction:
`reproduction-a2-local-source-original-loss-product-family-continuation.md`.
Statement card:
`statement-card-a2-local-source-original-loss-product-family-continuation.md`.
Review:
`review-a2-local-source-original-loss-product-family-continuation.md`.

Lean now composes the measurable local-source product-family adapted lower
bound with the local-source original-loss finite-integral socket:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_measurable_localSource_forall_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_multiEdgeProductCoordinateEdgeFamily_selfBase
```

The theorem returns `source = sourceU inter sourceRankStratum`,
`MeasurableSet source`, `x0 in source`, source-stratum inclusion, source-rank
facts, the `nhdsWithin` equality, positive `R <= Rmax` and `c`, and a
continuation: once residual positivity/integrability and density bounds are
supplied on the returned local source, the finite local integral for the
concrete endpoint square-Frobenius `lossDLN` follows.

Boundary: this is a conditional composition wrapper, not an Aoyagi-stated
chart theorem.  It does not construct a signed-box chart, prove source
image/coverage, prove weighted pushforward or Jacobian/source-density
transport, produce residual/source-density monomial units, prove residual
integrability, prove normal crossings, compute pole order, or extract RLCT.

## 2026-06-25 A2 selected-entry signed-box monomial-unit data

Reproduction:
`reproduction-a2-selected-entry-signed-box-monomial-unit-data.md`.
Statement card:
`statement-card-a2-selected-entry-signed-box-monomial-unit-data.md`.
Review:
`review-a2-selected-entry-signed-box-monomial-unit-data.md`.

Lean now proves concrete signed-box monomial-unit data for the elementary
selected-entry pivot chart:

```text
SelectedEntrySignedBox.residual_eq_unit_mul_abs_monomial
SelectedEntrySignedBox.sourceDensity_eq_abs_pivotFirstJacobian_det
SelectedEntrySignedBox.sourceDensity_eq_unit_mul_abs_monomial
SelectedEntrySignedBox.monomialUnitHypotheses
SelectedEntrySignedBox.monomialLower_sourceDensityBounds
SelectedEntrySignedBox.CenterCoord.monomialUnitHypotheses
SelectedEntrySignedBox.CenterCoord.monomialLower_sourceDensityBounds
```

The coordinate index is `Option {i // i in center.erase pivot}`.  The `none`
coordinate is the selected pivot variable `u`; the `some` coordinates are the
non-pivot residual variables.  The exponents are `k none = 1`,
`k (some _) = 0`, `h none = (center.erase pivot).card`, and
`h (some _) = 0`.  The residual unit is
`1 + sum_{i in center.erase pivot} residual_i^2`, and the density unit is
`1`.  The `CenterCoord` namespace restates the same package over
`center -> R`, with zero exponents away from the pivot, for downstream Case 2
source-coordinate use.

Boundary: this is only selected-entry finite algebra plus formal absolute
determinant data.  It does not construct the local chart source, prove source
coverage, prove a weighted pushforward or analytic Jacobian/source-density
identity, compare to the full DLN loss, prove normal crossings, compute pole
order, or extract RLCT.

## 2026-06-25 A2 selected-entry local-source finite-integral handoff

Reproduction:
`reproduction-a2-selected-entry-local-source-finite-integral-handoff.md`.
Statement card:
`statement-card-a2-selected-entry-local-source-finite-integral-handoff.md`.
Review:
`review-a2-selected-entry-local-source-finite-integral-handoff.md`.

Lean now plugs the center-indexed selected-entry signed-box data into the
local-source p.13 finite-integral socket:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_selectedEntryCenter_signedBox_withDensity_edgeMatrix
```

The theorem assumes a supplied local source chart, weighted pushforward
identity, and equality between the fixed-base residual block square-sum and
`SelectedEntrySignedBox.CenterCoord.residual pivot`.  It discharges the
selected-entry residual/source-density monomial-unit hypotheses and reduces
the coordinatewise threshold to the pivot inequality
`2 * t < (center.erase pivot.1).card + 1`.

Boundary: this remains conditional local-source plumbing.  It does not
construct the selected-entry chart source, prove source image/coverage,
weighted pushforward, analytic Jacobian/source-density transport, original
loss comparison, normal crossings, pole order, or RLCT.

## 2026-06-25 A2 selected-entry chart Jacobian pushforward

Reproduction:
`reproduction-a2-selected-entry-chart-jacobian-pushforward.md`.
Statement card:
`statement-card-a2-selected-entry-chart-jacobian-pushforward.md`.
Review:
`review-a2-selected-entry-chart-jacobian-pushforward.md`.

Lean now proves the actual finite center-indexed selected-entry chart
Jacobian and signed-box weighted pushforward:

```text
SelectedEntrySignedBox.CenterCoord.chartMapFDeriv_det
SelectedEntrySignedBox.CenterCoord.sourceDensity_eq_abs_chartMapFDeriv_det
SelectedEntrySignedBox.CenterCoord.measurableSet_chartMap_image_signedBoxSet
SelectedEntrySignedBox.CenterCoord.map_chartMap_restrict_withDensity_sourceDensity_eq_restrict_image_of_subset_pivot_ne_zero
SelectedEntrySignedBox.CenterCoord.map_chartMap_restrict_nonzeroSignedBox_withDensity_sourceDensity_eq_restrict_image
SelectedEntrySignedBox.CenterCoord.map_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image
```

The proof first applies Mathlib's Jacobian change-of-variables theorem on a
null-measurable source set contained in `{y | y pivot != 0}`, where the chart
is injective.  It then recovers the full signed-box statement using the
Lebesgue-null pivot hyperplane on the source and target sides.

Review found no mathematical fidelity issue.  Follow-up fixes added chart-image
measurability for downstream wrappers, corrected the module docstring, and
removed an unnecessary normal-crossing import.

Boundary: this proves the finite chart transport for the concrete
center-indexed selected-entry map.  It still does not construct the p.13
source chart inside the original DLN parameter space, prove source
image/coverage, identify the original source measure with this chart-image
restriction, compare the full DLN loss, produce normal crossings, compute pole
order, or extract RLCT.

## 2026-06-25 A2 selected-entry chart-image local handoff

Reproduction:
`reproduction-a2-selected-entry-chart-image-local-handoff.md`.
Statement card:
`statement-card-a2-selected-entry-chart-image-local-handoff.md`.
Review:
`review-a2-selected-entry-chart-image-local-handoff.md`.

Lean now specializes the selected-entry local-source finite-integral handoff
to the finite chart image:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix
```

The theorem sets
`source = SelectedEntrySignedBox.CenterCoord.chartMap pivot ''
SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres`,
`sourceChart = SelectedEntrySignedBox.CenterCoord.chartMap pivot`, and
`μ = volume`.  The finite selected-entry chart transport theorem supplies the
weighted pushforward, chart-image measurability supplies `hsource_meas`, and
continuity supplies chart a.e.-measurability.

Independent xhigh review found no mathematical fidelity issue.  The reviewer
checked that the assumptions and conclusion are over the finite chart image,
not an original DLN source.

Boundary: this is a finite chart-image wrapper.  It does not identify the
chart image with an original DLN source neighborhood, prove original source
coverage or source-measure equality, compare full DLN loss, produce normal
crossings, compute pole order, or extract RLCT.

## 2026-06-25 A2 selected-entry chart-image original-loss wrapper

Reproduction:
`reproduction-a2-selected-entry-chart-image-original-loss-wrapper.md`.
Statement card:
`statement-card-a2-selected-entry-chart-image-original-loss-wrapper.md`.
Review:
`review-a2-selected-entry-chart-image-original-loss-wrapper.md`.

Lean now proves the finite chart-image original-loss wrapper:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix_adaptedProductDifferenceSquareSum_lower
```

The theorem keeps the source as
`SelectedEntrySignedBox.CenterCoord.chartMap pivot ''
SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres`.  It combines the
selected-entry chart-image local-measure handoff with the finite endpoint
basis comparison from adapted product-difference Frobenius loss to original
`lossDLN`.  The adapted-product lower bound, residual identity along the
selected-entry chart, edge-matrix measurability, pivot integrability threshold,
and density bounds remain explicit hypotheses on the finite chart image.

The same Lean file also contains a source-stratum-equality specialization,
but its source identification is an explicit hypothesis, not a proof of p.13
source coverage.

Independent xhigh review found no issue.  It checked that the main theorem
integrates over the finite chart image, keeps the adapted-product lower bound
explicit, and that the source-stratum variant is conditional.

Boundary: this still does not construct an original DLN p.13 source chart,
prove source-rank stratum coverage or original-source measure identity, derive
the adapted-product lower bound from original-source coordinates, produce
normal crossings, compute pole order, or extract RLCT.

## 2026-06-25 A2 selected-entry local source-stratum original-loss bridge

Reproduction:
`reproduction-a2-selected-entry-local-source-stratum-original-loss-bridge.md`.
Statement card:
`statement-card-a2-selected-entry-local-source-stratum-original-loss-bridge.md`.
Review:
`review-a2-selected-entry-local-source-stratum-original-loss-bridge.md`.

Lean now proves a local-equality version of the selected-entry source-stratum
original-loss endpoint:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_eq_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase
```

The theorem replaces the previous global equality hypothesis

```text
sourceStratum = chartMap pivot '' signedBoxSet Rres
```

with a supplied open neighborhood `Ulocal` of `x0` and a local equality

```text
Ulocal ∩ sourceStratum =
Ulocal ∩ (chartMap pivot '' signedBoxSet Rres).
```

The proof transports source-stratum eventual bounds to the finite chart-image
filter, applies the finite chart-image original-loss wrapper, and then shrinks
the returned open set into `Ulocal` before rewriting the restricted measure.
Focused build passed for
`DLNFibre.DLN.Aoyagi.SelectedEntryOriginalLossLocalMeasure`.
Independent xhigh review accepted the theorem boundary and the local
filter/restricted-measure shrink.

Boundary: the local source/image equality is an explicit hypothesis.  This
still does not construct the p.13 source chart, prove source-rank image or
coverage, prove original-source measure transport, produce normal crossings,
compute pole order, or extract RLCT.

## 2026-06-25 A2 selected-entry source-chart coverage boundary

Reproduction:
`reproduction-a2-selected-entry-source-chart-coverage-boundary.md`.

Fresh xhigh source/API scouting checked Aoyagi PDF pp. 15-21 against the
current selected-entry source-stratum endpoint.  The printed proof displays the
top-left selected-entry chart in Case 1 (2) and Case 2 and performs the
elementary `Q/P` Schur cleanup there.  It does not state an all-pivot affine
cover, sector decomposition, or chart-overlap analysis.

Controller decision: keep source image/coverage supplied.  The next honest
Lean target is only the residual-coordinate algebra under an explicit
coordinate-readout bridge, beginning with the elementary identity
`CenterCoord.residual pivot y = aoyagiCoordinateSquareSum (chartMap pivot y)`.

Statement card:
`statement-card-a2-selected-entry-residual-coordinate-square-sum.md`.
Review:
`review-a2-selected-entry-residual-coordinate-square-sum.md`.

Lean now proves the square-sum reindexing utility, the selected-entry
center-coordinate residual square-sum identity, and a source-neutral
coordinate-readout bridge.  The bridge requires an explicit finite equivalence
and pointwise coordinate readout; it does not construct the fixed-base residual
map readout.

## 2026-06-25 A2 selected-entry original-loss readout wrapper

Reproduction:
`reproduction-a2-selected-entry-original-loss-readout-wrapper.md`.
Statement card:
`statement-card-a2-selected-entry-original-loss-readout-wrapper.md`.
Review:
`review-a2-selected-entry-original-loss-readout-wrapper.md`.

Lean now proves the local source-stratum original-loss endpoint with the raw
scalar `hresidual_eq` socket replaced by explicit residual-coordinate readout:
a finite equivalence from fixed-base residual indices to selected-entry center
coordinates, plus pointwise readout along `chartMap pivot`.  It derives the
old scalar square-sum hypothesis using the finite square-sum bridge and then
delegates to the existing endpoint.  Source coverage and the readout itself
remain supplied.

## 2026-06-25 A2 selected-entry residual-product matrix readout

Reproduction:
`reproduction-a2-selected-entry-residual-product-matrix-readout.md`.
Statement card:
`statement-card-a2-selected-entry-residual-product-matrix-readout.md`.
Review:
`review-a2-selected-entry-residual-product-matrix-readout.md`.

Lean now proves that a supplied fixed-base suffix residual-product matrix
identity at a selected-entry chart point implies the pointwise residual
coordinate readout required by the original-loss wrapper.  This is the natural
next layer below the pointwise readout hypothesis: it reduces future source
residual-readout subgoal to constructing the residual-product matrix formula
for `CedgeBase`.
It does not construct `CedgeBase`, prove source image/coverage, construct the
residual-index equivalence, or prove the matrix formula.
Independent xhigh review passed after wording fixes to keep the source
boundary precise.

## 2026-06-25 A2 selected-entry prescribed-matrix readout

Reproduction:
`reproduction-a2-selected-entry-prescribed-matrix-readout.md`.
Statement card:
`statement-card-a2-selected-entry-prescribed-matrix-readout.md`.
Review:
`review-a2-selected-entry-prescribed-matrix-readout.md`.

Lean now proves that a prescribed fixed-base matrix family with a supplied
selected-entry residual-product matrix identity gives the same pointwise
readout after those matrices are realised as continuous reverse edges.  This
is the layer expected if the future source-chart algebra is phrased directly
in fixed-base edge matrices.  It does not construct the matrix family, prove
the residual-product identity, construct the residual-index equivalence, or
prove source image/coverage.
Independent xhigh review passed after wording fixes to avoid implying that the
theorem packages a source chart.

## 2026-06-25 A2 residual-product factor frontier

Reproductions:
`reproduction-a2-residual-factor-product.md` and
`reproduction-a2-product-coordinate-residual-product-preservation.md`.
Statement cards:
`statement-card-a2-residual-factor-product.md` and
`statement-card-a2-product-coordinate-residual-product-preservation.md`.
Review:
`review-a2-residual-product-factor-frontier.md`.

Lean now defines
`ChartLocalSuffixState.residualFactorProduct`, the explicit decreasing
endpoint product of supplied residual factors, and proves:

```text
ChartLocalSuffixState.residualProduct_eq_residualFactorProduct_of_residualBlock_eq
ChartLocalSuffixState.residualProduct_productCoordinateEdges_succSucc_eq_residualFactorProduct
paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean_residualProduct_eq_base
```

The first theorem says that if every suffix transformed Schur residual block
below the endpoint `j` is a supplied factor `C p`, then the suffix residual
product is the explicit ordered factor product.  The second
specializes this to raw multi-edge p.13 product-coordinate matrices.  The
third exposes the existing fixed-base product-coordinate constructor's base
residual-product preservation as a named theorem.

This is an intermediate-factor API.  It does not prove that the factor product
is Aoyagi's selected-entry matrix, does not construct residual factors from
source data, does not realize an arbitrary final residual matrix in the
multi-edge case, does not construct a fixed-base source chart or residual-index
equivalence, and does not prove source coverage, source-measure transport,
normal crossings, pole order, or RLCT.

## 2026-06-25 A2 residual-factor rank obstruction

Reproduction:
`reproduction-a2-residual-factor-product-rank-obstruction.md`.
Statement card:
`statement-card-a2-residual-factor-product-rank-obstruction.md`.
Review:
`review-a2-residual-factor-product-rank-obstruction.md`.

Lean now proves:

```text
ChartLocalSuffixState.residualFactorProduct_trans
ChartLocalSuffixState.rank_residualFactorProduct_le_card_intermediate
```

The split law says an explicit residual-factor product factors through any
intermediate residual index `q`.  Over a nontrivial coefficient ring, the rank
of the terminal product is therefore bounded by `card (kappa q)`.  This
formalises the obstruction found in pen-and-paper review: a multi-edge
residual product cannot realize an arbitrary terminal matrix unless the
desired matrix is compatible with all intermediate residual dimensions.

This is finite matrix algebra only.  It does not decide whether Aoyagi's
displayed selected-entry residual matrix has a suitable factorization, does
not construct source factors, source coverage, source-measure transport,
normal crossings, pole order, or RLCT.

## 2026-06-25 A2 p.13 residual-factor product boundary audit

Source/API audit:
`source-audit-a2-p13-residual-factor-product-boundary.md`.

After interruption recovery, xhigh scout `Hilbert` rechecked Aoyagi p.13
against the current residual-factor API.  The audited source-backed theorem is
exactly the already-landed ordered-product statement

```text
ChartLocalSuffixState.residualProduct_productCoordinateEdges_succSucc_eq_residualFactorProduct
```

together with the fixed-base preservation consumer

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean_residualProduct_eq_base.
```

This confirms the current boundary: multi-edge selected-entry work still needs
compatible residual factors plus an explicit product identity to the
selected-entry matrix and a residual-index equivalence.  A terminal
selected-entry matrix alone must not be inserted into a multi-edge residual
product because the rank/split obstruction through intermediate residual
types is real.

## 2026-06-25 A2 selected-entry residual-factor constructor readout

Reproduction:
`reproduction-a2-selected-entry-residual-factor-constructor-readout.md`.
Statement card:
`statement-card-a2-selected-entry-residual-factor-constructor-readout.md`.
Review:
`review-a2-selected-entry-residual-factor-constructor-readout.md`.

Lean now composes the fixed-base residual-factor product-coordinate
constructor with the selected-entry prescribed-matrix readout bridge:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_residualFactorProduct_eq_matrix
```

The theorem takes supplied `uBase`, supplied compatible factors `Cfac`, a
residual-index equivalence, and a factor-product identity for
`Cfac (SelectedEntrySignedBox.CenterCoord.chartMap pivot y)`.  It realizes the
fixed-base matrices from
`paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfResidualFactorsEuclidean`,
uses the constructor theorem
`..._residualProduct_eq_residualFactorProduct`, and returns the pointwise
selected-entry residual-coordinate readout needed by the original-loss local
socket.

This is finite p.13 product-coordinate/readout composition only.  It does not
construct `Cfac`, prove the selected-entry factor-product identity, construct
the residual-index equivalence, prove local source/image equality, transport
measure, produce normal crossings, compute pole order, or prove RLCT.

## 2026-06-25 A2 residual-factor product two-edge unfold

Reproduction:
`reproduction-a2-residual-factor-product-two-edge-unfold.md`.
Statement card:
`statement-card-a2-residual-factor-product-two-edge-unfold.md`.
Review:
`review-a2-residual-factor-product-two-edge-unfold.md`.

Lean now proves the generic two-edge unfold:

```text
ChartLocalSuffixState.residualFactorProduct_fin_two_eq_mul
```

For a supplied residual-factor family over `Fin 2`, the product from
`Fin.last 2` to `0` is the right factor followed by the left factor, with the
two factors cast to the canonical middle endpoint `(1 : Fin 3)`.  This is the
generic API needed before any future Case 2 local two-factor product is
threaded into a residual-factor statement.

The bespoke displayed Case 2 dependent `Fin 3` package is still not added:
it would need endpoint equivalences from the fixed-base residual types to the
Case 2 post-pivot row/column/following-factor types and an equality with the
selected-entry coordinate matrix before it becomes a real readout input.

## 2026-06-25 A2 Case 2 residual-factor product reindex

Reproduction:
`reproduction-a2-case2-residual-factor-product-reindex.md`.
Statement card:
`statement-card-a2-case2-residual-factor-product-reindex.md`.
Review:
`review-a2-case2-residual-factor-product-reindex.md`.

Lean now proves:

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_residualFactorProduct_submatrix
```

This theorem takes a supplied two-edge residual-factor family, explicit
endpoint equivalences, and the two factor identities identifying its factors
with the Case 2 post-pivot residual block and following-factor tail.  It then
reindexes the generic two-edge `residualFactorProduct` and recovers
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct`.

This is the guarded bridge that the previous two-edge unfold made possible.
It still does not construct the displayed Case 2 `Cfac`, fixed-base endpoint
equivalences, selected-entry matrix RHS identity, source/image equality,
normal crossings, pole order, or RLCT.

## 2026-06-25 A2 Case 2 residual-coordinate index pivot entries

Reproduction:
`reproduction-a2-case2-residual-coordinate-index-pivot-entries.md`.
Statement card:
`statement-card-a2-case2-residual-coordinate-index-pivot-entries.md`.
Review:
`review-a2-case2-residual-coordinate-index-pivot-entries.md`.

Lean now proves:

```text
case2ResidualBlockCoordinateIndexEquivPivotEntries
```

For the Case 2 residual block, the p.13 residual scalar-coordinate index
`AoyagiResidualBlockCoordinateIndex row col` is equivalent to the finite
selected-entry center `case2ResidualBlockPivotEntries n S J`.  This packages
the source-backed rectangular index provenance checked for Aoyagi pp. 19-22.

This helps the future `residualCoordEquiv` socket, but it is finite
bookkeeping only.  It does not construct a selected-entry chart, compatible
residual factors, a selected-entry matrix RHS, source/image equality, normal
crossings, pole order, or RLCT.

## 2026-06-25 A2 Case 2 residual-coordinate endpoint-equivalence composition

Reproduction:
`reproduction-a2-case2-residual-coordinate-endpoint-equivalence-composition.md`.
Statement card:
`statement-card-a2-case2-residual-coordinate-endpoint-equivalence-composition.md`.
Review:
`review-a2-case2-residual-coordinate-endpoint-equivalence-composition.md`.

Lean now proves:

```text
case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
case2ResidualBlockCoordinateIndexEquivPivotEntriesOfCase2EndpointEquivs
```

Given supplied endpoint row and column equivalences to
`Case2ResidualRowIndex n S J` and `Case2ResidualColIndex n S J`, the full
endpoint residual scalar-coordinate product is equivalent to
`case2ResidualBlockPivotEntries n S J`.  The second theorem is the same
composition with the equivalences oriented out of the Case 2 types, matching
the factor-product reindex bridge.  This sharpens the future
`residualCoordEquiv` socket: the source-moving obligation is now exactly the
two endpoint equivalences, not the product assembly.

This remains finite bookkeeping only.  It does not construct the endpoint
equivalences, a selected-entry chart, compatible residual factors, a
selected-entry matrix RHS, source/image equality, normal crossings, pole order,
or RLCT.

## 2026-06-25 A2 Case 2 residual-factor product selected-center matrix

Reproduction:
`reproduction-a2-case2-residual-factor-product-selected-center-matrix.md`.
Statement card:
`statement-card-a2-case2-residual-factor-product-selected-center-matrix.md`.
Review:
`review-a2-case2-residual-factor-product-selected-center-matrix.md`.

Lean now proves:

```text
Matrix.eq_of_submatrix_equiv_eq
residualFactorProduct_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_submatrix
```

The theorem composes the guarded displayed-product bridge with a supplied
selected-center RHS equality and then uses equivalence-submatrix faithfulness
to remove the wrapper.  The resulting statement is the exact matrix identity
expected by the selected-entry residual-factor readout socket.

The post-pivot domains are `(S,J+1)`, matching Aoyagi's continuing Case 2
branch.  The theorem still does not prove the displayed RHS, construct
`Cfac`, construct endpoint equivalences, produce `Cprime` from source data,
or prove source/image equality, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 Case 2 displayed-product entrywise selected-center RHS

Reproduction:
`reproduction-a2-case2-displayed-product-entrywise-selected-center-rhs.md`.
Statement card:
`statement-card-a2-case2-displayed-product-entrywise-selected-center-rhs.md`.
Review:
`review-a2-case2-displayed-product-entrywise-selected-center-rhs.md`.

Lean now proves:

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_centerCoordinateSubmatrix_of_entrywise
residualFactorProduct_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
```

The first theorem turns an entrywise displayed selected-center readout into
the matrix submatrix RHS required by the previous bridge.  The second theorem
composes this with the Case 2 residual-factor product bridge, so future source
work can supply pointwise displayed entries rather than a full matrix equality.

This remains finite matrix extensionality.  The entrywise readout itself,
compatible factors, endpoint equivalences, source production of `Cprime`,
source/image equality, normal crossings, pole order, and RLCT remain open.

## 2026-06-26 A2 Case 2 displayed-product successor source-chart map

Reproduction:
`reproduction-a2-case2-displayed-product-successor-source-chart-map.md`.
Statement card:
`statement-card-a2-case2-displayed-product-successor-source-chart-map.md`.
Review:
`review-a2-case2-displayed-product-successor-source-chart-map.md`.

Lean now proves:

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_successorSourceChartMapMatrix_of_entrywise
```

Given an entrywise readout of the displayed post-pivot lower product into the
successor Case 2 source-chart map, and a supplied column endpoint equivalence
`tau ~= Case2ResidualColIndex n S (J+1)`, the displayed product is the matrix
whose entries are those successor source-chart coordinates.  The row endpoint
is the definitional successor Case 2 row domain, and the product-index
assembly uses
`case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs`.

This is finite endpoint reindexing only.  The entrywise successor source-chart
readout, selected-center readout, compatible factors, endpoint/source data,
source/image equality, normal crossings, pole order, and RLCT remain open.

## 2026-06-26 A2 Case 2 displayed-product entry expansion

Reproduction:
`reproduction-a2-case2-displayed-product-entry-expansion.md`.
Statement card:
`statement-card-a2-case2-displayed-product-entry-expansion.md`.
Review:
`review-a2-case2-displayed-product-entry-expansion.md`.

Lean now proves:

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_apply
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_apply_eq_sum_freeCprime
```

For every continuing row `i` and target column `t`, the displayed post-pivot
lower product is the finite sum over
`Case2ResidualColIndex n S (J+1)` of the post-pivot residual block entry times
the transported following-factor tail entry.  This is the entrywise form of
the source-supported product `D_(J+1) * C'_+`.

This remains finite matrix multiplication only.  It does not prove any
selected-center readout, successor source-chart readout, endpoint equivalence,
source/image equality, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 Case 2 source-chart CenterCoord alignment

Reproduction:
`reproduction-a2-case2-source-chart-centercoord-alignment.md`.
Statement card:
`statement-card-a2-case2-source-chart-centercoord-alignment.md`.
Review:
`review-a2-case2-source-chart-centercoord-alignment.md`.

Lean now proves:

```text
case2DisplayedSourceChartMap_eq_selectedEntrySignedBoxCenterCoord_chartMap_apply
```

The displayed Case 2 source-chart map on the old center
`case2ResidualBlockPivotEntries n S J` is definitionally the same finite map
as `SelectedEntrySignedBox.CenterCoord.chartMap` at the displayed pivot
`(J+1,J+1)`.  This gives downstream selected-entry chart/measure code a
shared vocabulary for the source-supported old chart.

This is not a post-pivot product readout.  It does not identify
`D_(J+1) * C'_+` with selected-center or successor source-chart coordinates,
and it proves no source/image equality, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 Case 2 successor readout CenterCoord matrix

Reproduction:
`reproduction-a2-case2-successor-readout-centercoord-matrix.md`.
Statement card:
`statement-card-a2-case2-successor-readout-centercoord-matrix.md`.
Review:
`review-a2-case2-successor-readout-centercoord-matrix.md`.

Lean now proves:

```text
residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
```

Given a supplied entrywise successor source-chart readout for the displayed
post-pivot lower product, plus the residual-factor identities and endpoint
equivalences, the unreindexed two-edge residual-factor product is exactly the
successor `SelectedEntrySignedBox.CenterCoord.chartMap` matrix.  This composes
the Case 2 product bridge with the old/source selected-entry chart vocabulary
alignment.

This is still conditional finite plumbing.  It does not prove the successor
readout, construct endpoint equivalences or factors, produce `Cprime`, prove
source/image equality, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 Case 2 concrete two-edge factor family

Reproduction:
`reproduction-a2-case2-concrete-two-edge-factor-family.md`.
Statement card:
`statement-card-a2-case2-concrete-two-edge-factor-family.md`.
Review:
`review-a2-case2-concrete-two-edge-factor-family.md`.

Lean now proves:

```text
case2PostPivotTwoEdgeDomain
case2PostPivotFreeTwoEdgeFactorFamily
residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_freeTwoEdgeFactorProduct
residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_entrywise
```

The concrete endpoint family is the displayed Case 2 two-edge chain
`tau -> Case2ResidualColIndex n S (J+1) -> Case2ResidualRowIndex n S (J+1)`.
The residual-factor product for this family is exactly
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct`, so callers no longer need
to supply a generic `kappa`, endpoint equivalences, or the two factor
identities when they are already in this displayed Case 2 chain.  The
successor selected-entry matrix theorem composes this specialization with a
supplied successor entrywise readout.

This remains a finite socket reducer.  The successor readout, source
production of `Cprime`, successor source data, source/image equality, normal
crossings, pole order, and RLCT remain supplied or open.

## 2026-06-26 A2 Case 2 paper-Cprime source-following factor product

Reproduction:
`reproduction-a2-case2-paper-cprime-source-following-factor-product.md`.
Statement card:
`statement-card-a2-case2-paper-cprime-source-following-factor-product.md`.
Review:
`review-a2-case2-paper-cprime-source-following-factor-product.md`.

Lean now proves:

```text
residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_paperCprime_eq_sourceResidualBlock_successorFollowingFactor
```

For Aoyagi's paper transformed following factor `C' = Q^-1 C`, the concrete
Case 2 two-edge residual-factor product rewrites as the source residual block
at `(S,J+1)` times the formula-level successor following factor restricted to
that same next residual domain.  This uses the existing source-supported
paper-`C'` tail identity and the zero-extended post-pivot source residual
representative.

This is finite product-reduction algebra only.  It does not construct
successor source data, selected-entry readout, source/image equality, chart
coverage, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 Case 2 post-pivot compatible residual-factor identity audit

Reproduction:
`reproduction-a2-case2-post-pivot-compatible-residual-factor-identity.md`.
Statement card:
`statement-card-a2-case2-post-pivot-compatible-residual-factor-identity.md`.
Review:
`review-a2-case2-post-pivot-compatible-residual-factor-identity.md`.

Xhigh source and Lean/API scouts audited the tempting next claim that Aoyagi's
displayed post-pivot two-edge product supplies the selected-entry
`CenterCoord.chartMap` matrix identity.  The result is negative.

Aoyagi pp. 19-21 prove the finite Case 2 product algebra:

```text
D''' = blockdiag(1,D_(J+1)),
C' = Q^-1 C,
lower(D''' C') = D_(J+1) * C'_+.
```

Entrywise, after writing the normalized pivot block as `[1 y; x Z]`, the
post-pivot lower product has entries

```text
sum_k (Z_ik - x_i y_k) C_(k,a).
```

The next selected-entry chart is on the next residual block `D_(J+1)`, not on
the product `D_(J+1) * C'_+`.  Therefore the equality of this product with a
successor selected-entry chart-map matrix is not source-backed.  The existing
Lean `..._of_entrywise` bridges remain the correct interface: the successor
entrywise readout must stay supplied until a genuine source-production theorem
constructs it.

## 2026-06-26 A2 selected-entry finite-cover integral assembly

Reproduction:
`reproduction-a2-selected-entry-finite-cover-integral-assembly.md`.
Statement card:
`statement-card-a2-selected-entry-finite-cover-integral-assembly.md`.
Review:
`review-a2-selected-entry-finite-cover-integral-assembly.md`.

Lean now proves:

```text
lintegral_prod_restrict_lt_top_of_subset_iUnion_finite
PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_selectedEntryCenter_signedBox_finiteCover_withDensity_edgeMatrix
PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_selectedEntryCenter_signedBox_finiteCover_withDensity_edgeMatrix_adaptedProductDifferenceSquareSum_lower
```

The generic measure lemma turns a finite base-set cover into finite lower
integrability over the covered set after product with the regular-coordinate
measure.  The selected-entry theorem intersects all fixed-pivot neighborhoods,
uses the already-proved all-pivot selected-entry sector cover
`signedBoxSet Sres subset union_p chartMap p '' signedBoxSet Rres`, and
assembles the per-pivot finite chart-image integrals into a finite integral
over `signedBoxSet Sres` near `0`.  The original-loss theorem instantiates
the same assembly for `lossDLN` through the existing adapted-to-original loss
comparison.

This is finite coordinate-cover and measure bookkeeping only.  It does not
identify `signedBoxSet Sres` with an Aoyagi source-rank stratum, construct an
analytic source chart, prove original source-measure transport, produce
normal crossings, prove pole order, or extract an RLCT.

## 2026-06-26 A2 Schur-core formal Jacobian unit

Reproduction:
`reproduction-a2-schur-core-formal-jacobian-unit.md`.
Statement card:
`statement-card-a2-schur-core-formal-jacobian-unit.md`.
Review:
`review-a2-schur-core-formal-jacobian-unit.md`.

Lean now proves:

```text
SchurCoreTangent
schurCoreFormalJacobian
schurCoreFormalJacobianInverse
schurCoreFormalJacobianEquiv
schurCoreFormalJacobian_det_isUnit
```

This is the fixed-pivot Schur core from Aoyagi Lemma 2 and the repeated
Theorem 3 step:

```text
F2 = -B^{-1} A2,
F3 = -A3 B^{-1},
C4 = A4 - A3 B^{-1} A2.
```

The formal tangent map is packaged as a `LinearEquiv`; the determinant-unit
theorem is restricted to finite side indices `mu` and `nu`, following xhigh
review, so it is not a vacuous infinite-dimensional determinant statement.

This remains formal finite Jacobian arithmetic only.  It is not a
`HasFDerivAt` theorem, not the full p. 13 product-step Jacobian for
`(C1,D,F3_old,A1,A2,A3,A4)`, not source-measure or density transport, not chart
coverage, not normal crossings, not pole order, and not RLCT extraction.

## 2026-06-26 A2 product-step fixed-passive formal Jacobian unit

Reproduction:
`reproduction-a2-product-step-fixed-passive-formal-jacobian-unit.md`.
Statement card:
`statement-card-a2-product-step-fixed-passive-formal-jacobian-unit.md`.
Review:
`review-a2-product-step-fixed-passive-formal-jacobian-unit.md`.

Lean now proves:

```text
ProductStepFixedPassiveRawTangent
ProductStepFixedPassiveChartTangent
productStepFixedPassiveFormalJacobian
productStepFixedPassiveFormalJacobianInverse
productStepFixedPassiveFormalJacobianEquiv
productStepFixedPassiveFormalJacobian_det_isUnit
```

This extends the Schur-core formal Jacobian work by allowing the top block
`C1` and accumulated old `F3` field to vary while keeping `D`, `A1`, and `A3`
fixed.  The formal tangent formulas are the fixed-passive linearisation of

```text
Ctop = C1*A1,
F2   = -(A1^-1*A2),
F3   = F3old - D*A3*(C1*A1)^-1,
C    = A4 - A3*A1^-1*A2.
```

The determinant-unit theorem is finite-dimensional and assumes finite `pi` and
`nu`. It has no `D.det` hypothesis. This remains a formal finite tangent
calculation: no full variable-`D/A1/A3` p. 13 Jacobian, no analytic derivative,
no source-measure or density transport, no normal crossings, no pole order,
and no RLCT.

## 2026-06-26 A2 product-step full formal Jacobian formulas

Reproduction:
`reproduction-a2-product-step-full-formal-jacobian-formulas.md`.
Statement card:
`statement-card-a2-product-step-full-formal-jacobian-formulas.md`.
Review:
`review-a2-product-step-full-formal-jacobian-formulas.md`.

Lean now records the full p. 13 one-step formal tangent formulas for all raw
variables and the pure chart-output coordinate permutation needed before any
determinant theorem:

```text
ProductReductionStepRawTangent
ProductReductionStepChartTangent
productReductionStepFormalJacobianFormula
productReductionStepFormalJacobianInverseFormula
productReductionStepChartTangentRawOrderEquiv
```

The formulas include the missing `dD`, `dA1`, and `dA3` contributions.  The
chart output is ordered `(Ctop,D,A1,A3,F2,F3,C)`, while raw order is
`(C1,D,F3old,A1,A2,A3,A4)`, so determinant unitness for the full map must
first compose with the reorder to `(Ctop,D,F3,A1,F2,A3,C)`.

This is formula-level Lean, not yet the bundled full `LinearMap`,
`LinearEquiv`, or determinant-unit theorem.  No analytic derivative,
source-measure transport, normal crossings, pole order, or RLCT is claimed.

## 2026-06-26 A2 product-step full formal linear maps

Reproduction:
`reproduction-a2-product-step-full-linear-maps.md`.
Statement card:
`statement-card-a2-product-step-full-linear-maps.md`.
Review:
`review-a2-product-step-full-linear-maps.md`.

Lean now bundles the full p. 13 forward and inverse formal tangent formulas as
`LinearMap`s:

```text
productReductionStepFormalJacobian
productReductionStepFormalJacobianInverse
```

and proves the application theorems:

```text
productReductionStepFormalJacobian_apply
productReductionStepFormalJacobianInverse_apply
```

The maps are built from fixed matrix left/right multiplication maps and named
nested-tuple projections. This proves linearity of the full formulas without
expanding a monolithic `map_add`/`map_smul` proof. The full raw/chart
`LinearEquiv`, raw-order endomorphism, and determinant-unit theorem remain
open, and determinants still must not be taken on the native raw-to-chart map.

## 2026-06-26 A2 product-step raw-order fderiv determinant unit

Reproduction:
`reproduction-a2-product-step-raw-order-fderiv-det-unit.md`.
Statement card:
`statement-card-a2-product-step-raw-order-fderiv-det-unit.md`.
Review:
`review-a2-product-step-raw-order-fderiv-det-unit.md`.

Lean now proves:

```text
fderiv_productReductionStepTopologyTupleToChart_rawOrder_det_isUnit
```

This uses the raw-order `HasFDerivAt` theorem to identify the actual `fderiv`
with the continuous-linear version of
`productReductionStepFormalJacobianRawOrder x`, then applies the formal
determinant-unit theorem
`productReductionStepFormalJacobianRawOrder_det_isUnit`.

This closes the ambient determinant-unit bridge for the p. 13 product-step
coordinate map.  It does not prove determinant-chart subtype differentiability,
source-measure pushforward, density transport, change of variables, normal
crossings, pole order, or RLCT.

## 2026-06-26 A2 product-step determinant-chart fderivWithin

Reproduction:
`reproduction-a2-product-step-det-chart-fderivwithin.md`.
Statement card:
`statement-card-a2-product-step-det-chart-fderivwithin.md`.
Review:
`review-a2-product-step-det-chart-fderivwithin.md`.

Lean now proves:

```text
isOpen_productReductionStepRawTopologyTuple_detChart
hasFDerivWithinAt_productReductionStepTopologyTupleToChart_rawOrder_detChart
fderivWithin_productReductionStepTopologyTupleToChart_rawOrder_det_isUnit
```

This closes the ambient open-domain determinant-chart derivative bridge for
the raw-order p. 13 product-step coordinate map. The raw determinant chart is
open because it is the intersection of two determinant-unit preimages, and on
that open set `fderivWithin` agrees with the already-landed ambient `fderiv`.

This is not differentiability on the determinant-chart subtype and does not
prove local injectivity/inverse data for measure change-of-variables, source
measure pushforward, density transport, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 product-step raw-order injectivity on determinant chart

Reproduction:
`reproduction-a2-product-step-raw-order-injon-det-chart.md`.
Statement card:
`statement-card-a2-product-step-raw-order-injon-det-chart.md`.
Review:
`review-a2-product-step-raw-order-injon-det-chart.md`.

Lean now proves:

```text
ProductReductionStepRawCoordinates.topologyTuple_injective
ProductReductionStepChartCoordinates.topologyTuple_injective
productReductionStepRawCoordinatesOfTopologyTuple
productReductionStepTopologyTupleToChart_ofTopologyTuple
injOn_productReductionStepTopologyTupleToChart_rawOrder_detChart
```

The proof packages raw tuples as records, removes the raw-order coordinate
permutation by injectivity of `productReductionStepChartTangentRawOrderEquiv`,
uses tuple injectivity to recover equality of chart records, and then applies
the determinant-chart left inverse `productReductionStepCoordinate_left_inverse`.

This supplies the injectivity hypothesis for a future Mathlib Jacobian
change-of-variables adapter. It does not prove the adapter itself, source
measure pushforward, density transport, image equality with the full target
determinant chart, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 product-step weighted Haar change of variables

Reproduction:
`reproduction-a2-product-step-weighted-haar-cov.md`.
Statement card:
`statement-card-a2-product-step-weighted-haar-cov.md`.
Review:
`review-a2-product-step-weighted-haar-cov.md`.

Lean now proves:

```text
ProductReductionStepRawTopologyTuple
productReductionStepRawDetChartSet
isOpen_productReductionStepRawDetChartSet
nullMeasurableSet_productReductionStepRawDetChartSet
productReductionStepTopologyTupleToChartRawOrder
productReductionStepRawOrderJacobianCLM
productReductionStepRawOrderJacobianAbsDet
map_productReductionStepTopologyTupleToChartRawOrder_restrict_detChart_withDensity_abs_det
```

This is the direct Mathlib Jacobian change-of-variables adapter for the raw
p. 13 determinant chart. For an additive Haar measure `m`, the raw-order map
pushes forward `m` restricted to the determinant chart and weighted by
`|det J(z)|` to `m` restricted to the image of that determinant chart.

The theorem is intentionally generic in the additive Haar measure and keeps
the null-measurability hypothesis explicit. It does not specialize to
`volume`, identify the image with the whole target determinant chart, transport
the original DLN source/prior measure, prove source coverage, construct
normal crossings, compute pole order, or extract an RLCT.

## 2026-06-26 A2 product-step determinant-chart image

Reproduction:
`reproduction-a2-product-step-det-chart-image.md`.
Statement card:
`statement-card-a2-product-step-det-chart-image.md`.
Review:
`review-a2-product-step-det-chart-image.md`.

Lean now proves:

```text
ProductReductionStepRawCoordinates.topologyTuple_mem_rawDetChartSet
productReductionStepRawCoordinatesOfTopologyTuple_of_topologyTuple
productReductionStepChartCoordinatesOfRawOrderTopologyTuple
productReductionStepChartCoordinatesOfRawOrderTopologyTuple_detChart
productReductionStepChartCoordinatesOfRawOrderTopologyTuple_rawOrder
ProductReductionStepChartCoordinates.rawOrderTopologyTuple_mem_rawDetChartSet
mapsTo_productReductionStepTopologyTupleToChartRawOrder_detChart
surjOn_productReductionStepTopologyTupleToChartRawOrder_detChart
bijOn_productReductionStepTopologyTupleToChartRawOrder_detChart
image_productReductionStepTopologyTupleToChartRawOrder_detChart
map_productReductionStepRawOrder_restrict_detChart_withDensity_absDet_eq_restrict_detChart
```

This identifies the image of the raw determinant chart under the raw-order p.
13 product-step map with the raw-shaped target determinant chart. The
strengthened Haar theorem rewrites the previous target `Phi '' S` to `S`
using this image equality.

This is still weighted additive-Haar transport in p. 13 coordinates. It does
not identify the original DLN source/prior measure, remove the Jacobian
density, prove source coverage, construct normal crossings, compute pole
order, or extract an RLCT.

## 2026-06-26 A2 product-step Jacobian density positivity

Reproduction:
`reproduction-a2-product-step-jacobian-density-pos.md`.
Statement card:
`statement-card-a2-product-step-jacobian-density-pos.md`.
Review:
`review-a2-product-step-jacobian-density-pos.md`.

Lean now proves:

```text
productReductionStepRawOrderJacobianCLM_det_isUnit
productReductionStepRawOrderJacobianAbsDet_pos
eventually_productReductionStepRawOrderJacobianAbsDet_pos_nhds
```

The proof transfers the formal raw-order determinant-unit theorem to the
continuous-linear derivative family used by the weighted Haar theorem, then
uses absolute-value positivity. Since the raw determinant chart is open, this
positivity also holds eventually near any determinant-chart point.

This is not a continuity theorem, not an upper-bound theorem, not original
DLN source/prior transport, not source coverage, not normal crossings, not
pole order, and not RLCT.

## 2026-06-26 A2 product-step Jacobian density continuity

Reproduction:
`reproduction-a2-product-step-jacobian-density-continuity.md`.
Statement card:
`statement-card-a2-product-step-jacobian-density-continuity.md`.
Review:
`review-a2-product-step-jacobian-density-continuity.md`.

Lean now proves:

```text
continuousAt_productReductionStepRawOrderJacobianCLM_apply_of_mem_rawDetChartSet
continuousAt_productReductionStepRawOrderJacobianCLM_of_mem_rawDetChartSet
continuousAt_productReductionStepRawOrderJacobianAbsDet_of_mem_rawDetChartSet
exists_pos_eventually_le_productReductionStepRawOrderJacobianAbsDet_nhds
exists_pos_eventually_productReductionStepRawOrderJacobianAbsDet_le_nhds
```

The proof expands the formal p. 13 derivative formula at a fixed tangent
vector, uses local continuity of `A1^{-1}` and `(C1 A1)^{-1}` at
determinant-chart points, then reconstructs continuity of the
continuous-linear-map valued derivative family using finite basis matrix
coordinates.  Determinant and absolute-value continuity give continuity of
the source-side forward density.  Positivity at the base point gives a
positive local lower bound; continuity gives a positive local upper bound.

This is source-side forward-density unit control.  It is not chart-side
inverse-density transport, original DLN source/prior transport, source
coverage, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 product-step inverse Jacobian density

Reproduction:
`reproduction-a2-product-step-inverse-jacobian-density.md`.
Statement card:
`statement-card-a2-product-step-inverse-jacobian-density.md`.
Review:
`review-a2-product-step-inverse-jacobian-density.md`.

Lean now proves:

```text
continuousAt_productReductionStepChartRawOrderToRawTopologyTuple_of_mem_rawDetChartSet
productReductionStepRawOrderInverseJacobianDensity
productReductionStepRawOrderInverseJacobianDensity_pos
continuousAt_productReductionStepRawOrderInverseJacobianDensity_of_mem_rawDetChartSet
exists_pos_eventually_le_productReductionStepRawOrderInverseJacobianDensity_nhds
exists_pos_eventually_productReductionStepRawOrderInverseJacobianDensity_le_nhds
```

The proof packages the raw-shaped target inverse map
`(Ctop,D,F3,A1,F2,A3,C) -> (Ctop A1^{-1},D,F3+D A3 Ctop^{-1},A1,-A1 F2,A3,C-A3 F2)`,
shows it is continuous at target determinant-chart points, and composes it
with the already-proved source-side forward density continuity.  The chart-side
density is the reciprocal `|det D Phi(Phi^{-1}(y))|^{-1}`, so real inverse
continuity is justified by source-side positivity at the raw preimage.

This is local chart-side reciprocal-density unit control.  It is not an
unweighted source-measure pushforward theorem, not original DLN source/prior
transport, not source coverage, not normal crossings, not pole order, and not
RLCT.

## 2026-06-26 A2 p.13 regular-coordinate inverse density handoff

Reproduction:
`reproduction-a2-product-step-regular-coordinate-inverse-density.md`.
Statement card:
`statement-card-a2-product-step-regular-coordinate-inverse-density.md`.
Review:
`review-a2-product-step-regular-coordinate-inverse-density.md`.

Lean now defines the left-endpoint raw-shaped target tuple for the explicit
p. 13 multi-edge regular-coordinate family:

```text
(Ctop(u), Dtail(x), F3(u), Ctop(u), F2(u), 0, C0(x)).
```

Lean proves determinant-chart membership at the centered regular coordinate,
continuity of this tuple at self-base points, and continuity/positivity of the
chart-side inverse product-step Jacobian density after composition.

The critical calculation is that the passive `A1` slot is `Ctop(u)`, not the
identity.  The identity is the pre-left-step accumulator `C1`.  The determinant
chart therefore checks two copies of `IsUnit det(Ctop(u))`, discharged at
`u = 0` by `Ctop(0) = I`.

This is only a local tuple and reciprocal-density handoff.  It is not source
coverage, original DLN source/prior transport, unweighted measure transport,
normal crossings, pole order, or RLCT.

## 2026-06-26 A2 p.13 product-step inverse-density finite-integral handoff

Reproduction:
`reproduction-a2-product-step-inverse-density-finite-integral-handoff.md`.
Statement card:
`statement-card-a2-product-step-inverse-density-finite-integral-handoff.md`.
Review:
`review-a2-product-step-inverse-density-finite-integral-handoff.md`.

Lean now specializes the existing p.13 local finite-integral handoff from an
abstract positive continuous regular-fiber density to the concrete chart-side
inverse product-step Jacobian density

```text
productReductionStepRawOrderInverseJacobianDensity
  (paperEndpointFixedBaseP13RawOrderTuple V Bv U0 hU0 CedgeBase xu).
```

Lean proves both the direct continuous-density finite-integral wrapper and the
weighted signed-box residual-source wrapper:

```text
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_continuousAt_selfBase
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_selfBase
```

The pen-and-paper check is only the inverse-coordinate readout for the concrete
tuple:

```text
Phi^{-1}(Ctop(u),Dtail(x),F3(u),Ctop(u),F2(u),0,C0(x))
  = (I,Dtail(x),F3(u),Ctop(u),-Ctop(u)F2(u),0,C0(x)).
```

This confirms that no `Dtail` inverse is introduced and that the local unit
input remains the two `Ctop(u)` determinant checks.  The theorem is a
finite-integral consumer only: it does not prove the p.13 product chart image,
source coverage, product-step pushforward identity, original DLN source/prior
transport, signed-box density identification, normal crossings, pole order, or
RLCT.

## 2026-06-26 A2 suffix-step raw-order inverse density handoff

Reproduction:
`reproduction-a2-suffix-step-raw-order-inverse-density.md`.
Statement card:
`statement-card-a2-suffix-step-raw-order-inverse-density.md`.
Review:
`review-a2-suffix-step-raw-order-inverse-density.md`.

Lean now defines the arbitrary suffix-step target tuple

```text
chartLocalSuffixStateStepRawOrderTargetTuple E p S F3prev
```

as the raw-order product-step chart image of
`ChartLocalSuffixState.stepRawCoordinates E p S F3prev`.  It proves:

```text
continuousAt_productReductionStepTopologyTupleToChartRawOrder_of_mem_rawDetChartSet
chartLocalSuffixStateStepRawOrderTargetTuple_mem_rawDetChartSet
continuousAt_chartLocalSuffixState_stepRawCoordinates_topologyTuple
continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple
continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple_inverseJacobianDensity
chartLocalSuffixStateStepRawOrderTargetTuple_inverseJacobianDensity_pos
```

with direct/raw-continuity variants also available.

The pen-and-paper calculation is

```text
x = (S.Ctop,S.D,F3prev,A1,A2,A3,A4)
Y = (S.Ctop*A1, S.D,
     F3prev - S.D*A3*(S.Ctop*A1)^(-1),
     A1, -A1^(-1)*A2, A3, A4 - A3*A1^(-1)*A2).
```

The formulas invert `A1` and `S.Ctop*A1`; the residual/passive block `S.D` is
not assumed invertible.  This is generic local product-step chart/density
infrastructure only; it is not source coverage, source/prior transport,
product-step pushforward, signed-box density identification, normal crossings,
pole order, or RLCT.

## 2026-06-26 A2 raw-order inverse-density pushforward

Reproduction:
`reproduction-a2-product-step-raw-order-inverse-density-pushforward.md`.
Statement card:
`statement-card-a2-product-step-raw-order-inverse-density-pushforward.md`.
Review:
`review-a2-product-step-raw-order-inverse-density-pushforward.md`.

Lean now proves the raw determinant-chart unweighted pushforward orientation:

```text
map Phi (m.restrict s)
  = (m.restrict s).withDensity
      (fun y => ofReal (productReductionStepRawOrderInverseJacobianDensity y)).
```

Here `Phi` is `productReductionStepTopologyTupleToChartRawOrder`, `s` is
`productReductionStepRawDetChartSet`, and `m` is an additive Haar measure on
the raw tuple space.  The proof uses the already-landed weighted COV theorem

```text
map Phi ((m.restrict s).withDensity (ofReal J)) = m.restrict s
```

together with the new pointwise cancellation

```text
ofReal (J z) *
  ofReal (productReductionStepRawOrderInverseJacobianDensity (Phi z)) = 1
```

on the determinant chart.  A private local measure lemma transports the second
density through the pushforward; no inverse derivative theorem is introduced.

New Lean names:

```text
productReductionStepRawOrderInverseJacobianDensity_apply_chartMap
productReductionStepRawOrderJacobianAbsDet_mul_inverseJacobianDensity_apply_chartMap
map_productReductionStepRawOrder_restrict_detChart_eq_withDensity_inverseJacobian
```

This is the first genuine raw product-chart density-transport theorem after
the suffix-density handoff.  It is still not original DLN source/prior
transport, source coverage, p.13 source-chart construction, signed-box density
identification, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 p.13 raw product-step preimage

Reproduction:
`reproduction-a2-p13-raw-product-step-preimage.md`.
Statement card:
`statement-card-a2-p13-raw-product-step-preimage.md`.
Review:
`review-a2-p13-raw-product-step-preimage.md`.

Lean now defines the explicit raw source tuple

```text
X(x,u) = (I, Dtail(x), F3(u), Ctop(u), -Ctop(u)*F2(u), 0, C0(x))
```

whose raw-order product-step image is the existing p.13 raw-shaped target
tuple

```text
Y(x,u) = (Ctop(u), Dtail(x), F3(u), Ctop(u), F2(u), 0, C0(x)).
```

New Lean names:

```text
paperEndpointFixedBaseP13RawPreimageTuple
paperEndpointFixedBaseP13RawPreimageTuple_mem_rawDetChartSet
paperEndpointFixedBaseP13RawPreimageTuple_mem_rawDetChartSet_center
productReductionStepTopologyTupleToChartRawOrder_paperEndpointFixedBaseP13RawPreimageTuple
```

The determinant-chart hypothesis is only `IsUnit det(Ctop(u))`; the centered
case uses `Ctop(0) = I`.  The calculation inverts `Ctop` only.  It does not
invert `Dtail`, prove source coverage, construct the p.13 source chart from
original DLN coordinates, transport the original source/prior measure, identify
signed-box density, prove product-measure pushforward, produce normal
crossings, compute pole order, or extract RLCT.

## 2026-06-26 A2 p.13 product-coordinate left-step raw preimage

Reproduction:
`reproduction-a2-p13-product-coordinate-left-step-raw-preimage.md`.
Statement card:
`statement-card-a2-p13-product-coordinate-left-step-raw-preimage.md`.
Review:
`review-a2-p13-product-coordinate-left-step-raw-preimage.md`.

Lean now connects the explicit p.13 raw preimage tuple to the actual
constructed multi-edge product-coordinate matrix family.  It defines

```text
paperEndpointFixedBaseP13ProductCoordinateMatrixFamily
```

and proves:

```text
p13ProductCoordinateLeftStepRawTopologyTuple_eq_rawPreimageTuple
p13ProductCoordinateLeftStepRawOrderTargetTuple_eq_rawOrderTuple
```

The first theorem identifies the left-endpoint
`ChartLocalSuffixState.stepRawCoordinates` topology tuple with

```text
(I,Dtail,F3,Ctop,-Ctop*F2,0,C0).
```

The proof uses the existing product-coordinate tail-state fields
`S.B = 0`, `S.Ctop = I`, `S.L = [I,0;F3,I]`, transfers the tail residual
product back to the fixed-base family, and reads the left endpoint edge as
`[Ctop,-Ctop*F2;0,C0]`.  The second theorem applies the already-proved raw
product-step preimage theorem to obtain the target tuple
`(Ctop,Dtail,F3,Ctop,F2,0,C0)` under `IsUnit det(Ctop)`.

Xhigh review passed after renaming the matrix constructor away from
`EdgeFamily` wording and updating stale pre-implementation wording in the
reproduction note.

This is still pointwise finite product-coordinate algebra.  It does not prove
source coverage, original DLN source/prior transport, signed-box density
identification, product-measure pushforward, regular-suspension certification,
normal crossings, pole order, or RLCT.

## 2026-06-26 A2 p.13 left-step conditional raw pushforward consumer

Reproduction:
`reproduction-a2-p13-left-step-conditional-raw-pushforward-consumer.md`.
Statement card:
`statement-card-a2-p13-left-step-conditional-raw-pushforward-consumer.md`.
Review:
`review-a2-p13-left-step-conditional-raw-pushforward-consumer.md`.

Lean now consumes the raw-order inverse-density pushforward theorem at the p.13
left endpoint, while keeping the source/product-chart pushforward as an
explicit hypothesis.

New Lean names:

```text
aemeasurable_productReductionStepTopologyTupleToChartRawOrder_restrict_detChart
ae_mem_productReductionStepRawDetChartSet_of_map_eq_restrict
map_productReductionStepRawOrder_comp_eq_withDensity_inverseJacobian
paperEndpointFixedBaseP13RawPreimageTuple_C1_eq_one
paperEndpointFixedBaseP13RawPreimageTuple_A3_eq_zero
p13ProductCoordinateLeftStepRawTopologyTuple
p13ProductCoordinateLeftStepRawTopologyTuple_C1_eq_one
p13ProductCoordinateLeftStepRawTopologyTuple_A3_eq_zero
ae_isUnit_ctopMatrix_det_of_p13RawPreimage_map_eq_restrict_rawDetChart
ae_isUnit_ctopMatrix_det_of_p13LeftStepRaw_map_eq_restrict_rawDetChart
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_rawPreimage_map
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map
```

The generic theorem says that if a raw source tuple `pre` pushes a measure
`eta` to additive Haar measure restricted to the raw determinant chart, then
the raw-order chart map pushes `eta` to the inverse-Jacobian weighted raw
target measure.  The raw chart null-measurability and raw-order map
a.e.-measurability are derived internally from the open determinant chart and
continuity of the raw-order map on that chart.  Lean also derives raw-chart
support from the supplied raw pushforward; for the p.13 raw preimage this gives
`IsUnit det(Ctop)` a.e. from the second raw determinant-chart condition.  The
p.13 raw-preimage theorem applies this to
`(I,Dtail,F3,Ctop,-Ctop*F2,0,C0)` and identifies the target tuple
`(Ctop,Dtail,F3,Ctop,F2,0,C0)` a.e. without a separate `det(Ctop)` a.e.
hypothesis.  The public left-step theorem uses the actual constructed
left-endpoint suffix-step raw tuple and transports the supplied raw
pushforward through
`p13ProductCoordinateLeftStepRawTopologyTuple_eq_rawPreimageTuple`.

Follow-up xhigh scout checks, recorded in
`review-a2-p13-left-step-raw-section-guardrail.md` and
`review-a2-p13-left-step-ctop-from-raw-chart-support.md`, found two guardrails.
First, the p.13 raw preimage is a section of the full raw tuple space, fixing
raw `C1 = I` and raw `A3 = 0`; the four section facts above are now formalized
for both the explicit raw preimage tuple and the actual constructed left-step
raw tuple.  Second, the `Ctop` a.e. unit fact is recoverable only after taking
the strong raw pushforward and raw-map a.e. measurability as inputs.
Consequently, p.13 should not be read as providing a full raw determinant-chart
Haar parametrisation; the raw pushforward remains an explicit hypothesis and
is not a source-backed theorem at this stage.

Xhigh review passed with no findings.  The reviewer confirmed that the density
is on the raw target measure
`(m.restrict rawDetChart).withDensity ...`, not pulled back to the
source/product-coordinate domain.

This is a conditional measure consumer only.  It does not prove the supplied
raw pushforward, source coverage, original DLN source/prior transport,
signed-box density identification, product-measure pushforward,
regular-suspension certification, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 p.13 left-step raw tuple measurability

Reproduction:
`reproduction-a2-p13-left-step-raw-tuple-measurability.md`.
Statement card:
`statement-card-a2-p13-left-step-raw-tuple-measurability.md`.
Review:
`review-a2-p13-left-step-raw-tuple-measurability.md`.

Lean now derives the a.e.-measurability input for the actual constructed p.13
left-step raw tuple from fixed-base edge-matrix measurability.  New suffix
recursion projections:

```text
measurable_chartLocalSuffixState_residualProduct_real
measurable_chartLocalSuffixState_residualBlock_real
```

New p.13 tuple measurability names:

```text
measurable_paperEndpointFixedBaseP13RawPreimageTuple_of_measurable_edgeMatrix
aemeasurable_paperEndpointFixedBaseP13RawPreimageTuple_of_measurable_edgeMatrix
measurable_p13ProductCoordinateLeftStepRawTopologyTuple_of_measurable_edgeMatrix
aemeasurable_p13ProductCoordinateLeftStepRawTopologyTuple_of_measurable_edgeMatrix
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map_of_measurable_edgeMatrix
```

The last theorem is still conditional on the raw source pushforward
`Measure.map p13ProductCoordinateLeftStepRawTopologyTuple eta =
m.restrict rawDetChart`; it only derives the raw tuple a.e.-measurability
premise before calling the earlier conditional consumer.  Xhigh review passed
with no blocking findings.  This does not prove the supplied raw pushforward,
source coverage, original DLN source/prior transport, signed-box density
identification, product-measure pushforward, regular-suspension certification,
normal crossings, pole order, or RLCT.

## 2026-06-26 A2 p.13 left-step section-image measure

Reproduction:
`reproduction-a2-p13-left-step-section-image-measure.md`.
Statement card:
`statement-card-a2-p13-left-step-section-image-measure.md`.
Review:
`review-a2-p13-left-step-section-image-measure.md`.

Source and pen-and-paper xhigh scouts rechecked the raw-Haar boundary:
Aoyagi p.13 does not state a full raw determinant-chart pushforward, and the
p.13 raw tuple is a section fixing raw `C1 = I` and raw `A3 = 0`.  Lean now
records the honest section-level measure identity:

```text
map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_measurable_edgeMatrix
```

If the actual left-step raw tuple lies in the raw determinant chart a.e., then
the p.13 raw-order target measure is the raw-order product-step image of the
actual left-step raw image measure:

```text
Measure.map Y eta = Measure.map Phi (Measure.map X eta).
```

This proves only functoriality plus the pointwise p.13 section algebra under
raw-chart support.  It does not identify `Measure.map X eta` with full raw
Haar, does not add a density conclusion, and does not prove source coverage,
source/prior transport, signed-box density identification, product-measure
pushforward, regular-suspension certification, normal crossings, pole order,
or RLCT.  Xhigh landed-slice review passed with no blocking findings.

## 2026-06-26 A2 p.13 left-step local raw-det support

Reproduction:
`reproduction-a2-p13-left-step-local-raw-det-support.md`.
Statement card:
`statement-card-a2-p13-left-step-local-raw-det-support.md`.
Review:
`review-a2-p13-left-step-local-raw-det-support.md`.

Lean now proves local raw determinant-chart support for the actual p.13
left-step raw tuple:

```text
p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet
exists_pos_radius_le_forall_p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet
ae_p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet_of_ae_regular_mem_ball
exists_pos_radius_le_ae_p13LeftStepRaw_mem_rawDetChartSet_of_ae_regular_mem_ball
```

The pointwise theorem rewrites the actual left-step tuple to the explicit raw
preimage tuple `(I,Dtail,F3,Ctop,-Ctop*F2,0,C0)` and uses the existing
membership theorem when `det Ctop(u)` is a unit.  The small-ball theorem uses
continuity of `det Ctop(u)` at `u=0` to choose `0 < R <= Rmax`; the a.e.
theorems turn support in that regular-coordinate ball into the raw-chart
support hypothesis needed by the section-image measure identity.

This is local support for a section.  It does not prove a raw-Haar/full-chart
pushforward, source coverage, original source/prior transport, signed-box
density identification, product-measure pushforward, regular-suspension
certification, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 p.13 left-step small-ball section image

Reproduction:
`reproduction-a2-p13-left-step-small-ball-section-image.md`.
Statement card:
`statement-card-a2-p13-left-step-small-ball-section-image.md`.
Review:
`review-a2-p13-left-step-small-ball-section-image.md`.

Lean now proves:

```text
exists_pos_radius_le_map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_ae_regular_mem_ball
```

For every `Rmax > 0`, it chooses `0 < R <= Rmax`.  Under fixed-base
edge-matrix measurability, if the local `(x,u)` measure is supported a.e. on
the regular-coordinate ball `u in ball(0,R)`, then the existing section-image
identity applies:

```text
Measure.map Y eta = Measure.map Phi (Measure.map X eta).
```

The proof first uses
`exists_pos_radius_le_ae_p13LeftStepRaw_mem_rawDetChartSet_of_ae_regular_mem_ball`
to obtain raw determinant-chart support, then applies
`map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_measurable_edgeMatrix`.

This remains section-image bookkeeping only.  It does not prove a
raw-Haar/full-chart pushforward, source coverage, original source/prior
transport, density identification, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 p.13 raw pushforward source-boundary audit

Audit:
`source-audit-a2-p13-left-step-raw-pushforward-boundary.md`.

After direct Ghostscript extraction and rendered-page checking of Aoyagi PDF
pp. 5-14, plus independent xhigh source, Lean-boundary, and pen-and-paper
audits, the full raw-Haar pushforward target remains killed as a source-backed
claim:

```text
Measure.map p13ProductCoordinateLeftStepRawTopologyTuple eta =
  m.restrict rawDetChart
```

The source supports the block substitutions in Lemma 2/Theorem 3 and the
displayed p.13 LCT equality, but pp. 5-14 do not state a concrete p.13
source/product-coordinate measure pushforward, Jacobian/density transport,
raw determinant-chart image theorem, or coverage theorem.

The Lean API is already at the right boundary.  The inverse-density theorems
`map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map` and
`..._of_measurable_edgeMatrix` keep the raw pushforward supplied.  The proved
section-image theorem
`map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_measurable_edgeMatrix`
is the honest replacement when only the p.13 raw section is available.

The pen-and-paper obstruction is structural: the p.13 raw section fixes
`C1 = I` and `A3 = 0`, while the raw determinant chart only requires
`det C1` and `det A1` to be units.  For nonzero rank block `rho`, the chart
has open sets with `C1 != I`, so full raw Haar gives positive mass outside
the section image.  The section obstruction disappears only when `rho = 0`,
and even then this does not prove the remaining source-map pushforward.

No Lean theorem was added.  Future inverse-density uses must either keep the
raw pushforward supplied or construct a genuine p.13 source chart, source
coverage, and density/prior transport for the correct source measure.

## 2026-06-26 A2 source-stratum local-subset local-source consumer

Reproduction:
`reproduction-a2-source-stratum-local-subset-local-source-finite-integral-consumer.md`.
Statement card:
`statement-card-a2-source-stratum-local-subset-local-source-finite-integral-consumer.md`.
Review:
`review-a2-source-stratum-local-subset-local-source-finite-integral-consumer.md`.

Lean now proves:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_subset_localSource
```

This theorem consumes an open neighborhood `Ulocal` with
`Ulocal ∩ sourceStratum ⊆ Ulocal ∩ localSource`.  It applies the existing
local-source p.13 finite-integral theorem, shrinks the returned open set by
`Ulocal`, and uses restricted product-measure monotonicity to conclude
finiteness over the shrunk source-rank-stratum set.  The Lean statement carries
`[SFinite μ]` for the product-restriction comparison.

This is a conditional consumer only.  It does not prove the local inclusion,
source coverage, local source/image equality, raw-Haar pushforward,
source-measure transport, density/Jacobian identity, normal crossings, pole
order, or RLCT.

## 2026-06-26 A2 p.13 local source coverage boundary

Audit:
`source-audit-a2-p13-local-source-coverage-boundary.md`.

After the source-stratum local-subset consumer landed, three xhigh
post-recovery scouts rechecked whether Aoyagi pp. 10-13 or the current Lean
API support the missing p.13 local source coverage/inverse theorem.  The
answer remains negative.  The source gives the Lemma 2 block elimination, the
Theorem 3 product normal form, and the p.13 product-difference display; it
does not state a source-image equality, finite determinant-chart cover, local
inverse with passive variables, p.13 source-measure pushforward, or
density/Jacobian transport.

The Lean boundary is aligned with the source: forward p.13 product-coordinate
source-rank membership is proved, but reverse coverage/source-stratum equality
is still an explicit hypothesis in downstream handoffs.  Future work should
not add more wrappers around the local-subset consumer.  The source-moving
alternatives are a genuine p.13 source chart with passive variables and
transport, a smaller reverse rank/readback theorem, or a different
source-backed finite algebra slice.

## 2026-06-26 A2 product-coordinate residual-rank readback

Reproduction:
`reproduction-a2-product-coordinate-residual-rank-readback.md`.
Statement card:
`statement-card-a2-product-coordinate-residual-rank-readback.md`.
Review:
`review-a2-product-coordinate-residual-rank-readback.md`.

Lean now proves the smaller reverse rank/readback theorem recommended by the
source-coverage boundary audit:

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_residualBlock_rank_of_mem_sourceRankStratum
```

If the constructed p.13 multi-edge product-coordinate family is already in
the source-rank stratum at `(x,u)` and `det Ctop(u)` is a unit, then each base
Schur residual block has rank `rEdge p - r`.  This is pointwise finite rank
bookkeeping only.  It assumes constructed-family source-rank membership and
does not prove source coverage, local inverse, exact-rank openness,
source/image equality, source-measure transport, density/Jacobian identity,
normal crossings, pole order, or RLCT.

## 2026-06-26 A2 p.13 passive-variable local source chart boundary

Reproduction:
`reproduction-a2-p13-passive-variable-local-source-chart-boundary.md`.
Review:
`review-a2-p13-passive-variable-local-source-chart-boundary.md`.

After xhigh source and Lean/API scouts rechecked the p.13 measure frontier,
the passive-variable repair route has been pinned as a boundary, not a Lean
theorem.  The audit separates three objects:

```text
full one-step raw determinant chart,
p.13 reduced section C1=I, A3=0, A1=Ctop,
hypothetical retained-passive multi-step source chart.
```

The full one-step raw chart is already formalised with inverse formulas,
derivative determinant unit, and additive-Haar density transport.  The p.13
reduced section is source-faithful to the displayed reduced variables but is
lower-dimensional in the full raw chart in positive rank, so it cannot supply
full raw-Haar pushforward.  A retained-passive multi-step chart remains a
plausible future route, but it is a different object and would need an
explicit source map, local source/source-rank coverage, product-measure
decomposition, and density/Jacobian accounting.  Aoyagi pp. 10-13 do not state
those fields.

Nonclaims: no local source chart, no local inverse, no source-rank coverage,
no source-measure pushforward, no density/Jacobian identity, no signed-box
residual chart, no normal crossings, no pole order, and no RLCT.

## 2026-06-26 A2 product-step A1 formal inverse

Reproduction:
`reproduction-a2-product-step-a1-formal-inverse.md`.
Statement card:
`statement-card-a2-product-step-a1-formal-inverse.md`.
Review:
`review-a2-product-step-a1-formal-inverse.md`.

Lean now proves:

```text
productReductionStepCoordinate_left_inverse_of_isUnit_A1
productReductionStepCoordinate_right_inverse_of_isUnit_A1
```

These extract the record-level inverse cancellation from the existing
determinant-chart inverse theorems.  Both formal inverse laws require only the
retained `A1` block to have determinant a unit; the older
`productReductionStepCoordinate_left_inverse` and
`productReductionStepCoordinate_right_inverse` names remain as determinant
chart wrappers for the analytic chart/domain API.

This is finite p. 13 coordinate algebra only.  It does not weaken the
determinant-chart hypotheses for derivative or measure transport, construct a
local source chart or local inverse for original DLN parameters, prove
source-rank coverage, push forward source measure, identify a density/Jacobian,
produce normal crossings, or compute pole order or RLCT.

## 2026-06-26 A2 retained-passive source-chart construction plan

Construction plan:
`construction-plan-a2-retained-passive-p13-source-chart.md`.

After VM reorientation, the controller and read-only xhigh scout
`Banach the 3rd` rechecked the retained-passive p.13 frontier.  Verdict: no
smaller source-faithful theorem exists below a genuine retained-passive chart
construction.  The named eliminable fields remain:

```text
hraw_map
hcoverage
```

in the raw-density and local-source consumers.  The current reduced p.13
section cannot remove them because it fixes raw `C1 = I` and raw `A3 = 0`,
while the raw determinant chart permits those coordinates to vary.

Future A2 work should start from the construction plan: define the
retained-passive coordinate domain, source map, local inverse, source-rank
coverage/image theorem, measure pushforward, and density/Jacobian accounting.
The first Lean payoff must remove `hraw_map`, remove `hcoverage`, or introduce
a construction theorem that directly produces one of those fields.  More
section-image wrappers or raw-density consumers with the same supplied fields
are parked.

## 2026-06-26 A2 retained-passive coordinate-domain inverse

Reproduction:
`reproduction-a2-retained-passive-coordinate-domain-inverse.md`.

Read-only xhigh scouts `Harvey the 3rd` and `Bernoulli the 3rd` checked the
next construction prerequisite.  The retained-passive coordinates should use
active p.13 variables

```text
X = Ctop_0 - I,  F2_0,  F3_0,  C_p for every edge p,
```

and passive variables

```text
A1_p and F2_p for p > 0,
A3_p for p < last.
```

The omitted variables are recovered recursively:

```text
A1_0 = Ctop_1^{-1} * Ctop_0,
A3_last = -(F3 + sum_{p<last} D_{p+1} A3_p Ctop_p^{-1}) * Ctop_last,
E_p = [I, F2_{p+1}; 0, I] * [A1_p, -A1_p F2_p; A3_p, C_p - A3_p F2_p],
```

with `F2_N = 0`.  This is the first finite source-map/inverse skeleton that
could later support `hcoverage`.  It does not yet prove coverage, exact-rank
openness, source-measure pushforward, density/Jacobian transport, normal
crossings, pole order, or RLCT.

## 2026-06-26 A2 retained-passive transformed-edge reconstruction

Statement card:
`statement-card-a2-retained-passive-transformed-edge-reconstruction.md`.

Lean now adds `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`.
The bounded theorem is

```text
ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrices_transformedEdge_eq
```

with helper definitions

```text
retainedPassiveTransformedEdge
retainedPassiveFixedBaseEdgeMatrix
```

and suffix-state `B` tracking helpers.  For retained-passive transformed blocks

```text
M_p = [A1_p, -A1_p F2_p; A3_p, C_p - A3_p F2_p]
```

and fixed-base edges

```text
E_p = [I, F2_{p+1}; 0, I] * M_p,
```

Lean proves that the deterministic suffix recursion has
`transformedEdge E p (suffixState E last p.succ) = M_p`, assuming
`F2_last=0` and unit determinants for every `A1_p`.

This is finite transformed-edge reconstruction only.  It does not recover the
active endpoint variables `A1_0` or `A3_last`, prove source-rank coverage,
construct source/image equality, push source measure forward, compute a
Jacobian/prior density, produce normal crossings, prove pole order, or extract
RLCT.

## 2026-06-26 A2 retained-passive Ctop determinant chart

Statement card:
`statement-card-a2-retained-passive-ctop-det-chart.md`.
Review:
`review-a2-retained-passive-ctop-det-chart.md`.

Lean now also tracks the suffix-state top block along the same retained-passive
fixed-base reconstruction.  The new local step theorem is

```text
ChartLocalSuffixState.step_retainedPassiveFixedBaseEdgeMatrix_Ctop
```

and the recursive theorems are

```text
ChartLocalSuffixState.suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix_castSucc
ChartLocalSuffixState.suffixState_Ctop_det_isUnit_retainedPassiveFixedBaseEdgeMatrix
```

The content is finite chart-state bookkeeping:

```text
Ctop_p = Ctop_{p+1} * A1_p,
IsUnit det(Ctop_p) for every recursive suffix state.
```

The determinant-unit result assumes `F2_last=0` and unit determinants for every
`A1_p`; the `F2_last` hypothesis is used through the already-proved recursive
`B=-F2` tracking needed to identify the transformed edge at each step.

This does not yet recover the omitted active endpoint `A1_0`, recover
`A3_last`, construct source-rank coverage or source/image equality, push source
measure forward, identify a Jacobian/prior density, produce normal crossings,
prove pole order, or extract RLCT.

Xhigh reviewer `Mill the 3rd` passed the slice and emphasized the scope caveat:
the determinant-unit theorem is for the reconstructed full fixed-base `A1_p`
family after all `A1_p` are assumed or proved determinant units.  It is not yet
the retained-passive coordinate-domain theorem with active `Ctop_0` and passive
`A1_p` for `p > 0`.

## 2026-06-26 A2 retained-passive A1 readback

Statement card:
`statement-card-a2-retained-passive-a1-readback.md`.
Review:
`review-a2-retained-passive-a1-readback.md`.

Lean now proves the constructor-side adjacent-Ctop readback theorem:

```text
ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrix_A1_eq_suffixState_Ctop_inv_mul_Ctop
```

For the same retained-passive fixed-base reconstruction from a full
determinant-unit `A1` family, adjacent suffix-state top blocks recover the
supplied factor:

```text
A1_p = Ctop_{p+1}^-1 * Ctop_p.
```

The proof uses the Ctop recurrence and determinant-unit propagation for
`Ctop_{p+1}`.  The noncommutative order is part of the theorem: the inverse is
on the left.

This is not yet the retained-passive coordinate-domain endpoint theorem.  At
`p=0`, `A1_0` is still an input and `hA1` assumes `det(A1_0)` is a unit.  The
future endpoint theorem must construct `A1_0` from active `Ctop_0=I+X` and
passive `A1_p` for `p>0`.  No `A3_last` recovery, coverage, source/image
theorem, source-measure pushforward, Jacobian/prior density theorem, normal
crossings, pole order, or RLCT is proved.

Verification passed with the local shared Lake directory: focused
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates`, full `DLNFibre`,
`scripts/sorries`, and `git diff --check`.

## 2026-06-26 A2 retained-passive projection-continuity checkpoint

The current latest banked topology rung is the retained-passive projection
continuity layer recorded in
`reproduction-a2-retained-passive-projection-continuity.md`,
`statement-card-a2-retained-passive-projection-continuity.md`, and
`review-a2-retained-passive-projection-continuity.md`.  The next target is
continuity on the determinant-chart subtype for `solvedA1`, `solvedA3`, and
then `edgeMatrix`, not arbitrary-edge source-image reconstruction.

## 2026-06-26 A2 retained-passive projection continuity

Reproduction:
`reproduction-a2-retained-passive-projection-continuity.md`.
Statement card:
`statement-card-a2-retained-passive-projection-continuity.md`.
Review:
`review-a2-retained-passive-projection-continuity.md`.

Lean now records the elementary product-topology continuity facts for the
nonredundant retained-passive coordinate fields:

```text
RetainedPassiveNonredundantCoordinateData.continuous_A1passive
RetainedPassiveNonredundantCoordinateData.continuous_F2
RetainedPassiveNonredundantCoordinateData.continuous_A3passive
RetainedPassiveNonredundantCoordinateData.continuous_C
RetainedPassiveNonredundantCoordinateData.continuous_Ctop
RetainedPassiveNonredundantCoordinateData.continuous_F3
```

It also proves componentwise continuity of the zero-filled embeddings into the
older bundled coordinate data:

```text
RetainedPassiveNonredundantCoordinateData.continuous_A1seed
RetainedPassiveNonredundantCoordinateData.continuous_F2full
RetainedPassiveNonredundantCoordinateData.continuous_A3seed
```

These are setup facts only: projections and constants in the product
topology.  They do not prove continuity of `solvedA1`, `solvedA3`,
`toCoordinateData`, or `edgeMatrix`.  They also do not assert image openness,
source-rank coverage, source/image equality, measure pushforward,
density/Jacobian transport, normal crossings, pole order, or RLCT.

Xhigh reviewer `Parfit the 3rd` passed the Lean statements, typeclass
assumptions, documentation boundary, and focused build.

## 2026-06-26 A2 retained-passive nonredundant coordinate data

Reproduction:
`reproduction-a2-retained-passive-nonredundant-coordinate-data.md`.
Statement card:
`statement-card-a2-retained-passive-nonredundant-coordinate-data.md`.
Review:
`review-a2-retained-passive-nonredundant-coordinate-data.md`.

Lean now defines the dummy-free coordinate object

```text
ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
```

with stored fields `A1passive`, nonterminal `F2`, `A3passive`, `C`, `Ctop`,
and `F3`.  It embeds this object into the older
`RetainedPassiveCoordinateData` by filling the ignored endpoint seeds and the
terminal `F2` slot canonically:

```text
A1seed_0 = 0,
A3seed_last = 0,
F2_last = 0.
```

The new layer proves

```text
ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.edgeMatrix_readbacks_eq_targets
ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.edgeMatrix_ext
```

Under passive `A1passive` determinant-unit hypotheses and `det(Ctop)` unit,
the edge family reads back every stored nonredundant coordinate.  Equality of
edge families for two such data objects forces full equality of the
nonredundant records.  This full extensionality is valid precisely because the
dummy `A1seed 0`, dummy `A3seed last`, and constrained terminal `F2` field have
been removed.

This is still finite coordinate algebra only.  It does not construct an open
coordinate domain, topology, determinant-unit neighborhood, source-rank
coverage, source/image theorem, measure pushforward, density/Jacobian
transport, normal crossings, pole order, or RLCT.

Xhigh reviewer `Locke the 3rd` passed the field boundary, `M=0` behavior,
dummy-slot embedding, passive-unit side-condition translation, readback scope,
full nonredundant extensionality, and nonclaim boundary.  The reviewer also
reran the focused `RetainedPassiveCoordinates` build successfully.

## 2026-06-26 A2 retained-passive determinant-chart domain

Reproduction:
`reproduction-a2-retained-passive-det-chart-domain.md`.
Statement card:
`statement-card-a2-retained-passive-det-chart-domain.md`.
Review:
`review-a2-retained-passive-det-chart-domain.md`.

Lean now names the determinant-domain predicate for the nonredundant
retained-passive coordinate object:

```text
ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.detChart
ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.detChartSet
```

The predicate is `det(Ctop)` unit plus determinant-unit passive `A1passive`
blocks.  The finite readback and extensionality theorems now have
domain-scoped wrappers:

```text
edgeMatrix_readbacks_eq_targets_of_detChart
edgeMatrix_ext_of_detChart
injOn_edgeMatrix_detChartSet
```

The new topology module
`RetainedPassiveCoordinatesTopology.lean` gives the record the product
topology on its finite matrix fields and proves:

```text
isOpen_detChartSet
detChartSet_mem_nhds
```

This is a coordinate-domain topology statement only.  It does not prove image
openness, continuity of `edgeMatrix`, source-rank coverage, source/image
equality, measure pushforward, density/Jacobian transport, normal crossings,
pole order, or RLCT.

Xhigh reviewer `Poincare the 3rd` passed the determinant-domain scope, `M=0`
behavior, domain-scoped wrappers, `Set.InjOn` statement, product-topology
field order, openness proof scope, aggregator import, and nonclaim boundary.
The reviewer also reran the focused topology-module build successfully.

## 2026-06-26 A2 retained-passive recoverable readbacks

Reproduction:
`reproduction-a2-retained-passive-recoverable-readbacks.md`.
Statement card:
`statement-card-a2-retained-passive-recoverable-readbacks.md`.
Review:
`review-a2-retained-passive-recoverable-readbacks.md`.

Lean now proves the sharp finite readback and extensionality layer for the
bundled source-map object:

```text
ChartLocalSuffixState.RetainedPassiveCoordinateData.edgeMatrix_recoverableReadbacks_eq_targets
ChartLocalSuffixState.RetainedPassiveCoordinateData.edgeMatrix_recoverable_ext
```

The readback theorem recovers `F2_0`, `Ctop`, and `F3` from the source-left
suffix state and, from transformed edges, recovers `A1seed_p` for `p != 0`,
`F2_{p.castSucc}`, `A3seed_p` for `p != last edge`, and `C_p`.  The
extensionality theorem says equal edge families force equality of those
recoverable fields, with `F2_last` discharged by the side condition
`F2_last=0`.

This is not full injectivity of `RetainedPassiveCoordinateData`: `A1seed 0`
and `A3seed (Fin.last M)` are dummy seed fields and remain outside the
recoverable coordinate set.  It also proves no topology, source-rank coverage,
source/image equality, measure transport, density/Jacobian accounting, normal
crossings, pole order, or RLCT.

## 2026-06-26 A2 retained-passive transformed-edge readbacks

Reproduction:
`reproduction-a2-retained-passive-transformed-edge-readbacks.md`.
Statement card:
`statement-card-a2-retained-passive-transformed-edge-readbacks.md`.
Review:
`review-a2-retained-passive-transformed-edge-readbacks.md`.

Lean now proves the per-edge transformed-block readbacks:

```text
ChartLocalSuffixState.retainedPassiveTransformedEdge_readbacks
ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrices_transformedEdge_readbacks
```

For

```text
M_p = [A1_p, -A1_p F2_p; A3_p, C_p - A3_p F2_p],
```

Lean proves

```text
topLeft(M_p) = A1_p
upperRight(M_p) = -A1_p * F2_p
-A1_p^-1 * upperRight(M_p) = F2_p
lowerLeft(M_p) = A3_p
schurResidualBlock(M_p) = C_p
```

under the determinant-unit hypothesis for `A1_p`.  The fixed-base wrapper
first rewrites the actual deterministic transformed edge to `M_p` by
`retainedPassiveFixedBaseEdgeMatrices_transformedEdge_eq`, then applies the
readback theorem.

This is the per-edge readback ingredient for the eventual retained-passive
two-sided coordinate inverse.  It does not construct the coordinate domain,
prove the bundled inverse, source coverage, source/image equality, measure
pushforward, density/Jacobian transport, normal crossings, pole order, or RLCT.

Xhigh reviewer `Planck the 3rd` passed the sign/order, inverse-cancellation
hypothesis, Schur convention, and fixed-base rewrite scope.  The reviewer
suggested tightening one phrase in the reproduction note from fixed-base
source map to fixed-base edge-family theorem, which is now applied.

## 2026-06-26 A2 retained-passive fixed-base readback package

Reproduction:
`reproduction-a2-retained-passive-fixed-base-readback-package.md`.
Statement card:
`statement-card-a2-retained-passive-fixed-base-readback-package.md`.
Review:
`review-a2-retained-passive-fixed-base-readback-package.md`.

Lean now proves the fixed-base readback package:

```text
ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrix_activeEndpointAndEdgeReadbacks_eq_targets
```

Under the same solved endpoint hypotheses as the active endpoint package, the
source-left suffix state reads back

```text
-S_0.B = F2_0
S_0.Ctop = Ctop
lowerLeft(S_0.L) = F3
```

and each deterministic transformed edge `T_p=transformedEdge(E,p,S_{p+1})`
reads back

```text
topLeft(T_p) = A1_p
upperRight(T_p) = -A1_p * F2_p
-A1_p^-1 * upperRight(T_p) = F2_p
lowerLeft(T_p) = A3_p
schurResidualBlock(T_p) = C_p
```

The proof derives the full determinant-unit `A1` family from passive unit
hypotheses and the solved `A1_0`, then applies the per-edge readback theorem.
This remains finite fixed-base packaging: no coordinate-domain structure,
two-sided local inverse, coverage, source/image equality, measure pushforward,
density/Jacobian transport, normal crossings, pole order, or RLCT.

Xhigh reviewer `Lorentz the 3rd` passed the endpoint signs, per-edge readback
sign/order, solved `A1_0` and `A3_last` dependencies, and nonclaim boundary.
The reviewer suggested parenthesizing the informal inverse-readback formula to
match Lean exactly; this is now applied in the reproduction and card.

## 2026-06-26 A2 retained-passive solved family constructors

Reproduction:
`reproduction-a2-retained-passive-solved-family-constructors.md`.
Statement card:
`statement-card-a2-retained-passive-solved-family-constructors.md`.
Review:
`review-a2-retained-passive-solved-family-constructors.md`.

Lean now defines the solved retained-passive endpoint families:

```text
ChartLocalSuffixState.retainedPassiveSolvedA1
ChartLocalSuffixState.retainedPassiveSolvedA3
```

The solved `A1` family keeps the passive seed values for `p != 0` and sets
`A1_0=Tail(A1seed)^-1*Ctop`; Lean proves the passive tail is unchanged by this
solve:

```text
ChartLocalSuffixState.retainedPassiveA1TailAfterFirst_solvedA1
ChartLocalSuffixState.retainedPassiveSolvedA1_zero_eq_tail_inv_mul
ChartLocalSuffixState.retainedPassiveSolvedA1_passive_det_isUnit
```

The solved `A3` family keeps passive seed values for `p != last` and sets
`A3_last=-(F3-EarlyTail)*CtopLast`; Lean proves the final-zeroed family is
unchanged:

```text
ChartLocalSuffixState.retainedPassiveA3WithoutLast_solvedA3
ChartLocalSuffixState.retainedPassiveSolvedA3_last_eq_target
```

The wrapper

```text
ChartLocalSuffixState.retainedPassiveSolvedFixedBaseEdgeMatrix_readbacks_eq_targets
```

then applies the fixed-base readback package without taking `A1_0` or
`A3_last` endpoint equations as hypotheses.

This is the first explicit constructor-side source-map layer for the
retained-passive p.13 chart.  It does not define a bundled coordinate domain,
prove a two-sided inverse, coverage, source/image equality, measure
pushforward, density/Jacobian transport, normal crossings, pole order, or RLCT.

Xhigh reviewer `Bohr the 3rd` passed the sign/order, tail-invariance,
passive determinant-unit transport, reuse of the fixed-base readback package,
and nonclaim boundary.  No changes were required.

## 2026-06-26 A2 retained-passive coordinate-data source map

Reproduction:
`reproduction-a2-retained-passive-coordinate-data-source-map.md`.
Statement card:
`statement-card-a2-retained-passive-coordinate-data-source-map.md`.
Review:
`review-a2-retained-passive-coordinate-data-source-map.md`.

Lean now bundles the retained-passive finite coordinate fields into

```text
ChartLocalSuffixState.RetainedPassiveCoordinateData
```

with fields

```text
A1seed, F2, A3seed, C, Ctop, F3.
```

The projections

```text
RetainedPassiveCoordinateData.solvedA1
RetainedPassiveCoordinateData.solvedA3
RetainedPassiveCoordinateData.edgeMatrix
```

build the solved full families and the retained-passive fixed-base edge family.
The theorem

```text
RetainedPassiveCoordinateData.edgeMatrix_readbacks_eq_targets
```

reuses the solved-family wrapper to prove the active source-left and per-edge
transformed-edge readbacks from the bundled data under `F2_last=0`, passive
`A1seed` unit hypotheses, and `det(Ctop)` unit.

This is a finite algebraic source-map object.  It does not define an open
coordinate domain, topology, measure, Jacobian, two-sided local inverse,
coverage, source/image equality, normal crossings, pole order, or RLCT.

Xhigh reviewer `Kant the 3rd` passed the field contents, projection order,
terminal `F2` condition, reuse of the solved-family wrapper, and nonclaim
boundary.  No changes were required.

## 2026-06-26 A2 retained-passive `A1_0` endpoint target

Reproduction:
`reproduction-a2-retained-passive-a1-first-endpoint-target.md`.
Statement card:
`statement-card-a2-retained-passive-a1-first-endpoint-target.md`.
Review:
`review-a2-retained-passive-a1-first-endpoint-target.md`.

Lean now proves the active top-left endpoint half of the retained-passive
coordinate inverse in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`.
Main names:

```text
ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
ChartLocalSuffixState.retainedPassiveA1TailAfterFirst_mul_first
ChartLocalSuffixState.retainedPassiveA1TailAfterFirst_det_isUnit_of_passive
ChartLocalSuffixState.retainedPassiveCtopProduct_zero_eq_target_of_A1_zero_eq
ChartLocalSuffixState.retainedPassiveA1_zero_det_isUnit_of_A1_zero_eq_tail_inv_mul
ChartLocalSuffixState.retainedPassiveA1_det_isUnit_of_A1_zero_eq_tail_inv_mul
ChartLocalSuffixState.suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix_zero_eq_target_of_A1_zero_eq
```

For nonempty edge family length `M+1`, the passive tail after the first edge is
the ordered product `A1_last * ... * A1_1`.  Lean proves the first-edge split

```text
residualFactorProduct A1 last 0 = Tail * A1_0.
```

If `A1_0 = Tail^-1 * Ctop`, the full top-left product is `Ctop`.  Lean also
proves `det(Tail)` is a unit from the passive determinant-unit hypotheses
`det(A1_p)` unit for `p != 0`; together with `det(Ctop)` unit this gives the
full determinant-unit `A1` family and the suffix-state endpoint
`(suffixState E last 0).Ctop = Ctop`.

This is finite top-left endpoint algebra only.  It does not package the full
retained-passive coordinate domain, `F2` readback, `A3_last`/`F3` endpoint
source map, source-rank coverage, source/image equality, measure pushforward,
density/Jacobian transport, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 retained-passive active endpoint package

Reproduction:
`reproduction-a2-retained-passive-active-endpoint-package.md`.
Statement card:
`statement-card-a2-retained-passive-active-endpoint-package.md`.
Review:
`review-a2-retained-passive-active-endpoint-package.md`.

Lean now packages the active source-left endpoint readbacks for the
retained-passive fixed-base source map in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`:

```text
ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrix_activeEndpointFields_eq_targets
```

Under `F2_last=0`, passive `A1_p` determinant-unit hypotheses for `p != 0`,
`det(Ctop)` unit, the solved formula `A1_0=Tail^-1*Ctop`, and the solved
formula `A3_last=-(F3-EarlyTail)*CtopLast`, the theorem proves for the
constructed fixed-base edge family:

```text
-S_0.B = F2_0,
S_0.Ctop = Ctop,
lowerLeft(S_0.L) = F3,
transformedEdge(E,p,S_{p+1}) = retainedPassiveTransformedEdge_p for every p.
```

The theorem derives the required `CtopLast` determinant-unit hypothesis from
the full `A1` unit family, including the solved first block.  This is still
finite endpoint packaging only: no bundled coordinate-domain structure, no
two-sided local inverse, no source-rank coverage, no source/image equality, no
measure pushforward, no density/Jacobian theorem, no normal crossings, no pole
order, and no RLCT.

## 2026-06-26 A2 retained-passive lower-left L recursion

Reproduction:
`reproduction-a2-retained-passive-l-lowerleft-recursion.md`.
Statement card:
`statement-card-a2-retained-passive-l-lowerleft-recursion.md`.
Review:
`review-a2-retained-passive-l-lowerleft-recursion.md`.

Lean now specializes the one-step retained-passive `L` update to the actual
recursive suffix state:

```text
ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_castSucc
ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_castSucc_currentCtop
```

The first theorem proves

```text
lowerLeft(S_p.L)
  = -(S_{p+1}.D * A3_p * (S_{p+1}.Ctop * A1_p)^-1)
      + lowerLeft(S_{p+1}.L).
```

The second rewrites the contribution using the current Ctop block:

```text
lowerLeft(S_p.L)
  = -(S_{p+1}.D * A3_p * S_p.Ctop^-1)
      + lowerLeft(S_{p+1}.L).
```

This is still only one-edge recursive bookkeeping.  It does not prove the
iterated finite-sum formula for `F3_0`, solve `A3_last`, construct the
retained-passive coordinate domain, prove coverage, source/image equality,
measure pushforward, density/Jacobian transport, normal crossings, pole order,
or RLCT.

Xhigh reviewer `Plato the 3rd` passed the sign/order and current-`Ctop` rewrite.
Caveat: Lean's matrix inverse is total, so analytic/chart-regularity uses of
the displayed inverse must still combine this theorem with the existing
determinant-unit theorem for suffix-state `Ctop`.

Verification passed with the local shared Lake directory: focused
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates`, full `DLNFibre`,
`scripts/sorries`, and `git diff --check`.  The full build still emits
pre-existing warnings outside the touched Aoyagi module.

## 2026-06-26 A2 retained-passive lower-left L tail sum

Reproduction:
`reproduction-a2-retained-passive-l-tail-sum.md`.
Statement card:
`statement-card-a2-retained-passive-l-tail-sum.md`.
Review:
`review-a2-retained-passive-l-tail-sum.md`.

Lean now iterates the one-edge lower-left recurrence into a recursive finite
tail sum:

```text
ChartLocalSuffixState.retainedPassiveLowerLeftTailSum
ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_eq_tailSum
ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_zero_eq_tailSum
```

The theorem says

```text
lowerLeft(S_i.L) = Tail_i
Tail_last = 0
Tail_p = -(S_{p+1}.D * A3_p * S_p.Ctop^-1) + Tail_{p+1}.
```

The same Lean slice adds

```text
ChartLocalSuffixState.suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix
```

which identifies `S_i.Ctop` with the ordered product of the supplied `A1`
factors, and then proves the product-tail form:

```text
ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
ChartLocalSuffixState.retainedPassiveLowerLeftTailSum_eq_productTailSum
ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_eq_productTailSum
ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_zero_eq_productTailSum
```

This is now the finite iterated `F3` formula in recursive-tail form.  It still
does not solve `A3_last`, construct the retained-passive coordinate domain,
prove coverage, source/image equality, measure pushforward, density/Jacobian
transport, normal crossings, pole order, or RLCT.

Xhigh reviewer `Pauli the 3rd` passed the indexing, sign/order, terminal zero,
`Ctop` product order, and total-inverse caveat.

## 2026-06-26 A2 retained-passive final-edge endpoint solve

Reproduction:
`reproduction-a2-retained-passive-a3-last-endpoint-solve.md`.
Statement card:
`statement-card-a2-retained-passive-a3-last-endpoint-solve.md`.
Review:
`review-a2-retained-passive-a3-last-endpoint-solve.md`.

Lean now proves the local nonempty-edge endpoint cancellation:

```text
ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_last
ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_last_eq_of_A3_eq_neg_target_mul_Ctop
```

At the final edge the product tail is

```text
Tail_lastEdge = -(I * A3_last * Ctop_last^-1).
```

Under `IsUnit Ctop_last.det`, choosing

```text
A3_last = -G * Ctop_last
```

gives `Tail_lastEdge=G`.

This is the endpoint cancellation needed for the later retained-passive
coordinate inverse.  It does not yet build the full prefix target
`G=F3_0+prefix`, construct the retained-passive coordinate domain, prove
coverage, source/image equality, measure pushforward, density/Jacobian
transport, normal crossings, pole order, or RLCT.

Xhigh reviewer `Einstein the 3rd` passed the final-edge indexing, sign/order,
determinant-unit cancellation, and nonclaim boundary.  The reviewer also ran
the focused `RetainedPassiveCoordinates` build successfully.

## 2026-06-26 A2 retained-passive `A3_last` prefix target

Reproduction:
`reproduction-a2-retained-passive-a3-last-prefix-target.md`.
Statement card:
`statement-card-a2-retained-passive-a3-last-prefix-target.md`.
Review:
`review-a2-retained-passive-a3-last-prefix-target.md`.

Lean now connects the final-edge endpoint solve to the active source target in
recursive-tail form:

```text
ChartLocalSuffixState.retainedPassiveA3WithoutLast
ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_withoutLast_last
ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_eq_withoutLast_add_last
ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_zero_eq_target_of_A3_last_eq
```

The zeroed family `A3WithoutLast` keeps the earlier lower-left blocks and sets
the final block to zero.  Its source tail `EarlyTail` is the signed earlier
contribution, so the paper-facing unsigned prefix is `-EarlyTail`.  Lean proves
that choosing

```text
A3_last = -(F3 - EarlyTail) * Ctop_last
```

under `IsUnit Ctop_last.det` makes the full source product tail equal `F3`.

This is finite tail algebra only.  It does not yet package the full
retained-passive coordinate domain, reconstruct active `Ctop_0`/`A1_0`, prove
determinant-unit neighborhoods, coverage, source/image equality, measure
pushforward, density/Jacobian transport, normal crossings, pole order, or RLCT.

Xhigh reviewer `Tesla the 3rd` passed the sign convention, split indexing,
determinant-unit usage, and nonclaim boundary.  The reviewer also ran the
focused `RetainedPassiveCoordinates` build successfully.

## 2026-06-26 A2 retained-passive D and L recurrences

Reproduction:
`reproduction-a2-retained-passive-d-l-recurrence.md`.
Statement card:
`statement-card-a2-retained-passive-d-l-recurrence.md`.
Review:
`review-a2-retained-passive-d-l-recurrence.md`.

Lean now proves the retained-passive Schur residual and deterministic residual
field recurrences:

```text
ChartLocalSuffixState.schurResidualBlock_retainedPassiveTransformedEdge
ChartLocalSuffixState.step_retainedPassiveFixedBaseEdgeMatrix_D
ChartLocalSuffixState.suffixState_D_retainedPassiveFixedBaseEdgeMatrix_castSucc
ChartLocalSuffixState.suffixState_D_retainedPassiveFixedBaseEdgeMatrix
```

For

```text
M_p = [A1_p, -A1_p F2_p; A3_p, C_p - A3_p F2_p],
```

Lean proves `schurResidualBlock M_p = C_p`, then
`D_p = D_{p+1} * C_p`, and finally
`D_i = residualFactorProduct C last i`.

The same Lean slice also proves the one-step lower-unitriangular update:

```text
ChartLocalSuffixState.step_retainedPassiveFixedBaseEdgeMatrix_L
ChartLocalSuffixState.step_retainedPassiveFixedBaseEdgeMatrix_lowerLeftBlock_L
```

If the next suffix-state left multiplier is `[I,0;F3next,I]`, the new
lower-left block is

```text
-(D_{p+1} * A3_p * (Ctop_{p+1} * A1_p)^-1) + F3next.
```

Together with the already-proved `Ctop_p = Ctop_{p+1} * A1_p`, this is the
one-step algebra behind `F3_p = F3_{p+1} - D_{p+1} A3_p Ctop_p^-1`.

This is not yet the iterated finite-sum formula for `F3_0` and does not solve
for `A3_last`.  It also still assumes a full determinant-unit `A1` family,
including `A1_0`; no retained-passive coordinate-domain theorem, coverage,
source/image theorem, measure pushforward, density/Jacobian theorem, normal
crossings, pole order, or RLCT is proved.

Verification passed with the local shared Lake directory: focused
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates`, full `DLNFibre`,
`scripts/sorries`, and `git diff --check`.

## 2026-06-26 End-of-thread retained-passive topology pointer

The latest retained-passive topology rung banked in this thread is the
projection-continuity layer:
`reproduction-a2-retained-passive-projection-continuity.md`,
`statement-card-a2-retained-passive-projection-continuity.md`, and
`review-a2-retained-passive-projection-continuity.md`.  The next target is
determinant-chart subtype continuity for `solvedA1`, `solvedA3`, and then
`edgeMatrix`.

## 2026-06-26 A2 retained-passive solved-A1 continuity

Reproduction:
`reproduction-a2-retained-passive-solved-a1-continuity.md`.
Statement card:
`statement-card-a2-retained-passive-solved-a1-continuity.md`.
Review:
`review-a2-retained-passive-solved-a1-continuity.md`.

Lean now proves:

```text
RetainedPassiveNonredundantCoordinateData.continuous_retainedPassiveA1TailAfterFirst
RetainedPassiveNonredundantCoordinateData.continuous_solvedA1_detChart_subtype
```

The first theorem proves continuity of the passive top-left tail product by
finite product induction.  The second proves componentwise continuity of the
solved full `A1` family on `{data // data.detChart}`: the zero component uses
the determinant-chart tail unit and matrix-inverse continuity, while nonzero
components reduce to `A1seed`.

This is solved-top-left endpoint continuity only.  It does not prove
continuity of `solvedA3`, `toCoordinateData`, or `edgeMatrix`; no image
openness, source-rank coverage, source/image theorem, measure pushforward,
density/Jacobian theorem, normal crossings, pole order, or RLCT is proved.

Xhigh reviewer `Popper the 3rd` passed the Lean statements, typeclass
assumptions, documentation boundary, focused build, and diff hygiene.

## 2026-06-26 A2 retained-passive solved-A3 continuity

Reproduction:
`reproduction-a2-retained-passive-solved-a3-continuity.md`.
Statement card:
`statement-card-a2-retained-passive-solved-a3-continuity.md`.
Review:
`review-a2-retained-passive-solved-a3-continuity.md`.

Lean now proves the finite support lemmas for lower-left endpoint continuity:

```text
RetainedPassiveNonredundantCoordinateData.continuous_retainedPassiveA3WithoutLast
RetainedPassiveNonredundantCoordinateData.continuous_residualFactorProduct_C
RetainedPassiveNonredundantCoordinateData.solvedA1_det_isUnit_of_detChart
RetainedPassiveNonredundantCoordinateData.continuous_residualFactorProduct_solvedA1_detChart_subtype
RetainedPassiveNonredundantCoordinateData.residualFactorProduct_solvedA1_det_isUnit_of_detChart
RetainedPassiveNonredundantCoordinateData.continuous_retainedPassiveLowerLeftProductTailSum_detChart_subtype
```

It then proves:

```text
RetainedPassiveNonredundantCoordinateData.continuous_solvedA3_detChart_subtype
```

This completes endpoint-family continuity for the nonredundant determinant
chart.  It does not prove continuity of `edgeMatrix`; no image openness,
source-rank coverage, source/image theorem, measure pushforward,
density/Jacobian theorem, normal crossings, pole order, or RLCT is proved.

Xhigh reviewer `Sartre the 3rd` passed the Lean statements, inverse-continuity
usage, typeclass assumptions, documentation boundary, focused build, and diff
hygiene.

## 2026-06-26 A2 retained-passive edge-matrix continuity

Reproduction:
`reproduction-a2-retained-passive-edge-matrix-continuity.md`.
Statement card:
`statement-card-a2-retained-passive-edge-matrix-continuity.md`.
Review:
`review-a2-retained-passive-edge-matrix-continuity.md`.

Lean now proves:

```text
RetainedPassiveNonredundantCoordinateData.continuous_edgeMatrix_detChart_subtype_apply
RetainedPassiveNonredundantCoordinateData.continuous_edgeMatrix_detChart_subtype
```

The per-edge theorem unfolds the retained-passive source edge into the
fixed-base block formula and composes continuity of `solvedA1`, `solvedA3`,
`F2full`, and `C` with block-matrix operations.  The two `F2` roles remain
separate: `p.castSucc` is used inside the transformed edge and `p.succ` in
the left upper-unitriangular fixed-base multiplier.  The family theorem is the
Pi-topology wrapper.

This is source-map continuity on `{data // data.detChart}` only.  It does not
prove image openness, source-rank coverage, source/image theorem, local
homeomorphism, measure pushforward, density/Jacobian theorem, normal
crossings, pole order, or RLCT.

Xhigh reviewer `Galileo the 3rd` passed the Lean statements, formula indices,
final unfolding step, documentation boundary, focused build, and diff hygiene.

## 2026-06-26 A2 retained-passive source-readback object

Reproduction:
`reproduction-a2-retained-passive-source-readback-object.md`.
Statement card:
`statement-card-a2-retained-passive-source-readback-object.md`.
Review:
`review-a2-retained-passive-source-readback-object.md`.

Lean now defines:

```text
RetainedPassiveNonredundantCoordinateData.ext_fields
RetainedPassiveNonredundantCoordinateData.sourceReadbackSuffixState
RetainedPassiveNonredundantCoordinateData.sourceReadbackTransformedEdge
RetainedPassiveNonredundantCoordinateData.sourceReadback
```

and proves:

```text
RetainedPassiveNonredundantCoordinateData.sourceReadback_edgeMatrix_eq
```

The readback object is total on retained-passive-shaped edge families.  Its
fields are read from deterministic suffix states and transformed edges:
`A1passive` from edge `p.succ`, `F2` and `C` from edge `p`, `A3passive` from
edge `p.castSucc`, and active `Ctop/F3` from suffix state `0`.

The theorem proves only that this readback recovers `data` from
`data.edgeMatrix` when `data.detChart`.  It does not prove arbitrary
edge-family image membership, image openness, source-rank coverage,
source/image theorem, local homeomorphism, measure pushforward,
density/Jacobian theorem, normal crossings, pole order, or RLCT.

Xhigh reviewer `Averroes the 3rd` passed the index shifts, theorem scope,
documentation boundary, focused build, and diff hygiene.

## 2026-06-26 A2 retained-passive source-readback continuity

Reproduction:
`reproduction-a2-retained-passive-source-readback-continuity.md`.
Statement card:
`statement-card-a2-retained-passive-source-readback-continuity.md`.
Review:
`review-a2-retained-passive-source-readback-continuity.md`.

Lean now defines:

```text
RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart
```

and proves:

```text
RetainedPassiveNonredundantCoordinateData.continuousAt_sourceReadbackSuffixState_fields
RetainedPassiveNonredundantCoordinateData.continuousAt_sourceReadbackTransformedEdge
RetainedPassiveNonredundantCoordinateData.continuousAt_sourceReadback
RetainedPassiveNonredundantCoordinateData.continuous_sourceReadback_sourceRecursiveDetChart_subtype
```

The predicate requires exactly that every transformed edge visited by the
deterministic suffix-state readback recursion lies in the selected determinant
chart.  Under this basepoint predicate and `ContinuousAt E x0`, the suffix
fields, transformed edges, and all six fields of `sourceReadback (E x)` are
continuous at `x0`.  The subtype theorem is a corollary, not an openness or
image theorem.

This is finite source-readback continuity only.  It does not prove arbitrary
edge-family image membership, image openness, source-rank coverage,
source/image theorem, local homeomorphism, measure pushforward,
density/Jacobian theorem, normal crossings, pole order, or RLCT.

Xhigh reviewer `Beauvoir the 3rd` passed the determinant predicate scope,
index shifts, theorem layering, documentation boundary, and focused build.

## 2026-06-26 A2 retained-passive source-recursive reconstruction spine

Reproduction:
`reproduction-a2-retained-passive-source-recursive-reconstruction-spine.md`.
Statement card:
`statement-card-a2-retained-passive-source-recursive-reconstruction-spine.md`.
Review:
`review-a2-retained-passive-source-recursive-reconstruction-spine.md`.

Lean now proves the first finite algebraic spine for the right-inverse
direction:

```text
DLNFibre.DLN.Aoyagi.fromBlocks_schurReadbacks_eq
RetainedPassiveNonredundantCoordinateData.sourceReadbackSuffixState_Ctop_det_isUnit_of_sourceRecursiveDetChart
RetainedPassiveNonredundantCoordinateData.sourceReadback_detChart_of_sourceRecursiveDetChart
RetainedPassiveNonredundantCoordinateData.sourceReadback_F2full_eq_neg_sourceReadbackSuffixState_B
RetainedPassiveNonredundantCoordinateData.sourceReadbackSuffixState_Ctop_castSucc
RetainedPassiveNonredundantCoordinateData.sourceReadback_A1Tail_eq_sourceReadbackSuffixState_Ctop_of_ne_zero
RetainedPassiveNonredundantCoordinateData.sourceReadback_A1TailAfterFirst_eq_sourceReadbackSuffixState_Ctop_succ_zero
RetainedPassiveNonredundantCoordinateData.sourceReadback_solvedA1_eq_topLeftCorner
```

The generic Schur reassembly lemma was placed in `ProductReduction.lean`.
The source-side determinant predicate now gives retained-passive `detChart`
membership for `sourceReadback E`, the full right field satisfies
`F2full i = -S_i.B`, and the solved full `A1` family matches the selected
top-left block of every visited transformed source edge.

This is not yet the full right inverse.  The next finite target is the
solved-`A3` analogue
`sourceReadback_solvedA3_eq_lowerLeftBlock`; the final edge is the only
substantial case and should use the source-side `F3` lower-left suffix field
and the retained-passive lower-left tail sum.  Do not promote this rung to
image openness, source-rank coverage, source/image equality, local
homeomorphism, measure transport, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 retained-passive source right inverse

Reproduction:
`reproduction-a2-retained-passive-source-right-inverse.md`.
Statement card:
`statement-card-a2-retained-passive-source-right-inverse.md`.
Review:
`review-a2-retained-passive-source-right-inverse.md`.

Lean now proves the finite right-inverse theorem on the recursive determinant
chart:

```text
ChartLocalSuffixState.step_lowerLeftBlock_L_of_L_eq_lowerUnitriangular
ChartLocalSuffixState.step_lowerLeftBlock_L_of_exists_L_eq_lowerUnitriangular
RetainedPassiveNonredundantCoordinateData.retainedPassiveSolvedA3_last_eq_of_productTailSum_eq
RetainedPassiveNonredundantCoordinateData.retainedPassiveSolvedA3_last_eq_of_productTailSum_eq_of_ne_last
RetainedPassiveNonredundantCoordinateData.sourceReadback_solvedA1_residualFactorProduct_eq_Ctop
RetainedPassiveNonredundantCoordinateData.sourceReadbackSuffixState_D_eq_residualFactorProduct_C
RetainedPassiveNonredundantCoordinateData.sourceReadbackSuffixState_lowerLeftBlock_L_eq_lowerLeftProductTailSum
RetainedPassiveNonredundantCoordinateData.sourceReadback_solvedA3_eq_lowerLeftBlock
RetainedPassiveNonredundantCoordinateData.retainedPassiveTransformedEdge_sourceReadback_eq_sourceReadbackTransformedEdge
RetainedPassiveNonredundantCoordinateData.edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart
```

The missing lower-left endpoint is closed by identifying
`lowerLeftBlock S_0.L` with the retained-passive lower-left product-tail sum
for the actual transformed source lower-left blocks.  The final `A3` solver
then cancels the final tail contribution against `CtopLast`.  Schur
reassembly reconstructs every transformed source edge, and the stored
`F2full = -S.B` identity cancels the deterministic upper-unitriangular
multiplier.

This proves image membership only for edge families satisfying
`sourceRecursiveDetChart`: `(sourceReadback E).edgeMatrix = E`.  The next
frontier is topological/geometric packaging around this finite inverse, such
as the exact source-domain/image statement and local-homeomorphism conditions,
but those require explicit openness/image hypotheses.  Do not assert source
rank coverage, measure transport, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 retained-passive source-recursive chart homeomorphism

Reproduction:
`reproduction-a2-retained-passive-source-recursive-chart-homeomorph.md`.
Statement card:
`statement-card-a2-retained-passive-source-recursive-chart-homeomorph.md`.
Review:
`review-a2-retained-passive-source-recursive-chart-homeomorph.md`.

Lean now packages the finite two-sided inverse as a topological equivalence
between explicit chart domains:

```text
RetainedPassiveNonredundantCoordinateData.solvedA1_det_isUnit_of_detChart
RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart_edgeMatrix_of_detChart
RetainedPassiveNonredundantCoordinateData.continuous_edgeMatrix_sourceRecursiveDetChart_subtype
RetainedPassiveNonredundantCoordinateData.continuous_sourceReadback_detChart_subtype
RetainedPassiveNonredundantCoordinateData.detChart_sourceRecursiveDetChart_homeomorph
```

The forward map sends `data : {data // data.detChart}` to
`data.edgeMatrix`, now with proof that it satisfies `sourceRecursiveDetChart`.
The inverse sends `E : {E // sourceRecursiveDetChart E}` to
`sourceReadback E`, now with proof that it satisfies `detChart`.  The inverse
laws are exactly the earlier `sourceReadback_edgeMatrix_eq` and
`edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart` theorems.

This is a homeomorphism of named subtypes only.  It does not prove ambient
openness of `sourceRecursiveDetChart`, equality with the whole source image,
source-rank coverage, measure transport, normal crossings, pole order, or
RLCT.

## 2026-06-26 A2 retained-passive source-recursive chart openness

Reproduction:
`reproduction-a2-retained-passive-source-recursive-chart-openness.md`.
Statement card:
`statement-card-a2-retained-passive-source-recursive-chart-openness.md`.
Review:
`review-a2-retained-passive-source-recursive-chart-openness.md`.

Lean now names the source-recursive determinant chart set and proves it is
open in the ambient edge-family space:

```text
RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChartSet
RetainedPassiveNonredundantCoordinateData.mem_sourceRecursiveDetChartSet
RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart_iff
RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChartSet_mem_nhds
RetainedPassiveNonredundantCoordinateData.isOpen_sourceRecursiveDetChartSet
```

The proof removes the irrelevant proof argument in `sourceRecursiveDetChart`,
uses continuity of each transformed-edge readback at chart points, pulls back
the open selected determinant chart, and intersects the finitely many edge
neighborhoods.

This is ambient openness for the named source-recursive chart only.  It does
not prove equality with the whole source image, source-rank coverage, measure
transport, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 retained-passive open partial homeomorphism

Reproduction:
`reproduction-a2-retained-passive-open-partial-homeomorph.md`.
Statement card:
`statement-card-a2-retained-passive-open-partial-homeomorph.md`.
Review:
`review-a2-retained-passive-open-partial-homeomorph.md`.

Lean now packages the retained-passive determinant coordinate chart and the
explicit source-recursive determinant edge chart as an ambient open partial
homeomorphism:

```text
RetainedPassiveNonredundantCoordinateData.detChartSet_sourceRecursiveDetChartSet_homeomorph
RetainedPassiveNonredundantCoordinateData.detChart_sourceRecursiveDetChart_openPartialHomeomorph
```

The source is `detChartSet`, the target is `sourceRecursiveDetChartSet`, the
forward map is `edgeMatrix`, and the inverse map is `sourceReadback`.  The map
and inverse-law fields are the already banked finite inverse theorems; the
openness fields are `isOpen_detChartSet` and
`isOpen_sourceRecursiveDetChartSet`.  The forward continuity-on-source field
transports `continuous_edgeMatrix_detChart_subtype` across the named-set
membership rewrite, and the inverse continuity-on-target field uses
`continuousAt_sourceReadback` pointwise.

This is a local chart object for the explicit retained-passive chart only.  It
does not prove equality with the whole source image, source-rank coverage,
measure transport, density/Jacobian transport, normal crossings, pole order,
or RLCT.

## 2026-06-26 A2 retained-passive p.13 source-chart coverage boundary

Reproduction:
`reproduction-a2-retained-passive-p13-source-chart-boundary.md`.
Statement card:
`statement-card-a2-retained-passive-p13-source-chart-coverage-boundary.md`.
Review:
`review-a2-retained-passive-p13-source-chart-coverage-boundary.md`.

After VM reorientation, xhigh pen-and-paper scout Franklin the 3rd reproduced
the retained-passive p.13 source-chart calculation, and xhigh Lean/API scout
Socrates the 3rd audited the existing retained-passive chart against the
remaining downstream sockets.

The finite coordinate boundary is:

```text
active:  Ctop_0 - I, F2_0, F3_0, residual blocks C_p
passive: A1_p and F2_p for p > 0, A3_p for p < last
solved:  A1_0 and A3_last
```

The passive variables reconstruct the source edge family but do not enter the
p.13 active readout

```text
[ Ctop - I      -F2
  -F3        D - F3 F2 ].
```

Socrates confirmed that the existing open partial homeomorphism has no honest
downstream consumer by itself.  It does not remove the `hraw_map` measure
pushforward hypothesis in `ProductReductionStepRegularDensity.lean` and does
not remove the `hcoverage` local source-rank inclusion in
`RegularSuspensionLocalMeasure.lean`.

Boyle the 3rd reviewed the reproduction, card, and ledger updates and found no
blocking issue.  The residual risks before Lean are the paper/Lean index
convention for the retained-passive edge family and the need to define any
future Jacobian exponent by the actual `A2/F2` block width.

Next target: a retained-passive local source coverage theorem, not another
wrapper.  The theorem should define a local source tied to the preimage of
`sourceRecursiveDetChartSet` under the fixed-base source edge-family map and
prove a local inclusion from `paperEndpointFixedBaseSourceRankStratum`.
Do not set `localSource` to the source stratum itself.  Keep measure/Jacobian
transport as a separate later theorem family.

## 2026-06-26 A2 retained-passive local-source coverage

Reproduction:
`reproduction-a2-retained-passive-local-source-coverage.md`.
Statement card:
`statement-card-a2-retained-passive-local-source-coverage.md`.
Review:
`review-a2-retained-passive-local-source-coverage.md`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean`.

Lean now defines the chart-tied retained-passive p.13 local source

```text
paperEndpointFixedBaseRetainedPassiveP13LocalSource
```

as the fixed-base edge-matrix preimage of
`RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChartSet`, with
`rho = Fin (Module.finrank K U0)` and
`kappa' = throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U0`.

The Lean index convention is now explicit: the retained-passive parameter `M`
means vertices `Fin (M + 2)` and edges `Fin (M + 1)`.  If the paper notation
has `N` edges, this Lean theorem uses `M = N - 1`.

Main Lean names:

```text
mem_paperEndpointFixedBaseRetainedPassiveP13LocalSource_iff_recursiveDetCharts
paperEndpointFixedBaseRetainedPassiveP13LocalSource_mem_nhds_of_selfBase
exists_open_paperEndpointFixedBaseRetainedPassiveP13LocalSource_coverage_of_selfBase
```

The theorem returns an open `Ulocal` containing the base point with `Ulocal`
contained in the retained-passive local source.  Therefore
`Ulocal ∩ paperEndpointFixedBaseSourceRankStratum` is locally contained in the
same chart-tied source.  Carson the 3rd confirmed that the nontrivial content
is the determinant-chart preimage neighborhood; the source-rank inclusion is
the handoff-shaped consequence of `Ulocal ⊆ localSource`, not source-rank
openness.

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalSource
```

Nonclaims: no exact-rank openness, no global source-rank finite cover, no
source-image equality, no measurability of this local source, no measure
pushforward, no Jacobian/density theorem, no normal crossings, no pole order,
and no RLCT extraction.

## 2026-06-26 A2 retained-passive local-source measurability

Reproduction:
`reproduction-a2-retained-passive-local-source-measurability.md`.
Statement card:
`statement-card-a2-retained-passive-local-source-measurability.md`.
Review:
`review-a2-retained-passive-local-source-measurability.md`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean`.

Lean now proves:

```text
continuous_paperEndpointFixedBaseRetainedPassiveP13EdgeMatrix_of_continuous
measurableSet_paperEndpointFixedBaseRetainedPassiveP13LocalSource_of_continuous
```

The proof is purely topological.  Global continuity of `Cedge` gives global
continuity of the fixed-base edge-matrix map by the existing fixed-base
continuity-at theorem.  The retained-passive local source is the preimage of
the open set `sourceRecursiveDetChartSet`, hence measurable under
`OpensMeasurableSpace`.

This removes the `hlocalSource_meas` obligation for this retained-passive
local source when `Cedge` is globally continuous.  Nonclaims: no source-rank
openness, no residual integrability, no loss/density bounds, no measure
pushforward, no Jacobian/density theorem, no normal crossings, no pole order,
and no RLCT extraction.

## 2026-06-26 A2 retained-passive local-measure handoff

Reproduction:
`reproduction-a2-retained-passive-local-measure-handoff.md`.
Statement card:
`statement-card-a2-retained-passive-local-measure-handoff.md`.
Review:
`review-a2-retained-passive-local-measure-handoff.md`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean`.

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource
```

This specializes the existing source-stratum/local-source finite-integral
consumer to the retained-passive determinant-chart local source.  It supplies
the local coverage and measurability fields from the retained-passive local
source lemmas, under global `Continuous Cedge` and the self-base equality.

It still assumes residual positivity, residual negative-power integrability,
and local loss/density bounds on the retained-passive local source.  Nonclaims:
no source image equality, no measure pushforward, no Jacobian/density theorem,
no residual integrability proof, no original-loss comparison, no normal
crossings, no pole order, and no RLCT extraction.

## 2026-06-26 A2 retained-passive signed-box local-measure handoff

Reproduction:
`reproduction-a2-retained-passive-signed-box-local-measure-handoff.md`.
Statement card:
`statement-card-a2-retained-passive-signed-box-local-measure-handoff.md`.
Review:
`review-a2-retained-passive-signed-box-local-measure-handoff.md`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean`.

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_residualSource_signedBox_withDensity_monomialLower
```

This specializes the weighted signed-box residual-source constructor to the
retained-passive determinant-chart local source.  Global `Continuous Cedge`
gives the measurable fixed-base edge-matrix map; the supplied signed-box
pushforward and monomial residual/density bounds give residual positivity and
negative-power integrability on the retained-passive local source; the prior
retained-passive local-measure handoff gives the finite integral over a local
source-rank-stratum neighborhood.

It still assumes the signed-box chart, weighted pushforward, monomial
residual/density estimates, and local loss/density bounds.  Nonclaims: no
source chart construction, no source image equality, no measure pushforward
proof, no Jacobian/density theorem, no original-loss comparison, no normal
crossings, no pole order, and no RLCT extraction.

## 2026-06-26 A2 retained-passive monomial-unit local-measure handoff

Reproduction:
`reproduction-a2-retained-passive-monomial-unit-local-measure-handoff.md`.
Statement card:
`statement-card-a2-retained-passive-monomial-unit-local-measure-handoff.md`.
Review:
`review-a2-retained-passive-monomial-unit-local-measure-handoff.md`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean`.

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_residualSource_signedBox_withDensity_monomialUnits
```

This specializes the elementary signed-box monomial-unit package to the
retained-passive determinant-chart local source.  Supplied residual/source
density monomial-times-unit identities and unit bounds imply the residual
monomial lower bound and source-density bounds consumed by the retained-
passive signed-box local-measure handoff.

It still assumes the source chart, weighted pushforward, monomial-unit
identities, unit bounds, and local loss/density bounds.  Nonclaims: no source
chart construction, no source image equality, no measure pushforward proof, no
Jacobian/density theorem, no original-loss comparison, no normal crossings, no
pole order, and no RLCT extraction.

## 2026-06-26 A2 retained-passive selected-entry signed-box handoff

Reproduction:
`reproduction-a2-retained-passive-selected-entry-signed-box-handoff.md`.
Statement card:
`statement-card-a2-retained-passive-selected-entry-signed-box-handoff.md`.
Review:
`review-a2-retained-passive-selected-entry-signed-box-handoff.md`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean`.

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity
```

This specializes the retained-passive monomial-unit socket to
`SelectedEntrySignedBox.CenterCoord`, discharging selected-entry density-unit
measurability, monomial identities, and unit bounds from existing finite
calculation lemmas.  It keeps the retained-passive source chart, weighted
pushforward, residual readout, and local loss/density bounds explicit.

Nonclaims: no source chart construction, no source image equality, no measure
pushforward/Jacobian proof, no original-loss comparison, no normal crossings,
no pole order, and no RLCT.

## 2026-06-26 A2 retained-passive source-readback residual readout

Reproduction:
`reproduction-a2-retained-passive-source-readback-residual-readout.md`.
Statement card:
`statement-card-a2-retained-passive-source-readback-residual-readout.md`.
Review:
`review-a2-retained-passive-source-readback-residual-readout.md`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean`.

Lean now proves:

```text
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_sourceReadback_residualFactorProduct
```

This rewrites the fixed-base p.13 residual coordinate map as the scalar-entry
map of the retained-passive source-readback residual-factor product.  It
combines the existing fixed-base residual-product readout with the existing
retained-passive source-readback theorem identifying the same suffix `D` block
with `residualFactorProduct (sourceReadback E).C`.

Nonclaims: no selected-entry source chart is constructed, no entrywise
selected-entry residual-coordinate identification is proved, and no
pushforward/Jacobian, original-loss comparison, normal crossings, pole order,
or RLCT statement is proved.

## 2026-06-26 A2 retained-passive selected-entry source-readback residual-factor handoff

Reproduction:
`reproduction-a2-retained-passive-selected-entry-source-readback-residual-factor-handoff.md`.
Statement card:
`statement-card-a2-retained-passive-selected-entry-source-readback-residual-factor-handoff.md`.
Review:
`review-a2-retained-passive-selected-entry-source-readback-residual-factor-handoff.md`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean`.

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_sourceReadback_residualFactorProduct_eq_matrix

PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceReadback_residualFactorProduct_eq_matrix
```

The first theorem derives the selected-entry residual square-sum equality from
a retained-passive source-readback residual-factor product matrix identity and
a residual-coordinate equivalence to the selected center.  The second theorem
uses this derived equality to call the previous retained-passive selected-
entry local-measure handoff, so callers no longer supply the raw
`hresidual_eq` square-sum hypothesis.

Remaining supplied fields: the source chart, weighted pushforward, residual-
factor matrix identity, local loss bound, and density bounds.  Nonclaims: no
source chart construction, source image equality, pushforward/Jacobian proof,
original-loss comparison, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 retained-passive coordinate-data edge-matrix residual-factor bridge

Reproduction:
`reproduction-a2-retained-passive-coordinate-data-edge-matrix-residual-factor-bridge.md`.
Statement card:
`statement-card-a2-retained-passive-coordinate-data-edge-matrix-residual-factor-bridge.md`.
Review:
`review-a2-retained-passive-coordinate-data-edge-matrix-residual-factor-bridge.md`.

Lean files:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean`,
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean`.

Lean now proves the pure pointwise bridge
`sourceReadback_paperEndpointFixedBaseEdgeMatrix_eq_retainedPassiveData_of_edgeMatrix_eq`,
then uses it in
`sourceReadback_residualFactorProduct_eq_matrix_of_retainedPassiveCoordinateData_edgeMatrix`
and
`aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_retainedPassiveCoordinateData_edgeMatrix`.

This exposes the next Aoyagi-specific residual readout target at the retained-
passive coordinate-data level: construct or identify `retainedData y`, prove
its `edgeMatrix` realizes the fixed-base source chart, and prove the product
identity for `(retainedData y).C`.

Nonclaims: no construction of retained-passive data, no Case 2 entrywise
product identity, no source chart construction, no source image equality, no
pushforward/Jacobian proof, no original-loss comparison, no normal crossings,
no pole order, and no RLCT.

## 2026-06-26 A2 retained-passive Case 2 selected-entry bridge

Reproduction:
`reproduction-a2-retained-passive-case2-selected-entry-bridge.md`.
Statement card:
`statement-card-a2-retained-passive-case2-selected-entry-bridge.md`.
Review:
`review-a2-retained-passive-case2-selected-entry-bridge.md`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean`.

Lean now proves the two-edge retained-passive adapters

```text
residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_entrywise
residualFactorProduct_retainedPassiveCoordinateData_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2PostPivot_entrywise
```

The factor order is pinned in the statement: `data.C 1` is the post-pivot
residual block and `data.C 0` is the following factor.  The source-shaped
adapter targets the successor `(S,J+1)` center and pivot `(J+2,J+2)`, not the
old Case 2 center.

This is finite algebra only.  It does not slice a longer retained-passive
suffix to two edges, construct retained-passive source data, prove the
entrywise displayed product readout, or prove source chart/source image,
pushforward/Jacobian, original-loss comparison, normal crossings, pole order,
or RLCT statements.

## 2026-06-26 A2 retained-passive Case 2 synthetic two-edge data

Reproduction:
`reproduction-a2-retained-passive-case2-synthetic-data.md`.
Statement card:
`statement-card-a2-retained-passive-case2-synthetic-data.md`.
Review:
`review-a2-retained-passive-case2-synthetic-data.md`
passed by xhigh `Ampere the 3rd`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean`.

Lean now defines and proves:

```text
case2PostPivotRetainedPassiveData
case2PostPivotRetainedPassiveData_detChart
case2PostPivotRetainedPassiveData_hdataFactor_of_entrywise
case2PostPivotRetainedPassiveData_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_entrywise
```

The definition builds the concrete two-edge retained-passive datum for the
post-pivot Case 2 endpoint family
`tau -> Case2ResidualColIndex n S (J+1) -> Case2ResidualRowIndex n S (J+1)`.
Its passive fields are zero except `A1passive=1`, and `Ctop=1`; its active
`C` family is exactly `case2PostPivotFreeTwoEdgeFactorFamily`.

The determinant-chart theorem proves the finite retained-passive determinant
condition from identity `Ctop` and identity passive `A1`.  The `hdataFactor`
theorem then delegates to the concrete Case 2 selected-entry bridge, removing
the generic factor-identification hypotheses for this synthetic two-edge
datum while keeping the entrywise successor-source readout and endpoint
equivalence explicit.  The final identity is also exposed under a content-
named residual-factor-product alias.

Nonclaims: no source chart or source edge family is constructed, no longer
retained-passive suffix is sliced or transported to this two-edge datum, no
entrywise displayed product readout is proved, and no source image,
pushforward/Jacobian, original-loss comparison, normal crossings, pole order,
or RLCT statement is proved.

## 2026-06-26 A2 retained-passive fixed-base edge realisation

Reproduction:
`reproduction-a2-retained-passive-fixed-base-edge-realisation.md`.
Statement card:
`statement-card-a2-retained-passive-fixed-base-edge-realisation.md`.
Review:
`review-a2-retained-passive-fixed-base-edge-realisation.md`
passed by xhigh `Pasteur the 4th`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean`.

Lean now proves:

```text
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOf_retainedPassiveEdgeMatrix

sourceReadback_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOf_retainedPassiveEdgeMatrix_eq
```

The first theorem specializes the existing fixed-base prescribed-matrix
realisation API to a retained-passive datum's `edgeMatrix`: the continuous
reverse-edge family built from those matrices has fixed-base edge matrices
exactly `data.edgeMatrix`.  The second theorem adds `data.detChart` and
recovers `data` by source readback.

This removes a future `hedge` equality only when the source edge family is
definitionally realised from `data.edgeMatrix`.  It does not construct
`data`, does not prove literal Case 2 source production, and does not identify
the synthetic Case 2 two-edge datum with a fixed-base source chart or longer
retained-passive suffix.  It proves no source image, pushforward/Jacobian,
original-loss comparison, normal-crossing, pole-order, or RLCT statement.

## 2026-06-26 A2 retained-passive Case 2 pivot-nonzero source readout

Reproduction:
`reproduction-a2-retained-passive-case2-pivot-nonzero-source-readout.md`.
Statement card:
`statement-card-a2-retained-passive-case2-pivot-nonzero-source-readout.md`.
Review:
`review-a2-retained-passive-case2-pivot-nonzero-source-readout.md`.

Lean files:
`lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean`,
`lean/DLNFibre/DLN/Aoyagi/Case2ResidualSelectedEntryChartBridge.lean`,
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean`.

Lean now proves:

```text
SelectedEntrySignedBox.CenterCoord.chartMap_preimageOfPivotNeZero
SelectedEntrySignedBox.CenterCoord.exists_chartMap_eq_value_of_pivot_ne_zero

exists_successorSourceChartMap_entrywise_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_pivot_ne_zero

exists_case2PostPivotRetainedPassiveData_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_pivot_ne_zero
```

This is the fixed-pivot inverse for the selected-entry chart, specialized to
the successor Case 2 center `(S,J+1)` with pivot `(J+2,J+2)`.  Instead of
supplying the full entrywise successor-source readout, callers supply that the
displayed post-pivot product is nonzero at the fixed successor pivot.  Lean
then constructs `yNext` and derives the old entrywise readout internally.

The pivot-nonzero condition remains supplied.  This is not source chart
production, not endpoint-index alignment, not longer-suffix transport, and
not pushforward/Jacobian, original-loss, normal-crossing, pole-order, or RLCT
work.

## 2026-06-26 A2 adjacent two-edge residual-factor transport

Reproduction:
`reproduction-a2-adjacent-two-edge-residual-factor-transport.md`.
Statement card:
`statement-card-a2-adjacent-two-edge-residual-factor-transport.md`.
Review:
`review-a2-adjacent-two-edge-residual-factor-transport.md`
passed by xhigh `Zeno the 4th`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`.

Lean now proves:

```text
ChartLocalSuffixState.residualFactorProduct_one_edge_eq_factor
ChartLocalSuffixState.residualFactorProduct_adjacent_two_eq_mul
ChartLocalSuffixState.residualFactorProduct_adjacent_two_submatrix_eq_mul
```

This is the generic adjacent-window transport requested by the retained-
passive/Case 2 bridge scouts. For a supplied residual-factor family `C`, the
product over the adjacent window from `p+2` to `p` is the ordered product
`C_(p+1) * C_p`; after endpoint equivalences, the submatrix of the adjacent
window product is the product of the two reindexed factors.

This buys reusable finite transport for a future adjacent Case 2 selected-
entry consumer. It does not construct endpoint equivalences, prove the
Case 2 factor identities for a fixed-base source-readback family, remove
outside factors from a full retained-passive suffix, prove pivot nonzero,
produce a source chart, or prove pushforward/Jacobian, original-loss,
normal-crossing, pole-order, or RLCT statements.

## 2026-06-26 A2 adjacent-window Case 2 selected-entry consumer

Reproduction:
`reproduction-a2-adjacent-window-case2-selected-entry-consumer.md`.
Statement card:
`statement-card-a2-adjacent-window-case2-selected-entry-consumer.md`.
Review:
`review-a2-adjacent-window-case2-selected-entry-consumer.md`
passed by xhigh `Herschel the 4th`.

Lean files:
`lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean`,
`lean/DLNFibre/DLN/Aoyagi/Case2ResidualSelectedEntryChartBridge.lean`,
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean`.

Lean now proves:

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_residualFactorProduct_adjacent_two_submatrix

residualFactorProduct_adjacent_two_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise

residualFactorProduct_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise

exists_residualFactorProduct_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_pivot_ne_zero

exists_residualFactorProduct_retainedPassiveCoordinateData_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2PostPivot_pivot_ne_zero
```

This is the conditional adjacent-window consumer of the previous generic
transport.  It takes the adjacent index `p`, endpoint equivalences, and the
two factor identities as hypotheses.  The fixed-pivot variant still takes the
displayed-product nonzero hypothesis at `(J+2,J+2)` as a hypothesis and uses
the existing selected-entry inverse to produce `yNext`.

This does not construct endpoint equivalences, prove source-readback factor
identities, identify the full fixed-base endpoint product with the adjacent
window, prove pivot nonzero, produce a source chart, or prove
pushforward/Jacobian, original-loss, normal-crossing, pole-order, or RLCT
statements.

## 2026-06-26 A2 source-readback per-factor residual block

Reproduction:
`reproduction-a2-source-readback-per-factor-residual-block.md`.
Statement card:
`statement-card-a2-source-readback-per-factor-residual-block.md`.
Review:
`review-a2-source-readback-per-factor-residual-block.md`
passed by xhigh `Pascal the 4th`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`.

Lean now exposes:

```text
sourceReadback_C_eq_schurResidualBlock_sourceReadbackTransformedEdge
```

For a retained-passive-shaped source edge family `E`, the theorem states that
`(sourceReadback E).C p` is exactly the Schur residual block of
`sourceReadbackTransformedEdge E p`.  The proof is `rfl`; no determinant-chart
hypothesis is needed.

This is a per-factor API handle for the next adjacent-window/source-hypothesis
frontier.  It does not prove that the transformed source edge is a displayed
Case 2 post-pivot block, does not construct endpoint equivalences, does not
collapse a full fixed-base endpoint product to an adjacent window, and does
not prove pivot nonzero, source production, pushforward/Jacobian,
original-loss, normal-crossing, pole-order, or RLCT statements.

## 2026-06-26 A2 retained-passive source-map factor readout

Reproduction:
`reproduction-a2-retained-passive-source-map-factor-readout.md`.
Statement card:
`statement-card-a2-retained-passive-source-map-factor-readout.md`.
Review:
`review-a2-retained-passive-source-map-factor-readout.md`
passed by xhigh `Confucius the 4th`.

Lean files:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`,
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean`.

Lean now proves:

```text
schurResidualBlock_sourceReadbackTransformedEdge_edgeMatrix_eq_C

schurResidualBlock_sourceReadbackTransformedEdge_case2PostPivotRetainedPassiveData_edgeMatrix_one_eq_residualBlock

schurResidualBlock_sourceReadbackTransformedEdge_case2PostPivotRetainedPassiveData_edgeMatrix_zero_eq_freeFollowingFactor
```

The first theorem uses the retained-passive source-map/readback inverse:
under `data.detChart`, the transformed source edge of `data.edgeMatrix` has
Schur residual block `data.C p`.  The two Case 2 theorems specialize this to
the synthetic two-edge datum `case2PostPivotRetainedPassiveData`, whose edge
`1` factor is the displayed post-pivot residual block and whose edge `0`
factor is the displayed free following factor.

This moves the factor-identity frontier only for constructed retained-passive
source-map families.  It does not construct real fixed-base endpoint
equivalences, identify a real Aoyagi source chart/suffix family with the
synthetic two-edge datum, collapse a full endpoint product to the adjacent
window, prove pivot nonzero, or prove source image, pushforward/Jacobian,
original-loss, normal-crossing, pole-order, or RLCT statements.

## 2026-06-26 A2 full-to-adjacent-window outside-factor transport

Reproduction:
`reproduction-a2-full-to-adjacent-window-outside-factor-transport.md`.
Statement card:
`statement-card-a2-full-to-adjacent-window-outside-factor-transport.md`.
Review:
`review-a2-full-to-adjacent-window-outside-factor-transport.md`
passed by xhigh `Mencius the 4th`.

Lean files:
`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`,
`lean/DLNFibre/DLN/Aoyagi/Case2ResidualSelectedEntryChartBridge.lean`.

Lean now proves:

```text
residualFactorProduct_split_adjacent_two

residualFactorProduct_split_adjacent_two_of_middle_eq

residualFactorProduct_split_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
```

The generic theorems split a full residual-factor product through an adjacent
two-edge window and replace only that middle window by a supplied matrix.  The
Case 2 theorem instantiates the supplied matrix with the existing successor
selected-entry center-coordinate matrix, using the already-landed adjacent
Case 2 readout.

This closes the immediate full-to-window bookkeeping gap without collapsing a
longer suffix to the adjacent window.  The outside products remain in the
statement.  It does not prove endpoint equivalences, identify a real source
chart/suffix family, prove pivot nonzero, absorb outside factors, or prove
source image, pushforward/Jacobian, original-loss, normal-crossing,
pole-order, or RLCT statements.

## 2026-06-26 A2 retained-passive raw edge tuple target

Reproduction:
`reproduction-a2-retained-passive-raw-edge-tuple-target.md`.
Statement card:
`statement-card-a2-retained-passive-raw-edge-tuple-target.md`.
Review:
`review-a2-retained-passive-raw-edge-tuple-target.md`
passed by read-only scout `Bernoulli the 4th`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean`.

Lean now exposes:

```text
EdgeFamilyTuple
rawEdgeTupleA1
rawEdgeTupleA3
edgeFamilyOfRawOrderTuple
edgeFamilyRawOrderTuple
edgeFamilyRawOrderLinearEquiv
topologyTupleEdgeRawOrder
injOn_topologyTupleEdgeRawOrder_detChartSet
```

The raw tuple readout packs edge-family blocks into the existing
`TopologyTuple` order: first top-left block into `Ctop`, later top-left blocks
into `A1passive`, all upper-right blocks into `F2`, nonterminal lower-left
blocks into `A3passive`, the last lower-left block into `F3`, and all
lower-right blocks into `C`.  The inverse reconstructs each edge with
`Matrix.fromBlocks`; Lean proves the two inverse identities and a linear
equivalence.

Composing this readout with `topologyTupleEdgeMatrix` gives the endomap
`topologyTupleEdgeRawOrder`, and injectivity on the tuple determinant chart is
transferred back through the raw edge-family equivalence.

This removes the target-product mismatch for future retained-passive
derivative work.  It does not prove a derivative, determinant formula,
density, measure pushforward, image equality, homeomorphism, source-rank
coverage, normal-crossing theorem, pole order, or RLCT statement.

## 2026-06-26 A2 retained-passive raw-order block formulas

Reproduction:
`reproduction-a2-retained-passive-raw-order-derivative-jacobian-plan.md`.
Statement card:
`statement-card-a2-retained-passive-raw-order-block-formulas.md`.

Lean files:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`,
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean`.

Lean now exposes fixed-base raw edge block formulas:

```text
topLeftCorner_retainedPassiveFixedBaseEdgeMatrix
upperRightBlock_retainedPassiveFixedBaseEdgeMatrix
lowerLeftBlock_retainedPassiveFixedBaseEdgeMatrix
lowerRightBlock_retainedPassiveFixedBaseEdgeMatrix
toBlocks11_retainedPassiveFixedBaseEdgeMatrix
toBlocks12_retainedPassiveFixedBaseEdgeMatrix
toBlocks21_retainedPassiveFixedBaseEdgeMatrix
toBlocks22_retainedPassiveFixedBaseEdgeMatrix
```

and tuple-level component formulas:

```text
topologyTupleEdgeRawOrder_A1passive
topologyTupleEdgeRawOrder_F2
topologyTupleEdgeRawOrder_A3passive
topologyTupleEdgeRawOrder_C
topologyTupleEdgeRawOrder_Ctop
topologyTupleEdgeRawOrder_F3
```

The pointwise formula is the block product

```text
fromBlocks 1 F2full_(p.succ) 0 1 *
  fromBlocks A_p (-(A_p * F2full_(p.castSucc))) L_p
    (C_p - L_p * F2full_(p.castSucc)).
```

This is the formula layer for the next retained-passive derivative theorem.
It does not prove a derivative, determinant formula, density, measure
pushforward, image equality, source-rank coverage, normal-crossing theorem,
pole order, or RLCT statement.

## 2026-06-26 A2 retained-passive solved A1 derivative

Reproduction:
`reproduction-a2-retained-passive-solved-a1-derivative.md`.
Statement card:
`statement-card-a2-retained-passive-solved-a1-derivative.md`.
Review:
`review-a2-retained-passive-solved-a1-derivative.md`
passed by xhigh read-only explorer `Nietzsche the 4th`.

Lean files:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`,
`lean/DLNFibre.lean`.

Lean now proves the coordinate-projection differentiability helpers for the
retained-passive tuple, differentiability of the passive top-left tail product,
and

```text
differentiableAt_solvedA1_of_mem_topologyTupleDetChartSet
```

for every solved top-left block on the tuple determinant chart.  The endpoint
case uses determinant-unit differentiability of matrix inversion; successor
cases are tuple projections.

This is a partial derivative foothold only.  It does not prove solved lower-left
differentiability, full raw-order differentiability, a tangent equivalence,
determinant formula, Jacobian density, measure pushforward, image equality,
source-rank coverage, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 retained-passive solved A3 derivative

Reproduction:
`reproduction-a2-retained-passive-solved-a3-derivative.md`.
Statement card:
`statement-card-a2-retained-passive-solved-a3-derivative.md`.
Review:
`review-a2-retained-passive-solved-a3-derivative.md`
passed as a route audit by xhigh read-only explorer `Newton the 4th`; the
controller fixed the typeclass issues Newton observed in the dirty draft.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

Lean now adds a heterogeneous matrix multiplication differentiability helper
and proves:

```text
differentiableAt_retainedPassiveA3WithoutLast
differentiableAt_residualFactorProduct_C
differentiableAt_residualFactorProduct_solvedA1_of_mem_topologyTupleDetChartSet
differentiableAt_retainedPassiveLowerLeftProductTailSum_of_mem_topologyTupleDetChartSet
differentiableAt_solvedA3_of_mem_topologyTupleDetChartSet
```

This closes the lower-left solved-family differentiability component.  It does
not prove full raw-order differentiability, a tangent equivalence, determinant
formula, Jacobian density, measure pushforward, image equality, source-rank
coverage, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 retained-passive raw-order differentiability

Reproduction:
`reproduction-a2-retained-passive-raw-order-differentiability.md`.
Statement card:
`statement-card-a2-retained-passive-raw-order-differentiability.md`.
Review:
`review-a2-retained-passive-raw-order-differentiability.md`
passed by xhigh read-only explorer `Carver the 4th`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

Lean now proves:

```text
differentiableAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
```

The proof assembles the six landed raw-order component formulas from
`RetainedPassiveCoordinatesTopology.lean`, using solved-`A1` and solved-`A3`
differentiability, tuple projection differentiability for `F2full` and `C`,
and `differentiableAt_matrix_mul` for all rectangular products.

This closes the differentiability-only layer for the retained-passive
raw-order target-coordinate endomap.  It does not identify the derivative,
prove a tangent equivalence, determinant unit/formula, Jacobian density,
measure pushforward, image equality, source-rank coverage, normal crossings,
pole order, or RLCT.

## 2026-06-26 A2 retained-passive raw-order inverse chart

Reproduction:
`reproduction-a2-retained-passive-raw-order-inverse-chart.md`.
Statement card:
`statement-card-a2-retained-passive-raw-order-inverse-chart.md`.
Review:
`review-a2-retained-passive-raw-order-inverse-chart.md`
passed by xhigh read-only explorer `Meitner the 4th`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean`.

Lean now defines the raw-order target chart

```text
topologyTupleRawOrderSourceRecursiveDetChartSet
```

and the explicit raw-order readback

```text
topologyTupleEdgeRawOrderInverse
```

then proves maps-to, inverse-on-chart, and image equality:

```text
mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
topologyTupleEdgeRawOrderInverse_mem_topologyTupleDetChartSet
topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
topologyTupleEdgeRawOrder_topologyTupleEdgeRawOrderInverse
image_topologyTupleEdgeRawOrder_detChartSet
```

This is target-chart bookkeeping for the retained-passive raw-order map.  It
does not prove differentiability of the inverse, a formal tangent equivalence,
determinant unit/formula, Jacobian density, measure pushforward, source-rank
coverage, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 retained-passive raw-order topological chart

Reproduction:
`reproduction-a2-retained-passive-raw-order-topological-chart.md`.
Statement card:
`statement-card-a2-retained-passive-raw-order-topological-chart.md`.
Review:
`review-a2-retained-passive-raw-order-topological-chart.md`
passed by xhigh read-only explorer `Peirce the 4th`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean`.

Lean now proves continuity of the raw-order edge tuple reassembly/readout maps,
openness of the raw-order source-recursive determinant target chart, subtype
continuity of the forward raw-order map and inverse readback map, and packages
the result as:

```text
topologyTupleDetChartSet_rawOrderSourceRecursiveDetChartSet_homeomorph
topologyTupleEdgeRawOrder_openPartialHomeomorph
```

This turns the set-level raw-order inverse chart into a topological chart.  It
does not prove inverse differentiability, identify the derivative, prove a
tangent equivalence, determinant unit/formula, Jacobian density, measure
pushforward, source-rank coverage, normal crossings, pole order, or RLCT.

## 2026-06-26 A2 retained-passive raw-order inverse differentiability

Reproduction:
`reproduction-a2-retained-passive-raw-order-inverse-differentiability.md`.
Statement card:
`statement-card-a2-retained-passive-raw-order-inverse-differentiability.md`.
Review:
`review-a2-retained-passive-raw-order-inverse-differentiability.md`
passed by xhigh read-only explorer `Nash the 4th`, with a low dependency
granularity caveat.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

Lean now proves generic real differentiability helpers for matrix submatrix,
`fromBlocks`, block projections, and Schur residual blocks, then proves
source-readback suffix-state/transformed-edge differentiability and the final
inverse theorem:

```text
differentiableAt_topologyTupleEdgeRawOrderInverse_of_mem_rawOrderSourceRecursiveDetChartSet
```

The proof mirrors the deterministic suffix recursion: the `L` update uses the
inverse of `S.Ctop * topLeftCorner M`, whose determinant unit comes from the
induction-carried `S.Ctop` unit and the recursive chart unit for
`topLeftCorner M`.

This closes inverse differentiability for the raw-order target chart.  It does
not identify the derivative, prove a tangent equivalence, determinant
unit/formula, Jacobian density, measure pushforward, source-rank coverage,
normal crossings, pole order, or RLCT.  Dependency caveat: the module currently
imports the one-step derivative module for generic matrix inverse/multiplication
calculus helpers; split those helpers only if module-boundary hygiene becomes a
concrete blocker.

## 2026-06-26 A2 retained-passive raw-order fderiv determinant unit

Reproduction:
`reproduction-a2-retained-passive-raw-order-fderiv-det-unit.md`.
Statement card:
`statement-card-a2-retained-passive-raw-order-fderiv-det-unit.md`.
Review:
`review-a2-retained-passive-raw-order-fderiv-det-unit.md`
passed by xhigh read-only explorer `Hilbert the 4th`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

Lean now proves the local tangent inverse identities

```text
fderiv_topologyTupleEdgeRawOrderInverse_comp_fderiv_topologyTupleEdgeRawOrder
fderiv_topologyTupleEdgeRawOrder_comp_fderiv_topologyTupleEdgeRawOrderInverse
```

and the determinant-unit theorem

```text
fderiv_topologyTupleEdgeRawOrder_det_isUnit_of_mem_topologyTupleDetChartSet
```

The proof uses the already-landed open raw-order partial homeomorphism,
ambient differentiability of the forward and inverse maps, ordinary chain
rule, and neighborhood-form inverse identities coming from openness of the
source and target chart sets.

This closes density-free tangent invertibility for the retained-passive
raw-order chart.  It does not give an explicit derivative formula, determinant
formula, Jacobian density, measure pushforward, source-rank coverage, normal
crossings, pole order, or RLCT.

## 2026-06-27 A2 retained-passive raw-order Jacobian density interface

Reproduction:
`reproduction-a2-retained-passive-raw-order-jacobian-density-interface.md`.
Statement card:
`statement-card-a2-retained-passive-raw-order-jacobian-density-interface.md`.
Review:
`review-a2-retained-passive-raw-order-jacobian-density-interface.md`
accepted by xhigh read-only explorer `Laplace the 4th`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

Lean now defines the forward absolute determinant of the retained-passive
raw-order ambient derivative:

```text
topologyTupleEdgeRawOrderFDerivAbsDet
```

and proves:

```text
topologyTupleEdgeRawOrderFDerivAbsDet_pos_of_mem_topologyTupleDetChartSet
eventually_topologyTupleEdgeRawOrderFDerivAbsDet_pos_nhds
exists_pos_eventually_le_topologyTupleEdgeRawOrderFDerivAbsDet_nhds_of_continuousAt
exists_pos_eventually_topologyTupleEdgeRawOrderFDerivAbsDet_le_nhds_of_continuousAt
```

The pointwise positivity follows from the determinant-unit theorem.  The
eventual positivity follows from openness of the determinant chart.  The local
lower and upper bounds require an explicit `ContinuousAt` hypothesis for the
absolute determinant function.

This is the first retained-passive density-facing API after tangent
invertibility.  It still does not prove continuity of the retained-passive
derivative family, an explicit determinant formula, inverse-density formula,
measure pushforward, source-density identity, normal crossings, pole order, or
RLCT.

## 2026-06-27 A2 retained-passive raw-order weighted change of variables

Reproduction:
`reproduction-a2-retained-passive-raw-order-weighted-cov.md`.
Statement card:
`statement-card-a2-retained-passive-raw-order-weighted-cov.md`.
Review:
`review-a2-retained-passive-raw-order-weighted-cov.md`
accepted by xhigh read-only explorer `Aristotle the 4th`.

Lean files:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesMeasure.lean`,
`lean/DLNFibre.lean`.

Lean now proves the retained-passive raw-order weighted Jacobian
change-of-variables theorem:

```text
nullMeasurableSet_topologyTupleDetChartSet
map_topologyTupleEdgeRawOrder_restrict_detChart_withDensity_abs_det
map_topologyTupleEdgeRawOrder_withDensity_absDet_eq_restrict_rawSourceChart
map_topologyTupleEdgeRawOrder_restrict_detChart_withDensity_abs_det'
map_topologyTupleEdgeRawOrder_withDensity_absDet_eq_restrict_rawSourceChart'
```

The proof applies Mathlib's finite-dimensional real Jacobian theorem to the
endomap `topologyTupleEdgeRawOrder` on the tuple determinant chart.  The
within-derivative input comes from the ambient differentiability theorem, and
injectivity/image facts come from the retained-passive raw-order chart.

This proves only the forward weighted pushforward identity with the
source-side `|det Df|` weight.  It does not prove an explicit determinant
formula, determinant-density continuity, local bounded-density estimate,
inverse Jacobian density, source-prior density identity, original DLN source
pushforward, normal crossings, pole order, or RLCT.

## 2026-06-27 A2 retained-passive inverse Jacobian density

Reproduction:
`reproduction-a2-retained-passive-inverse-jacobian-density.md`.
Statement card:
`statement-card-a2-retained-passive-inverse-jacobian-density.md`.
Review:
`review-a2-retained-passive-inverse-jacobian-density.md`
accepted by xhigh read-only explorer `Raman the 4th` after a module-docstring
repair.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesMeasure.lean`.

Lean now defines the target-side inverse Jacobian density:

```text
topologyTupleEdgeRawOrderInverseJacobianDensity
```

and proves:

```text
topologyTupleEdgeRawOrderInverseJacobianDensity_apply_chartMap
topologyTupleEdgeRawOrderFDerivAbsDet_mul_inverseJacobianDensity_apply_chartMap
topologyTupleEdgeRawOrderInverseJacobianDensity_pos_of_mem_rawSourceChart
map_topologyTupleEdgeRawOrder_restrict_detChart_eq_withDensity_inverseJacobian_of_aemeasurable
```

The pointwise algebra defines `K(y)=J(g y)⁻¹`, where `J` is the forward
absolute determinant and `g` is raw-order source readback.  The determinant
chart inverse law gives `K(f z)=J(z)⁻¹`; positivity of `J(z)` gives the
`ENNReal.ofReal` cancellation.  The measure theorem is deliberately conditional
on a.e.-measurability of the forward density, inverse density, and composed
inverse density.

Focused module build, full `DLNFibre` build, `scripts/sorries`, and
`git diff --check` passed.  This proves pointwise inverse-density algebra and a
conditional inverse-density COV form.  It does not prove determinant-density
continuity or measurability, an explicit determinant formula, source-prior
density identity, original DLN source pushforward, normal crossings, pole
order, or RLCT.

## 2026-06-27 A2 retained-passive composed weighted COV

Reproduction:
`reproduction-a2-retained-passive-composed-weighted-cov.md`.
Statement card:
`statement-card-a2-retained-passive-composed-weighted-cov.md`.
Review:
`review-a2-retained-passive-composed-weighted-cov.md`
accepted by xhigh read-only explorer `Harvey the 4th`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesMeasure.lean`.

Lean now proves generic downstream composition forms:

```text
map_comp_topologyTupleEdgeRawOrder_withDensity_absDet_eq_map_restrict_rawSourceChart
map_comp_topologyTupleEdgeRawOrder_restrict_detChart_eq_map_invJac_of_aemeasurable
```

and edge-family readback specializations:

```text
map_topologyTupleEdgeMatrix_withDensity_absDet_eq_map_edgeFamilyOfRawOrderTuple
map_topologyTupleEdgeMatrix_restrict_detChart_eq_map_edgeFamily_invJac_of_aemeasurable
```

The forward form composes the weighted COV theorem with an arbitrary downstream
a.e.-measurable map.  The inverse form composes the conditional inverse-density
COV theorem and therefore retains the explicit `hF`, `hG`, and `hG_comp`
measurability hypotheses.  The edge-family versions use only
`Measure.map_congr` and the raw-order readback identity.

Focused module build, full `DLNFibre` build, `scripts/sorries`, and
`git diff --check` passed.  This is chart-coordinate measure-map composition
only; it does not prove determinant-density measurability, source-prior
transport, original DLN source pushforward, local-source coverage, normal
crossings, pole order, or RLCT.

## 2026-06-27 A2 retained-passive raw-order local-source COV bridge

Reproduction:
`reproduction-a2-retained-passive-raw-order-local-source-cov-bridge.md`.
Statement card:
`statement-card-a2-retained-passive-raw-order-local-source-cov-bridge.md`.
Review:
`review-a2-retained-passive-raw-order-local-source-cov-bridge.md`
accepted by xhigh read-only reviewer `Parfit the 4th`.

Lean files:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean` and
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean`.

Lean now proves:

```text
paperEndpointFixedBaseRetainedPassiveP13LocalSource_mem_of_edgeFamilyOfRawOrderTuple_realization
measure_map_restrict_retainedPassiveP13LocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_absDet_of_realization
```

The first theorem says that a raw-order target point `y in T` lands in the
retained-passive p.13 local source after a supplied fixed-base realization
whose edge matrices agree with `edgeFamilyOfRawOrderTuple y`.  The second
theorem applies the already-proved composed weighted raw-order COV theorem and
restricts the resulting raw-target pushforward
`mu = Measure.map sourceChart (m.restrict T)` to the local source.

This is a chart-produced local-source measure identity only.  It does not prove
determinant-density continuity, inverse-density measurability, original
source-prior transport, selected-entry target-image equality, source-rank
coverage, normal crossings, pole order, or RLCT.

Focused `RetainedPassiveLocalMeasure`, full `DLNFibre`, `scripts/sorries`, and
`git diff --check` passed.  The sorry scan reported `0 sorry`, `0 #exit`,
`0 native_decide`, and `0 axiom`.

## 2026-06-27 A2 retained-passive raw-order C1 and density continuity

Reproduction:
`reproduction-a2-retained-passive-raw-order-c1-density-continuity.md`.
Statement card:
`statement-card-a2-retained-passive-raw-order-c1-density-continuity.md`.
Review:
`review-a2-retained-passive-raw-order-c1-density-continuity.md`
accepted by xhigh read-only reviewer `Wegener the 4th`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

Lean now proves a forward `C^1` chain for `topologyTupleEdgeRawOrder`,
including the solved `A1` tail, solved `A3` lower-left tail sum, and raw-order
component assembly.  The payoff theorems are:

```text
contDiffAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
continuousAt_fderiv_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
continuousAt_fderiv_topologyTupleEdgeRawOrder_apply_of_mem_topologyTupleDetChartSet
continuousAt_topologyTupleEdgeRawOrderFDerivAbsDet_of_mem_topologyTupleDetChartSet
exists_pos_eventually_le_topologyTupleEdgeRawOrderFDerivAbsDet_nhds
exists_pos_eventually_topologyTupleEdgeRawOrderFDerivAbsDet_le_nhds
```

Focused `RetainedPassiveCoordinatesDerivative` build passed.  This removes the
supplied-continuity hypothesis for forward determinant-density local bounds at
determinant-chart points.  It does not prove an explicit determinant formula,
inverse-density measurability, original source-prior transport, selected-entry
target-image equality, source-rank coverage, normal crossings, pole order, or
RLCT.

## 2026-06-27 A2 retained-passive unconditional inverse-density COV

Reproduction:
`reproduction-a2-retained-passive-unconditional-inverse-density-cov.md`.
Statement card:
`statement-card-a2-retained-passive-unconditional-inverse-density-cov.md`.
Review:
`review-a2-retained-passive-unconditional-inverse-density-cov.md`
accepted by xhigh read-only reviewer `Heisenberg the 4th`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesMeasure.lean`.

Lean now adds target-chart null-measurability and inverse-density continuity:

```text
nullMeasurableSet_topologyTupleRawOrderSourceRecursiveDetChartSet
continuousAt_topologyTupleEdgeRawOrderInverseJacobianDensity_of_mem_rawSourceChart
continuousAt_topologyTupleEdgeRawOrderInverseJacobianDensity_comp_of_mem_rawSourceChart
```

It also removes the explicit density measurability hypotheses from the
retained-passive inverse-density COV layer:

```text
map_topologyTupleEdgeRawOrder_restrict_detChart_eq_withDensity_inverseJacobian
map_comp_topologyTupleEdgeRawOrder_restrict_detChart_eq_map_invJac
map_topologyTupleEdgeMatrix_restrict_detChart_eq_map_edgeFamily_invJac
```

The proof derives the three a.e.-measurability inputs for the older conditional
theorem from the previous C1 forward-density continuity checkpoint, continuity
of the raw-order inverse chart on `T`, positivity of the forward density at the
inverse point, and continuity of `ENNReal.ofReal`.

Focused `RetainedPassiveCoordinatesMeasure` and full `DLNFibre` builds passed;
the full build had only pre-existing unrelated linter warnings.
`scripts/sorries` reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  `git diff --check` passed.  Heisenberg the 4th found no blocking
issues in xhigh read-only review.

Nonclaims: no explicit determinant formula, source-prior transport, original
DLN source pushforward, selected-entry target-image equality, source-rank
coverage, normal crossings, pole order, or RLCT is proved.

## 2026-06-27 A2 retained-passive canonical local-source COV

Reproduction:
`reproduction-a2-retained-passive-canonical-local-source-cov.md`.
Statement card:
`statement-card-a2-retained-passive-canonical-local-source-cov.md`.
Review:
`review-a2-retained-passive-canonical-local-source-cov.md`
accepted by xhigh read-only reviewer `Sartre the 4th`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean`.

Lean now proves:

```text
measure_map_restrict_retainedPassiveP13CanonicalLocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_absDet
```

This specializes the previous arbitrary-realization local-source COV theorem
to the canonical fixed-base source edge-family chart

```text
y |-> paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
        (ofTopologyTuple (topologyTupleEdgeRawOrderInverse y)).
```

The proof checks two hypotheses internally.  First, on the raw-order target
chart `T`, the canonical edge family realizes `edgeFamilyOfRawOrderTuple y`
because fixed-base readback gives the edge matrix of
`ofTopologyTuple (topologyTupleEdgeRawOrderInverse y)` and the raw-order
right-inverse theorem gives `topologyTupleEdgeRawOrder (g y) = y`.  Second,
the canonical source chart is continuous on `T`, hence a.e.-measurable, by
composing raw-order inverse continuity, `ofTopologyTuple` continuity, and the
fixed-base determinant-chart source-chart continuity.

Focused `RetainedPassiveLocalMeasure` build passed.  Full `DLNFibre` build
passed with pre-existing unrelated linter warnings.  `scripts/sorries`
reported `0 sorry`, `0 #exit`, `0 native_decide`, and `0 axiom`.
`git diff --check` passed.  Independent xhigh review passed.

This is still only a chart-produced retained-passive local-source measure
identity.  It is not original source-prior transport, selected-entry
target-image equality, source-rank coverage, an explicit determinant formula,
normal crossings, pole order, or RLCT.

## 2026-06-27 A2 retained-passive raw-order determinant formula reproduction

Reproduction:
`reproduction-a2-retained-passive-raw-order-determinant-formula.md`.
Statement card:
`statement-card-a2-retained-passive-raw-order-determinant-formula.md`.

The controller reproduced the explicit determinant factorization for the
already-formalized retained-passive raw-order coordinate map.  The proposed
forward absolute determinant on the determinant chart is

```text
|det Tail|^(-|rho|)
* |det LastTop|^(|kappa'_(M+1)|)
* product_{p : Fin (M+1)} |det (A p)|^(|kappa'_p|).
```

Here `A p` is the solved top-left family,
`Tail = retainedPassiveA1TailAfterFirst A = A_M * ... * A_1` with empty
product `1`, and

```text
LastTop =
  residualFactorProduct A (Fin.last (M+1)) (Fin.last M).castSucc
    (Fin.last M).castSucc.le_last.
```

Independent xhigh endpoint check by `Boole the 4th` confirmed that
`LastTop = solvedA1 (Fin.last M)`: for `M > 0` it is the final passive top
block, and for `M = 0` it is `Ctop`, not `1`.  The two tails must not be
identified.

Lean status: the first reusable gap is now closed by
`lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean`, proving
`linearMap_det_mulLeftLinearMap` and `linearMap_det_mulRightLinearMap`.
No explicit retained-passive determinant formula has been implemented yet.
The existing retained-passive library proves only the abstract forward
determinant is unit/positive/continuous on the chart.

Nonclaims: no source-prior transport, selected-entry image equality,
source-rank coverage, normal crossings, pole order, or RLCT.  The current VM
could not extract the PDF, so source-fidelity against Aoyagi p.13 still needs
a manual/PDF-readable check before a final source claim depends on the note.

## 2026-06-27 A2 fixed-passive formal Jacobian determinant

Reproduction:
`reproduction-a2-fixed-passive-formal-jacobian-determinant.md`.
Statement card:
`statement-card-a2-fixed-passive-formal-jacobian-determinant.md`.
Review:
`review-a2-fixed-passive-formal-jacobian-determinant.md`
accepted by xhigh read-only reviewer `Arendt the 4th`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/ProductReductionStepJacobian.lean`.

Lean now proves the exact determinant of the one-step fixed-passive p.13
formal tangent map.  New names:

```text
productStepFixedPassiveDiagonalFormalJacobian
productStepFixedPassiveCShear
productStepFixedPassiveF3Shear
productStepFixedPassiveFormalJacobian_eq_shear_comp_diagonal
productStepFixedPassiveDiagonalFormalJacobian_det_eq
productStepFixedPassiveCShear_det_eq_one
productStepFixedPassiveF3Shear_det_eq_one
productStepFixedPassiveFormalJacobian_det_eq_multiplication_blocks
productStepFixedPassiveFormalJacobian_det_eq
```

The final theorem states

```text
LinearMap.det (productStepFixedPassiveFormalJacobian C1 D A1 A3)
  = A1.det ^ Fintype.card rho
    * (-A1^{-1}).det ^ Fintype.card nu.
```

The proof factors the map as one diagonal product map followed by two
determinant-one shears.  This closes the first formal-linear determinant
subproblem needed for the retained-passive explicit determinant route.

Focused `ProductReductionStepJacobian` and full `DLNFibre` builds passed.
The full build reports only the existing linter warning profile.  `scripts/sorries`
reported `0 sorry`, `0 #exit`, `0 native_decide`, and `0 axiom`.
`git diff --check` passed.  `#print axioms` for the two new determinant
theorems reports `[propext, Classical.choice, Quot.sound]`.

Nonclaims: this is not the retained-passive total determinant formula, not an
analytic `fderiv` theorem, not source-prior transport, not normal crossings,
not pole order, and not RLCT.

## 2026-06-27 A2 edge-local `(F,C)` pair determinant

Reproduction:
`reproduction-a2-edge-local-fc-pair-determinant.md`.
Statement card:
`statement-card-a2-edge-local-fc-pair-determinant.md`.
Review:
`review-a2-edge-local-fc-pair-determinant.md`
accepted by xhigh read-only reviewer `Lagrange the 4th`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean`.

Lean now proves the edge-local determinant factor from the retained-passive
raw-order determinant route.  For fixed

```text
A : Matrix rho rho K
H : Matrix rho mu K
G : Matrix mu rho K
```

the map

```text
(F, C) |->
  (-(A + H*G) * F + H * C,
   -G * F + C)
```

on `Matrix rho kappa K x Matrix mu kappa K`, in the displayed `(F,C)` input
and `(Y12,Y22)` output order, has determinant

```text
(-A).det ^ Fintype.card kappa.
```

New Lean names include `linearEquivUpperShear`,
`linearEquivUpperShear_det_eq_one`, `edgeLocalFCPairLinearMap_apply`, and
`edgeLocalFCPairLinearMap_det_eq`.  The proof factors the map as lower shear
`(F,C) |-> (F,C-GF)`, diagonal map `(F,C) |-> (-AF,C)`, and upper shear
`(F,C) |-> (F+HC,C)`.

Focused `MatrixLinearDeterminant` and downstream
`ProductReductionStepJacobian` builds passed.  After review, the older private
product/shear determinant helpers in `ProductReductionStepJacobian.lean` were
replaced by the promoted helpers in `MatrixLinearDeterminant.lean`.
Full `DLNFibre` build passed with the existing warning profile.
`scripts/sorries` reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  `git diff --check` passed.  Axiom audit for the new determinant
theorem reports `[propext, Classical.choice, Quot.sound]`.

Nonclaims: this is not the full retained-passive raw-order determinant formula,
not an analytic `fderiv` theorem, not source-prior transport, not normal
crossings, not pole order, and not RLCT.

## 2026-06-27 A2 retained-passive actual derivative C unshear

Reproduction:
`reproduction-a2-retained-passive-actual-derivative-formal-shear-bridge.md`.
Statement card:
`statement-card-a2-retained-passive-actual-derivative-c-unshear.md`.
Review:
`review-a2-retained-passive-actual-derivative-c-unshear.md`
accepted by xhigh read-only reviewer `Euler the 5th` after a documentation
indexing nit was fixed.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

Lean now proves the first analytic shear identity comparing the actual
Frechet derivative of `topologyTupleEdgeRawOrder` with the formal raw-order
Jacobian shape.  The helper
`rawEdgeTupleA3_topologyTupleEdgeRawOrder` identifies the lower-left raw
readout with the solved lower-left block.  The theorem
`fderiv_topologyTupleEdgeRawOrder_C_unshear_apply` proves that, at a
determinant-chart point, adding the lower-left derivative component multiplied
by the fixed basepoint `F2` coefficient changes the actual lower-right
derivative block into

```text
v.C p - coord.solvedA3 p * v.F2 p.
```

The follow-up bridge
`C_unshear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`
packages this as agreement with the `C` component of the point-specialized
formal raw-order map.

This is the `C` component of the formal raw-order map after the determinant-one
target shear.  It is not the full analytic determinant formula, not the
absolute determinant comparison with the formal raw-order determinant, not a
measure pushforward, not normal crossings, not pole order, and not RLCT.

## 2026-06-27 A2 retained-passive actual derivative passive A3 identity

Reproduction:
`reproduction-a2-retained-passive-actual-derivative-a3passive-identity.md`.
Statement card:
`statement-card-a2-retained-passive-actual-derivative-a3passive-identity.md`.
Review:
`review-a2-retained-passive-actual-derivative-a3passive-identity.md`
accepted by xhigh read-only reviewer `Mendel the 5th`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean now targets the passive nonterminal lower-left component of the actual
Frechet derivative.  The theorem
`fderiv_topologyTupleEdgeRawOrder_A3passive_apply` proves that, at a
determinant-chart point,

```text
((fderiv R topologyTupleEdgeRawOrder z) v).A3passive p = v.A3passive p.
```

The bridge theorem
`rawEdgeTupleA3_fderiv_topologyTupleEdgeRawOrder_castSucc_eq_formalRawOrderJacobianAt`
then identifies this passive lower-left readout with the matching component of
the point-specialized formal raw-order map.  This uses only the passive
`p.castSucc` case; the terminal `F3` coordinate remains determinant-bearing
and is not covered by this slice.

## 2026-06-27 A2 retained-passive actual derivative F2 shear bridge

Reproduction:
`reproduction-a2-retained-passive-actual-derivative-f2-shear-bridge.md`.
Statement card:
`statement-card-a2-retained-passive-actual-derivative-f2-shear-bridge.md`.
Independent pen-and-paper check:
xhigh read-only explorer `Lorentz the 5th`, pass on the algebra and endpoint
convention.
Implementation review:
xhigh read-only reviewer `Anscombe the 5th`, pass on endpoint/indexing,
successor-`F2` correction, formal raw-order matching, and nonclaim scope.
Review artifact:
`review-a2-retained-passive-actual-derivative-f2-shear-bridge.md`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean now proves the upper-right component bridge for the actual Frechet
derivative of `topologyTupleEdgeRawOrder`.  The theorem
`fderiv_topologyTupleEdgeRawOrder_F2_shear_apply` proves that

```text
((D raw z) v).F2 p
  + rawEdgeTupleA1 ((D raw z) v) p * coord.F2 p.castSucc
  - d(coord.F2 p.succ)(v) * coord.C p
= -(coord.solvedA1 p + coord.F2 p.succ * coord.solvedA3 p) * v.F2 p
  + coord.F2 p.succ * v.C p.
```

The successor `F2` coefficient is the full `F2full` field, so the terminal
edge is handled uniformly by the existing zero endpoint convention.  The bridge
`F2_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`
packages the same identity as agreement with the `F2` component of the
point-specialized formal raw-order map.

This is a sheared component identity.  It is not the full analytic derivative
factorization, not a determinant equality, not a measure pushforward, not
normal crossings, not pole order, and not RLCT.

## 2026-06-27 A2 retained-passive actual derivative passive A1 shear bridge

Reproduction:
`reproduction-a2-retained-passive-actual-derivative-a1passive-shear-bridge.md`.
Statement card:
`statement-card-a2-retained-passive-actual-derivative-a1passive-shear-bridge.md`.
Independent pen-and-paper check:
xhigh read-only explorer `Herschel the 5th`, pass on algebra, endpoint
convention, and passive `solvedA1` readback.
Implementation review:
xhigh read-only reviewer `Nash the 5th`, pass on indexing, terminal endpoint,
product-derivative signs/order, formal raw-order matching, and nonclaim scope.
Review artifact:
`review-a2-retained-passive-actual-derivative-a1passive-shear-bridge.md`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean now proves the passive top-left component bridge for the actual Frechet
derivative of `topologyTupleEdgeRawOrder`.  The theorem
`fderiv_topologyTupleEdgeRawOrder_A1passive_shear_apply` proves that, for
`p : Fin M`,

```text
((D raw z) v).A1passive p
  - d(coord.F2 p.succ.succ)(v) * coord.solvedA3 p.succ
  - coord.F2 p.succ.succ * d(coord.solvedA3 p.succ)(v)
= v.A1passive p.
```

The successor `F2` coefficient is the full `F2full` field, so the terminal
passive top-left edge is handled uniformly by the existing zero endpoint
convention.  The bridge
`A1passive_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`
packages the same identity as agreement with the passive `A1` component of
the point-specialized formal raw-order map.

This is a sheared passive-component identity.  It does not cover the first
top-left `Ctop` coordinate, the terminal lower-left `F3` coordinate, the full
analytic derivative factorization, determinant equality, measure pushforward,
normal crossings, pole order, or RLCT.

## 2026-06-27 A2 retained-passive actual derivative Ctop shear bridge

Reproduction:
`reproduction-a2-retained-passive-actual-derivative-ctop-shear-bridge.md`.
Statement card:
`statement-card-a2-retained-passive-actual-derivative-ctop-shear-bridge.md`.
Independent pen-and-paper check:
xhigh read-only reviewer `Einstein the 5th`, pass on algebra, endpoint slot,
tail-inverse correction, and formal target.
Implementation review:
xhigh read-only reviewer `Bohr the 5th`, pass on theorem statement, signs,
matrix order, full `F2` slot, formal bridge scope, and shortcut audit.
Review artifact:
`review-a2-retained-passive-actual-derivative-ctop-shear-bridge.md`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean now proves the first top-left `Ctop` component bridge for the actual
Frechet derivative of `topologyTupleEdgeRawOrder`.  The theorem
`fderiv_topologyTupleEdgeRawOrder_Ctop_shear_apply` proves that

```text
((D raw z) v).Ctop
  - d(coord.F2 ((0 : Fin (M+1)).succ))(v) * coord.solvedA3 0
  - coord.F2 ((0 : Fin (M+1)).succ) * d(coord.solvedA3 0)(v)
  - d(Tail^{-1})(v) * coord.Ctop
= Tail^{-1} * v.Ctop.
```

Here `Tail = retainedPassiveA1TailAfterFirst data.A1seed`.  The successor
`F2` coefficient is the full `F2full` field, so the `M = 0` boundary is the
terminal zero endpoint slot.  The bridge
`Ctop_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`
packages the same identity as agreement with the `Ctop` component of the
point-specialized formal raw-order map.

This is a sheared first-top-left component identity.  It does not cover the
terminal lower-left `F3` coordinate, the full analytic derivative
factorization, determinant equality, measure pushforward, normal crossings,
pole order, or RLCT.

## 2026-06-27 A2 retained-passive actual derivative F3 shear bridge

Reproduction:
`reproduction-a2-retained-passive-actual-derivative-f3-shear-bridge.md`.
Statement card:
`statement-card-a2-retained-passive-actual-derivative-f3-shear-bridge.md`.
Independent pen-and-paper check:
xhigh read-only reviewer `Epicurus the 5th`, pass on algebra, signs,
right-multiplication order, `M = 0`, and `LastTop` versus `Tail`.
Lean reconnaissance:
xhigh read-only scout `Godel the 5th`, pass on available APIs and target
shape.
Implementation/orientation review:
xhigh read-only explorer `Jason the 5th`, pass on proof shape, signs,
right-multiplication order, formal target, and endpoint convention.
Review artifact:
`review-a2-retained-passive-actual-derivative-f3-shear-bridge.md`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean now proves the terminal lower-left `F3` component bridge for the actual
Frechet derivative of `topologyTupleEdgeRawOrder`.  The theorem
`fderiv_topologyTupleEdgeRawOrder_F3_shear_apply` proves that

```text
((D raw z) v).F3
  - d(Early)(v) * LastTop
  + (coord.F3 - Early) * d(LastTop)(v)
= v.F3 * (-LastTop).
```

Here `Early` is the earlier lower-left retained-passive tail and `LastTop` is
the terminal one-edge residual factor.  The bridge
`F3_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`
packages the same identity as agreement with the `F3` component of the
point-specialized formal raw-order map, using
`retainedPassiveLastTopResidualFactorProduct_eq` to identify
`LastTop = coord.solvedA1 (Fin.last M)`.

This is a sheared terminal-component identity.  It completes the current
component list but still does not prove a global determinant-one shear
factorization, determinant equality, measure pushforward, density/Jacobian
theorem, normal crossings, pole order, or RLCT.

## 2026-06-27 A2 retained-passive tuple shear assembly and F2 recovery

Reproductions:
`reproduction-a2-retained-passive-actual-derivative-tuple-shear-assembly.md`
and `reproduction-a2-retained-passive-formal-f2-recovery.md`.
Statement cards:
`statement-card-a2-retained-passive-actual-derivative-tuple-shear-assembly.md`
and `statement-card-a2-retained-passive-formal-f2-recovery.md`.
Reviews:
`review-a2-retained-passive-actual-derivative-tuple-shear-assembly.md`
and `review-a2-retained-passive-formal-f2-recovery.md`, both PASS by xhigh
read-only reviewers.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean now packages the six retained-passive actual-derivative component bridges
into the tuple-valued correction
`shearedTopologyTupleEdgeRawOrderFDerivAt` and proves
`sheared_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`.
This theorem is pure component assembly by product extensionality; it does not
assert that the displayed correction is a determinant-one target-side linear
equivalence.

Lean also proves the first formal target-coordinate recovery brick,
`retainedPassiveFormalRawOrderJacobianAt_recovers_F2`.  For the formal output
`u = retainedPassiveFormalRawOrderJacobianAt z v`, it proves

```text
(coord.solvedA1 p)^-1 *
  (coord.F2 p.succ * u.C_p - u.F2_p)
= v.F2_p.
```

The proof uses the formal `(F2,C)` block formulas, the determinant-chart
invertibility theorem for `coord.solvedA1 p`, and matrix inverse cancellation.

This checkpoint changes the determinant-factorization frontier: the next
substantial target should build staged target-side shears whose coefficients
are recovered from formal target coordinates.  Reusing the six component
identities alone is insufficient for determinant equality.  Nonclaims remain:
no determinant-one shear equivalence, no actual derivative determinant
formula, no measure pushforward, no normal crossings, no pole order, and no
RLCT.

## 2026-06-27 A2 retained-passive formal C recovery

Reproduction:
`reproduction-a2-retained-passive-formal-c-recovery.md`.
Statement card:
`statement-card-a2-retained-passive-formal-c-recovery.md`.
Review:
`review-a2-retained-passive-formal-c-recovery.md`, PASS by xhigh read-only
reviewer `Huygens the 5th`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean proves `retainedPassiveFormalRawOrderJacobianAt_recovers_C`, the
companion recovery identity to
`retainedPassiveFormalRawOrderJacobianAt_recovers_F2`.  For
`u = retainedPassiveFormalRawOrderJacobianAt z v`, it proves

```text
u.C_p + coord.solvedA3 p *
  ((coord.solvedA1 p)^-1 * (coord.F2 p.succ * u.C_p - u.F2_p))
= v.C_p.
```

The theorem uses the previous formal `F2` recovery, unfolds the formal `C`
component, and cancels `-G*x + y + G*x`.  It introduces no new invertibility
beyond the determinant-chart input already used by `F2` recovery.

Nonclaims: no target-side `LinearEquiv`, determinant equality, actual
Frechet-derivative determinant formula, measure pushforward, normal crossings,
pole order, or RLCT.

## 2026-06-27 A2 edge-local `(F,C)` pair inverse equivalence

Reproduction:
`reproduction-a2-edge-local-fc-pair-inverse-equiv.md`.
Statement card:
`statement-card-a2-edge-local-fc-pair-inverse-equiv.md`.
Review:
`review-a2-edge-local-fc-pair-inverse-equiv.md`, PASS by xhigh read-only
reviewer `Halley the 5th`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean
```

Lean now proves the generic finite-linear equivalence for the edge-local
formal pair map

```text
(F,C) |-> (-(A + H*G)*F + H*C, -G*F + C)
```

under `IsUnit A.det`.  New Lean names:

```text
edgeLocalFCPairLinearMapInverse
edgeLocalFCPairLinearMapInverse_apply
edgeLocalFCPairLinearEquiv
edgeLocalFCPairLinearEquiv_apply
edgeLocalFCPairLinearEquiv_symm_apply
```

The inverse sends `(U,V)` to

```text
(A^{-1} * (H*V - U),
 V + G * (A^{-1} * (H*V - U))).
```

The first implementation had a proof-performance failure; the accepted proof
uses explicit matrix identities instead of a broad `simp`.  Focused builds for
`MatrixLinearDeterminant` and downstream
`RetainedPassiveCoordinatesJacobian` passed.

Nonclaims: this is reusable finite linear algebra only.  It is not yet the
retained-passive total target-side shear, actual derivative determinant
comparison, measure transport, normal crossings, pole order, or RLCT.

## 2026-06-27 A2 retained-passive edge-pair product equivalence

Reproduction:
`reproduction-a2-retained-passive-edge-pair-product-equiv.md`.
Statement card:
`statement-card-a2-retained-passive-edge-pair-product-equiv.md`.
Review:
`review-a2-retained-passive-edge-pair-product-equiv.md`, PASS by xhigh
read-only reviewer `Huygens`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveFormalLinearDeterminant.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveFormalRawOrder.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean now lifts the single-edge equivalence to the dependent product over all
retained-passive edge pairs:

```text
edgeLocalFCPairPiLinearEquiv
edgeLocalFCPairPiLinearEquiv_apply
edgeLocalFCPairPiLinearEquiv_symm_apply
```

and transports it through the raw-order `(F2,C)` regrouping:

```text
retainedPassiveFormalRawF2CLinearEquiv
retainedPassiveFormalRawF2CLinearEquiv_apply
retainedPassiveFormalRawF2CLinearEquiv_symm_apply
```

At a retained-passive point, the chart-specialized version is:

```text
retainedPassiveFormalRawF2CLinearEquivAt
retainedPassiveFormalRawF2CLinearEquivAt_apply_sourcePair
retainedPassiveFormalRawF2CLinearEquivAt_symm_apply
retainedPassiveFormalRawF2CLinearEquivAt_symm_recovers_sourcePair
```

The inverse is componentwise:

```text
F_p = (coord.solvedA1 p)^-1 * (coord.F2 p.succ * U_C_p - U_F2_p)
C_p = U_C_p + coord.solvedA3 p * F_p.
```

This packages the earlier `F2` and `C` recovery lemmas as a finite linear
equivalence for the formal edge-pair product.  It still excludes passive
`A1`, passive `A3`, `Ctop`, and terminal `F3`, and it does not identify the
formal map with the actual Frechet derivative.

## 2026-06-27 A2 retained-passive terminal `F2` target shear

Reproduction:
`reproduction-a2-retained-passive-terminal-f2-target-shear.md`.
Statement card:
`statement-card-a2-retained-passive-terminal-f2-target-shear.md`.
Review:
`review-a2-retained-passive-terminal-f2-target-shear.md`, PASS by xhigh
read-only reviewer `Huygens`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean now proves the terminal zero derivative lemma

```text
fderiv_retainedPassive_toCoordinateData_F2_last_apply
```

and the terminal-edge actual derivative bridge

```text
F2_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

At `p = Fin.last M`, the successor `F2` slot is the extended terminal zero,
so the general `F2` shear identity loses its `d(F2_{p+1}) * C_p` term:

```text
dY12_p + dA1_p * coord.F2 p.castSucc = formal.F2_p.
```

This is terminal-edge only.  Nonterminal edges still require staged
triangular bookkeeping; the theorem does not prove a global target-side shear,
determinant equality, measure transport, normal crossings, pole order, or
RLCT.

## 2026-06-27 A2 retained-passive terminal edge-pair target shear

Reproduction:
`reproduction-a2-retained-passive-terminal-edge-pair-target-shear.md`.
Statement card:
`statement-card-a2-retained-passive-terminal-edge-pair-target-shear.md`.
Review:
`review-a2-retained-passive-terminal-edge-pair-target-shear.md`, PASS by
xhigh read-only scouts `Mendel` and `Ramanujan`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean now packages the terminal actual target-side normalized `(F2,C)` pair and
recovers the source terminal edge pair from it.  New Lean names:

```text
F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F2
F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_recovers_C
```

For `p = Fin.last M` and `Dzv = d(topologyTupleEdgeRawOrder)_z(v)`, set

```text
U_F = Dzv.F2_p + rawEdgeTupleA1(Dzv)_p * coord.F2 p.castSucc,
U_C = Dzv.C_p  + rawEdgeTupleA3(Dzv)_p * coord.F2 p.castSucc.
```

The first theorem proves `(U_F,U_C)` equals the corresponding formal raw-order
output pair.  The next two theorems substitute this equality into the
previously landed formal inverse formulas to recover `v.F2_p` and `v.C_p`.

Endpoint guardrail: `p.castSucc` is the stored source-side `F2` slot in the
target shear, while `p.succ` is the terminal zero slot in the formal inverse.
For `M = 0`, `LastTop = coord.Ctop` remains separate from this edge-pair
package.

This is still terminal-edge only.  It does not prove the nonterminal staged
target-side construction, a determinant-one target-side linear equivalence,
actual derivative determinant equality, measure transport, normal crossings,
pole order, or RLCT.

## 2026-06-27 A2 retained-passive nonterminal edge-pair staged target shear

Reproduction:
`reproduction-a2-retained-passive-nonterminal-edge-pair-staged-target-shear.md`.
Statement card:
`statement-card-a2-retained-passive-nonterminal-edge-pair-staged-target-shear.md`.
Review:
`review-a2-retained-passive-nonterminal-edge-pair-staged-target-shear.md`.
First xhigh read-only review failed on a derivative/source-staging mismatch;
Lean was fixed with a projection derivative lemma; post-repair xhigh re-review
passed.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean now proves the one-step nonterminal source-staged package:

```text
fderiv_retainedPassive_toCoordinateData_F2_nonterminal_succ_apply
F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F2
F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_C
```

For `p : Fin M` and `q = p.castSucc`, the normalized target pair is

```text
U_F = Dzv.F2_q + rawEdgeTupleA1(Dzv)_q * coord.F2 q.castSucc
      - Xsucc * coord.C q,
U_C = Dzv.C_q  + rawEdgeTupleA3(Dzv)_q * coord.F2 q.castSucc,
```

where `Xsucc` is the source tangent `v.F2_(p.succ)` transported along
`Fin.succ_castSucc p`; the projection lemma identifies it with the actual
derivative of the successor extended `F2` slot.  With that staged input,
`(U_F,U_C)` equals the formal edge pair, and the formal inverse recovers
`v.F2_q` and `v.C_q`.

This is not the descending induction over all edges.  It does not prove a
target-side `LinearEquiv`, determinant equality, measure transport, normal
crossings, pole order, or RLCT.

## 2026-06-28 A2 retained-passive source-edge-family pre-measure inputs

Reproduction:
`reproduction-a2-retained-passive-source-edge-family-premeasure-inputs.md`.
Statement card:
`statement-card-a2-retained-passive-source-edge-family-premeasure-inputs.md`.
Review:
`review-a2-retained-passive-source-edge-family-premeasure-inputs.md`, PASS by
xhigh read-only reviewer `Linnaeus`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_sourceEdgeFamilyOfData
```

For retained-passive coordinate data `retainedData y`, the canonical source
edge-family map

```text
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
  W B U₀ hU₀ (retainedData y)
```

supplies the fixed-base local-source membership and source-readback
selected-entry residual-factor matrix inputs.  The separate realization
hypothesis from the generic bridge is discharged by
`paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq`.

This is fixed-base source-family plumbing only.  It does not transport
`edgeMatrix` or `sourceReadback`, prove fixed-base realization for transported
explicit Case 2 data, compare source priors or Jacobians, prove normal
crossings, pole order, or RLCT.

## 2026-06-28 A2 Case 2 endpoint-transport source-edge-family pre-measure inputs

Reproduction:
`reproduction-a2-case2-endpoint-transport-source-edge-family-premeasure-inputs.md`.
Statement card:
`statement-card-a2-case2-endpoint-transport-source-edge-family-premeasure-inputs.md`.
Review:
`review-a2-case2-endpoint-transport-source-edge-family-premeasure-inputs.md`,
PASS by xhigh read-only reviewer `Mill`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData
```

Given supplied endpoint equivalences from the displayed Case 2 two-edge
endpoint family to the fixed-base retained-passive endpoint family, the theorem
builds the fixed-base source chart from the endpoint-transported explicit Case
2 retained-passive datum.  It returns local-source membership and the
source-readback selected-entry residual-factor matrix identity.

The theorem lives in the Case 2 leaf bridge, not in the generic
`RetainedPassiveLocalMeasure.lean`, so the generic source-family bridge remains
Case2-free.  It still does not construct the endpoint equivalences, prove
standalone endpoint transport of `edgeMatrix` or `sourceReadback`, compare
source priors or Jacobians, prove positivity/integrability, normal crossings,
pole order, or RLCT.

## 2026-06-28 A2 Case 2 endpoint-transport source-edge-family residual square-sum

Reproduction:
`reproduction-a2-case2-endpoint-transport-source-edge-family-residual-square-sum.md`.
Statement card:
`statement-card-a2-case2-endpoint-transport-source-edge-family-residual-square-sum.md`.
Review:
`review-a2-case2-endpoint-transport-source-edge-family-residual-square-sum.md`,
PASS by xhigh read-only reviewer `Einstein`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_case2EndpointTransport_sourceEdgeFamilyOfData
```

For the source chart built from the endpoint-transported explicit Case 2
retained-passive datum, the fixed-base residual-block coordinate square-sum is
the successor selected-entry center residual.  The proof composes the
endpoint-transport source-family pre-measure wrapper with the generic
source-readback-to-residual-square-sum bridge.

This is still finite residual readout plumbing.  It does not construct endpoint
equivalences, prove source-chart measurability, compare source priors or
Jacobians, prove positivity/integrability, normal crossings, pole order, or
RLCT.

## 2026-06-28 A2 Case 2 endpoint-transport factor alignment

Reproduction:
`reproduction-a2-case2-endpoint-transport-factor-alignment.md`.
Statement card:
`statement-card-a2-case2-endpoint-transport-factor-alignment.md`.
Review:
`review-a2-case2-endpoint-transport-factor-alignment.md`, PASS by xhigh
read-only checker `Epicurus`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
```

Lean now proves:

```text
matrix_submatrix_equiv_symm_submatrix_equiv
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_C_one_submatrix_eq_displayedPostPivotResidualBlock
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_C_zero_submatrix_eq_displayedPostPivotFreeFollowingFactor
exists_pivot_residualFactorProduct_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_eq_selectedEntryCenter_matrix_of_ne_zero
```

For the endpoint-transported explicit Case 2 selected-entry retained-passive
datum, the stored `C 1` factor becomes Aoyagi's displayed post-pivot residual
block after submatrixing by the forward endpoint equivalences `e 2` and `e 1`.
The stored `C 0` factor becomes the displayed free following factor after
submatrixing by `e 1` and `e 0`.  The product order is `C 1 * C 0`.

The new all-pivot consumer applies the existing finite selected-entry residual
product theorem to this explicit transported datum without supplied `hD` and
`hF`.  It still assumes nonzeroness of the displayed two-edge product.

This is finite factor alignment only.  It does not prove product nonzeroness,
fixed-pivot nonzeroness, arbitrary `ofTopologyTuple` factor alignment,
fixed-base source-readback provenance, source-prior transport, Jacobian
comparison, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 Case 2 endpoint-transport pivot nonzero consumer

Reproduction:
`reproduction-a2-case2-endpoint-transport-pivot-nonzero-consumer.md`.
Statement card:
`statement-card-a2-case2-endpoint-transport-pivot-nonzero-consumer.md`.
Review:
`review-a2-case2-endpoint-transport-pivot-nonzero-consumer.md`, PASS by
xhigh read-only checkers `Raman` and `Ohm`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
```

Lean now proves:

```text
exists_pivot_residualFactorProduct_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_eq_selectedEntryCenter_matrix_of_yNext_pivot_ne_zero
```

For the endpoint-transported explicit Case 2 selected-entry retained-passive
datum, the all-pivot selected-entry residual-product readout follows from the
successor pivot-coordinate nonzero hypothesis `hyNext`.  The displayed-product
nonzero input is discharged by the successor-source product equality and the
successor selected-entry matrix nonzero lemma.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge` and
downstream focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.
`scripts/sorries`, `git diff --check`, touched Lean-file forbidden-marker
search, and direct axiom probe passed; the theorem reports only
`[propext, Classical.choice, Quot.sound]`.

This is constructed finite Case 2 nonzeroness only.  The all-pivot conclusion
produces some pivot and coordinates; it does not identify them with
`(J + 2, J + 2)` or the supplied `yNext`.  It also does not prove arbitrary
`ofTopologyTuple` factor alignment, fixed-base source-readback provenance,
source-prior transport, Jacobian comparison, normal crossings, pole order, or
RLCT.

## 2026-06-28 A2 Case 2 source-readback factor provenance

Reproduction:
`reproduction-a2-case2-source-readback-factor-provenance.md`.
Statement card:
`statement-card-a2-case2-source-readback-factor-provenance.md`.
Review:
`review-a2-case2-source-readback-factor-provenance.md`, PASS by xhigh
read-only checker `Bacon`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.sourceReadback_eq_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_of_case2EndpointTransport_sourceEdgeFamilyOfData
PaperEndpointFixedBaseRegularCoordinateSourceData.sourceReadback_C_one_submatrix_eq_displayedPostPivotResidualBlock_of_case2EndpointTransport_sourceEdgeFamilyOfData
PaperEndpointFixedBaseRegularCoordinateSourceData.sourceReadback_C_zero_submatrix_eq_displayedPostPivotFreeFollowingFactor_of_case2EndpointTransport_sourceEdgeFamilyOfData
```

The fixed-base source readback of the source edge family built from the
endpoint-transported explicit Case 2 datum is that transported datum itself.
Consequently the readback's `C 1` and `C 0` factors recover the displayed
post-pivot residual block and free following factor after forward endpoint
reindexing.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.
`scripts/sorries`, `git diff --check`, touched Lean-file forbidden-marker
search, and direct axiom probes passed; the new declarations report only
`[propext, Classical.choice, Quot.sound]`.

This is fixed-base source-readback factor provenance for the constructed
endpoint-transported datum.  It does not construct `tau`, prove `hTau`, give
label-preserving endpoint provenance, identify arbitrary `ofTopologyTuple`
data, transport source priors, compare Jacobians, prove normal crossings,
compute pole order, or extract RLCT.

## 2026-06-28 A2 Case 2 topology-tuple source-family alignment

Reproduction:
`reproduction-a2-case2-topology-tuple-source-family-alignment.md`.
Statement card:
`statement-card-a2-case2-topology-tuple-source-family-alignment.md`.
Review:
`review-a2-case2-topology-tuple-source-family-alignment.md`, PASS by xhigh
read-only checker `Helmholtz`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Lean now proves:

```text
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_topologyTuple_eq_sourceEdgeFamilyOfData
PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_topologyTuple_eq_case2EndpointTransport_sourceEdgeFamilyOfData
```

For any retained-passive determinant-chart datum, the raw-order p.13 source
chart evaluated at `topologyTupleEdgeRawOrder (topologyTuple data)` is the
direct fixed-base p.13 source edge family of `data`.  The proof composes the
existing raw-order source-chart identity with `ofTopologyTuple_topologyTuple`.

For the endpoint-transported explicit Case 2 selected-entry datum, the
determinant-chart input is discharged by
`case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart`.
This removes the concrete `ofTopologyTuple`/direct-datum mismatch on the
raw-order p.13 source path.

Focused builds of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalSource` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed via
the worktree-local `scripts/lb` command.  `scripts/sorries`, `git diff
--check`, touched Lean-file forbidden-marker search, and direct axiom probes
passed; both declarations report only `[propext, Classical.choice,
Quot.sound]`.

This is source-family presentation only.  It is not endpoint provenance,
endpoint canonicity, source-image equality, pushforward-measure transport,
source-rank coverage, source-prior transport, Jacobian comparison, normal
crossings, pole order, or RLCT.

## 2026-06-28 A2 Case 2 chart-produced density continuous-at finite integral

Reproduction:
`reproduction-a2-case2-chart-produced-density-continuousat-finite-integral.md`.
Statement card:
`statement-card-a2-case2-chart-produced-density-continuousat-finite-integral.md`.
Review:
`review-a2-case2-chart-produced-density-continuousat-finite-integral.md`, PASS
with corrections by xhigh read-only checker `Bohr`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_continuousAt_pos_density
```

For the endpoint-transported explicit Case 2 selected-entry chart-produced
measure, positive continuity of the transported density at `(base,0)` supplies
local nonnegativity and boundedness of the density after shrinking the
regular-coordinate radius.  The theorem removes supplied `Rreg`, `Creg`,
`0 <= Creg`, eventual density nonnegativity, and eventual density boundedness
as inputs.  It returns `R`, `C`, and `U` with `0 < R`, `R <= Rmax`, `0 <= C`,
`IsOpen U`, `base ∈ U`, and the finite-integral conclusion over `ball 0 R`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed via the
worktree-local `scripts/lb` command.  `scripts/sorries`, `git diff --check`,
touched Lean-file forbidden-marker search, and direct axiom probe passed; the
declaration reports only `[propext, Classical.choice, Quot.sound]`.

This is still a chart-produced source-measure theorem.  It does not construct
endpoint equivalences, prove endpoint provenance, identify an original prior or
external source measure, compare Jacobians for such a prior, prove source-rank
coverage, prove normal crossings, compute pole order, or extract RLCT.

## 2026-06-28 A2 Case 2 chart-produced determinant residual support wrapper

Reproduction:
`reproduction-a2-case2-det-chart-selected-entry-chart-produced-residual.md`.
Statement card:
`statement-card-a2-case2-det-chart-selected-entry-chart-produced-residual.md`.
Review:
`review-a2-case2-det-chart-selected-entry-chart-produced-residual.md`, PASS by
xhigh read-only checker `Volta`.

## 2026-06-29 A2 retained-passive small-box chart-produced residual bound

Reproduction:
`reproduction-a2-retained-passive-small-box-chart-produced-residual-bound.md`.
Statement card:
`statement-card-a2-retained-passive-small-box-chart-produced-residual-bound.md`.
Review:
`review-a2-retained-passive-small-box-chart-produced-residual-bound.md`,
PASS by xhigh `Carson the 2nd`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Lean now proves three fixed-radius residual boundedness handoffs:

```text
residualSquareSum_le_sq_ae_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_of_residual_eq_of_smallBox
residualSquareSum_le_sq_ae_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceEdgeFamilyOfData_chartProducedMeasure_of_smallBox
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure_of_smallBox
```

The generic theorem pushes the selected-entry weighted signed-box residual
upper bound through a supplied source chart and residual readout.  The
retained-passive source-edge-family theorem derives the chart landing and
readout from retained-data fields.  The final theorem feeds this bound to the
existing source-stratum two-sided handoff, replacing the explicit residual
boundedness premise by small-box hypotheses at the same `Rreg`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure` passed via `scripts/lb`.
`scripts/sorries` reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`; `git diff --check` passed.  Axiom audits for all three new theorem
names reported only `[propext, Classical.choice, Quot.sound]`.

Nonclaims: no choice of signed-box radii or `delta`, no transfer from `Rmax`
to a smaller produced radius, no source-rank coverage, no source/image
equality, no external source-prior or Jacobian transport, no normal crossings,
pole order, or RLCT.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_selectedEntrySignedBox_chartProducedMeasure
```

For the endpoint-transported explicit Case 2 selected-entry retained-passive
chart, the selected-entry weighted signed-box pushforward measure is supported
on `topologyTupleDetChartSet`.  The proof obtains pointwise determinant-chart
membership from the endpoint-transported Case 2 datum, converts it through
`topologyTuple`, proves the pushed-forward measure restricts to itself on the
determinant chart, and then applies the existing supplied-map residual theorem.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed via the
worktree-local `scripts/lb` command.  `scripts/sorries`, `git diff --check`,
touched Lean-file forbidden-marker search, and direct axiom probe passed; the
new declaration reports only `[propext, Classical.choice, Quot.sound]`.

This is a chart-produced determinant-measure theorem only.  It does not remove
the supplied-map hypothesis from the arbitrary-measure theorem, identify Haar
measure or an external source prior, prove full determinant-chart coverage,
source-rank coverage, normal crossings, pole order, or RLCT.

## 2026-06-28 A2 Case 2 inverse-Jacobian continuous-density finite-integral wrapper

Reproduction:
`reproduction-a2-case2-inverse-jacobian-density-continuousat-finite-integral.md`.
Statement card:
`statement-card-a2-case2-inverse-jacobian-density-continuousat-finite-integral.md`.
Review:
`review-a2-case2-inverse-jacobian-density-continuousat-finite-integral.md`,
PASS by xhigh read-only checker `Darwin`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_case2EndpointTransport_selectedEntrySignedBox_map_continuousAt_pos_density
```

For the endpoint-transported Case 2 raw-order inverse-Jacobian source measure,
positive continuity of the supplied integrand density at `(base,0)` supplies
local density nonnegativity and boundedness after shrinking the regular-
coordinate radius.  The theorem returns `R`, `C`, and `U` with `0 < R`,
`R <= Rmax`, `0 <= C`, `IsOpen U`, and `base ∈ U`, plus the finite-integral
conclusion over
`Measure.map rawChart ((m.restrict T).withDensity invJacDensity)`.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed via the
worktree-local `scripts/lb` command.  `scripts/sorries`, `git diff --check`,
touched Lean-file forbidden-marker search, and direct axiom probe passed; the
new declaration reports only `[propext, Classical.choice, Quot.sound]`.

The determinant-chart pushforward identity, selected-entry residual radii and
critical exponent inequality, and local loss lower bound remain explicit.  This
does not identify Haar measure or an external source prior, prove chart
coverage, prove source-rank coverage, construct normal crossings, compute pole
order, or extract RLCT.

## 2026-06-28 A2 generic selected-entry chart-produced determinant residual

Reproduction:
`reproduction-a2-retained-passive-selected-entry-chart-produced-det-residual.md`.
Statement card:
`statement-card-a2-retained-passive-selected-entry-chart-produced-det-residual.md`.
Review:
`review-a2-retained-passive-selected-entry-chart-produced-det-residual.md`,
PASS by xhigh read-only checker `Arendt`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_selectedEntrySignedBox_chartProducedMeasure
```

For any selected-entry chart-produced measure supported on the retained-passive
determinant chart, the generic theorem proves determinant-chart residual
positivity and finite negative-power residual integral from direct residual
positive-set measurability and the selected-entry residual readout.  It proves
the restriction identity for `Measure.map chart weightedBox` using
`withDensity_absolutelyContinuous`, `ae_map_iff`, and
`Measure.restrict_eq_self_of_ae_mem`, then calls the supplied-map theorem.

The Case 2 chart-produced determinant residual theorem now uses this generic
front end instead of duplicating the support/restriction proof.

Focused builds of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed via the
worktree-local `scripts/lb` command.  `scripts/sorries`, `git diff --check`,
touched Lean-file forbidden-marker search, and direct axiom probes passed; the
new generic declaration and the refactored Case 2 declaration report only
`[propext, Classical.choice, Quot.sound]`.

This is chart-produced support infrastructure only.  It is not an arbitrary-
measure theorem, Haar/source-prior transport, full determinant-chart coverage,
source-rank coverage, normal crossings, pole order, or RLCT.

## 2026-06-29 Lean A2 retained-passive F3 target-staged shear

Reproduction:
`reproduction-a2-retained-passive-f3-target-staged-shear.md`.
Statement card:
`statement-card-a2-retained-passive-f3-target-staged-shear.md`.
Review:
`review-a2-retained-passive-f3-target-staged-shear.md`
passed by xhigh `Bernoulli`.

Lean now proves:

```text
fderiv_topologyTupleEdgeRawOrder_F3_targetStaged_shear_apply
```

This is the positive-tail terminal `F3` shear with the earlier-tail derivative
substituted by
`retainedPassiveLowerLeftProductTailTargetStagedFDerivAt`.  It consumes the
already-proved `fderiv_topologyTupleEdgeRawOrder_F3_shear_apply` at `M+1` and
`fderiv_retainedPassiveLowerLeftProductTailSum_targetStaged_apply` at `M`,
leaving the terminal top-factor correction explicit.

Nonclaims: no full derivative/formal-Jacobian equality, no determinant
equality, no target-side linear equivalence, no measure transport, no normal
crossings, no pole order, and no RLCT.

## 2026-06-29 A2 Case 2 cardinality endpoint finite-integral handoff

Reproduction:
`reproduction-a2-case2-cardinality-endpoint-finite-integral.md`.
Statement card:
`statement-card-a2-case2-cardinality-endpoint-finite-integral.md`.
Review:
`review-a2-case2-cardinality-endpoint-finite-integral.md`
passed by xhigh read-only checker `Newton the 2nd`.

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_continuousAt_pos_density_card_eq
```

This is the endpoint-cardinality version of the endpoint-transported explicit
Case 2 chart-produced finite-integral handoff for positive continuous density.
It consumes cardinality hypotheses `hNext` and `hEndpoints`, constructs the
noncanonical finite endpoint equivalences via
`case2EndpointTransportEquivs_of_card_eq`, and applies the already-proved
endpoint-equivalence theorem.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`, full
`DLNFibre` build, `scripts/sorries`, `git diff --check`, and direct theorem
axiom audit passed; the new theorem reports only `[propext,
Classical.choice, Quot.sound]`.

Nonclaims: no proof of the cardinality equalities, no label-preserving
endpoint transport, no source-rank coverage, no original prior/source measure
identification, no external-prior Jacobian comparison, no normal crossings, no
pole order, and no RLCT.

## 2026-06-29 branch integration note - dev dimension-stack merge

The Aoyagi expedition branch was updated to include the current `origin/dev`
dimension-stack merge (`00fb7238`, PR #14).  Integration was probed first in
`.claude/worktrees/aoyagi-rlct-dimprobe` on
`probe/aoyagi-rlct-dimstack`; the merge was clean, including the auto-merge of
`lean/DLNFibre.lean`.

Probe gates passed:

```text
cd lean
scripts/lb DLNFibre
scripts/sorries
git diff --check HEAD^ HEAD
direct #print axioms probe for the latest passive source-stratum theorem
```

The actual branch `expedition/aoyagi-rlct` was then fast-forwarded to the
tested merge commit `7459252a`.  The same actual-worktree gates passed:
full `DLNFibre` build, zero-sorry scan, merge-diff whitespace check, and the
direct axiom probe for
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass_sourceStratum_bounds`,
which reported only `[propext, Classical.choice, Quot.sound]`.

This note changes no mathematical claim.  The active A2 frontier remains the
p.13 retained-passive source-chart/source-prior transport and
regular-square-suspension line, with pen-and-paper reproduction required before
substantial Lean.

## 2026-06-30 A2 Case 2 passive theta Jacobian-dominated source

Reproduction:
`reproduction-a2-case2-passive-theta-jacobian-dominated-source.md`.
Statement card:
`statement-card-a2-case2-passive-theta-jacobian-dominated-source.md`.
Review:
`review-a2-case2-passive-theta-jacobian-dominated-source.md`, PASS by xhigh
source/scope reviewer `Darwin` and xhigh Lean/API reviewer `McClintock`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
```

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_restrict_le_smul_globalWithDensity_jacobian_passiveProductMeasure_finiteMass
```

For an arbitrary concrete `Case2PassiveTheta` candidate source measure, the
theorem returns an open neighborhood `W` of the passive determinant-sector base
point.  The chart-produced measure

```text
mu = Measure.map sourceChart (candidateMeasure.restrict W)
```

is supported on the retained-passive p.13 local source.  If, for a finite
scalar `c`, the restricted candidate measure is dominated by

```text
c * (passiveSource.withDensity jacobianDensity).restrict W,
```

then the theorem also proves a.e. residual square-sum positivity and
`residualNegPowerIntegrableOn localSource mu t`.

The proof first obtains an open Jacobian-unit neighborhood `U`, applies the
existing passive-product local-domination residual-source socket to
`candidateMeasure.restrict U`, and then takes `W = U inter V`.  Repeated
restriction and `restrict_withDensity` identify the local hypotheses, and the
upper Jacobian sandwich converts domination by the weighted measure to finite
domination by `passiveSource`.

Nonclaims: no original source-prior construction, determinant-chart Haar
transport, raw-order Haar transport, exact passive-sector pushforward,
source-image equality, source-rank coverage, normal crossings, pole order, or
RLCT extraction.

## 2026-06-30 A2 Case 2 passive theta sector-image support

Reproduction:
`reproduction-a2-case2-passive-theta-sector-image-support.md`.
Statement card:
`statement-card-a2-case2-passive-theta-sector-image-support.md`.
Review:
`review-a2-case2-passive-theta-sector-image-support.md`, PASS by xhigh
source/scope reviewer `Nietzsche` and xhigh Lean/API reviewer `Beauvoir`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSector.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

Lean now names:

```text
case2PassiveThetaSectorSet
case2PassiveThetaEndpointSectorSet
```

and proves:

```text
measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_endpointSectorSet_eq_self
```

For the endpoint topology-tuple map `Y`, the named sector
`case2PassiveThetaEndpointSectorSet Omega = Y '' Omega`, and
`nu = Measure.map Y (thetaMeasure.restrict Omega)`, the theorem proves
`nu.restrict sectorSet = nu` under explicit measurability hypotheses on
`Omega`, `sectorSet`, and `Y`.

This is support bookkeeping for the full passive theta sector image.  It is
not exact passive-sector Haar transport, determinant-chart Haar transport,
raw-order Haar transport, source-prior comparison, finite-scalar domination,
bounded-density comparison, source-image equality, source-rank coverage,
normal crossings, pole order, or RLCT extraction.

## 2026-06-30 A2 Case 2 passive theta endpoint-sector domination

Reproduction:
`reproduction-a2-case2-passive-theta-endpoint-sector-domination.md`.
Statement card:
`statement-card-a2-case2-passive-theta-endpoint-sector-domination.md`.
Review:
`review-a2-case2-passive-theta-endpoint-sector-domination.md`, PASS as a
conditional domination transfer by xhigh source/scope reviewer `Lorentz` and
xhigh Lean/API reviewer `Carver`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

Lean now proves:

```text
measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_endpointSectorSet_le_smul
measure_map_case2PassiveThetaEndpointTopologyTuple_withDensity_restrict_endpointSectorSet_le_smul_of_ae_le
```

The first theorem transports an explicit theta-domain domination to
endpoint-sector pushforwards restricted to the named sector image.  The second
theorem derives the theta-domain domination from a local a.e. upper bound on
a `withDensity` density.

This is not exact passive-sector Haar transport, determinant-chart Haar
transport, raw-order Haar transport, source-prior comparison,
source-image equality, source-rank coverage, normal crossings, pole order, or
RLCT extraction.  The next frontier is to prove the actual local
theta-domain domination or bounded-density hypothesis from a
passive-sector/reference measure model.

## 2026-06-30 A2 Case 2 passive theta Jacobian endpoint-sector domination

Reproduction:
`reproduction-a2-case2-passive-theta-jacobian-endpoint-sector-domination.md`.
Statement card:
`statement-card-a2-case2-passive-theta-jacobian-endpoint-sector-domination.md`.
Review:
`review-a2-case2-passive-theta-jacobian-endpoint-sector-domination.md`, PASS
by xhigh source/scope reviewer `Hegel` and xhigh Lean/API reviewer
`Epicurus`.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
```

Lean now proves:

```text
exists_pos_open_measure_map_case2PassiveThetaEndpointTopologyTuple_withDensity_jacobian_restrict_endpointSectorSet_le_smul_passiveProductMeasure
```

This theorem applies the upper side of the concrete passive theta Jacobian
sandwich to the endpoint-sector domination transfer.  It returns a positive
scalar `K` and an open neighborhood `U` such that the endpoint pushforward of
the Jacobian-weighted passive-product theta measure is dominated by
`ofReal K` times the endpoint pushforward of the unweighted passive-product
theta measure, both restricted to the named endpoint sector image.

Nonclaims: no exact passive-sector Haar transport, determinant-chart Haar
transport, raw-order Haar transport, source-prior comparison,
source-image equality, source-rank coverage, normal crossings, pole order, or
RLCT extraction.

## 2026-06-30 A2 source-image external density automatic readback

Reproduction:
`reproduction-a2-source-image-external-density-automatic-readback.md`.
Statement card:
`statement-card-a2-source-image-external-density-automatic-readback.md`.
Review:
`review-a2-source-image-external-density-automatic-readback.md`, PASS after
focused Lean elaboration.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Lean now proves:

```text
measure_map_readback_restrict_image_le_smul_of_restrict_eq_withDensity_of_continuousOn_injOn
```

This is the generic external-measure equality version of the bounded-density
source-image pullback theorem.  Given a continuous injective local chart and a
pointwise left inverse, Lean derives readback a.e. measurability for the
chart-produced source-image reference and then pulls back any restricted
external measure that is explicitly equal to a bounded-density perturbation of
that reference.

The coordinate domain is generic.  It can later be instantiated with full
p.13 product coordinates `(theta,u)` once the actual source chart/readback and
source-prior density identity are available.

Nonclaims: no original/source prior transport, no source-rank coverage, no
Haar transport, no Jacobian formula, no normal crossings, no pole order, and
no RLCT extraction.

## 2026-06-30 A2 Case 2 product source-chart regular/residual readout

Reproduction:
`reproduction-a2-case2-product-source-chart-regular-residual-readout.md`.
Statement card:
`statement-card-a2-case2-product-source-chart-regular-residual-readout.md`.
Review:
`review-a2-case2-product-source-chart-regular-residual-readout.md`, PASS after
focused and full Lean verification.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Lean now proves:

```text
case2PassiveThetaEndpointProductSourceChart_regular_residualBlockCoordinateMap_eq
```

This is the concrete Case 2 specialization of the generic p.13
source-dependent product-coordinate readout.  For the full product chart
constructed from `case2PassiveThetaEndpointSourceChart`, the regular
coordinate map reads out the supplied Euclidean vector `u`, while the residual
coordinate map agrees with the base passive-theta source chart at `theta`.

The theorem keeps the `ctopMatrix u` unit-determinant hypothesis explicit and
does not assert a full inverse from source edge families to `(theta,u)`.

Verification passed:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_product_readout_axioms.lean
```

Nonclaims: no full inverse/readback to `(theta,u)`, no original/source-prior
transport, no source-rank coverage, no Haar transport, no Jacobian formula, no
normal crossings, no pole order, and no RLCT extraction.

## 2026-06-30 A2 Case 2 product source-chart small-ball readout

Reproduction:
`reproduction-a2-case2-product-source-chart-small-ball-readout.md`.
Statement card:
`statement-card-a2-case2-product-source-chart-small-ball-readout.md`.
Review:
`review-a2-case2-product-source-chart-small-ball-readout.md`, PASS after
focused and full Lean verification.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Lean now proves:

```text
exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_regular_residualBlockCoordinateMap_eq_nhdsWithin_source
```

This packages the pointwise `ctopMatrix u` unit-determinant hypothesis for the
full Case 2 product source chart into a positive Euclidean radius.  For all
regular variables `u` in the returned ball and eventually along the base
source-rank stratum, the product chart reads out regular coordinates as `u`
and residual coordinates as the passive-theta source residual coordinates.

Verification passed:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_product_small_ball_axioms.lean
```

Nonclaims: no full inverse/readback to `(theta,u)`, no source-image coverage,
no original/source-prior transport, no Haar transport, no Jacobian formula, no
normal crossings, no pole order, and no RLCT extraction.

## 2026-06-30 A2 chart-piece readback-domination handoff

Reproduction:
`reproduction-a2-chart-piece-readback-domination-handoff.md`.
Statement card:
`statement-card-a2-chart-piece-readback-domination-handoff.md`.
Review:
`review-a2-chart-piece-readback-domination-handoff.md`, PASS by xhigh
`Schrodinger the 2nd`.

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge.lean
```

Lean now proves:

```text
measure_le_smul_restrict_of_le_smul_of_restrict_eq_self
restrict_restrict_eq_self_of_subset
restrict_le_smul_restrict_of_le_smul_of_subset

measure_restrict_piece_le_smul_map_restrict_of_map_readback_restrict_piece_le_smul

exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_externalSourceMeasure_restrict_chartPiece_map_readback_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

The new Aoyagi theorem keeps the caller-supplied readback domination explicit:

```text
Measure.map readback (externalSourceMeasure.restrict chartPiece)
  <= Cpull * coordinateSourceMeasure.restrict W
```

where `coordinateSourceMeasure = baseJ.withDensity
(fun z => sourceImageDensity (sourceChart z))`.  A pointwise right-inverse
hypothesis on `chartPiece`, `chartPiece subset sourceLocal`, and
`Cpull < infinity` give finite loss-power integrability over
`(externalSourceMeasure.restrict chartPiece).prod nu`.

Verification passed so far:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_chart_piece_readback_domination_axioms.lean
```

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.

Nonclaims: no original/source-prior transport, no chart-image equality, no
source-rank coverage, no Haar/Jacobian transport, no normal crossings, no pole
order, and no RLCT extraction.

## 2026-07-01 Case 2 passive-theta endpoint reference

Lean now names the concrete passive-theta reference source and proves its
determinant-chart support after determinant-sector localization:

```text
matrixEntryReferenceMeasure
case2PassiveThetaPassiveFieldReferenceMeasure
case2PassiveThetaCenterSignedBoxMeasure
case2PassiveThetaCenterWeightedBoxMeasure
case2PassiveThetaReferenceSourceMeasure
case2PassiveThetaEndpointReferenceImageMeasure

measure_map_case2PassiveThetaEndpointTopologyTuple_referenceSource_restrict_detChartSet_eq_self_of_subset_detSector
case2PassiveThetaEndpointReferenceImageMeasure_restrict_detChartSet_eq_self_of_subset_detSector
measure_map_case2PassiveThetaEndpointTopologyTuple_passiveSource_restrict_le_smul_endpointReferenceImage_of_passiveMeasure_le_smul_reference
```

Artifacts:

```text
reproduction-a2-case2-passive-theta-endpoint-reference.md
statement-card-a2-case2-passive-theta-endpoint-reference.md
review-a2-case2-passive-theta-endpoint-reference.md
```

Verification passed:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaEndpointReference.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaEndpointReference
env LEAN_NUM_THREADS=3 lake build DLNFibre
lean/scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_endpoint_reference_axioms.lean
```

The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.  Xhigh scouts confirmed the
coordinate boundary; unrestricted full determinant-chart Haar domination is
obstructed for this theta domain because the endpoint image fixes the full
`C` family through selected-entry residual data.

Nonclaims: no endpoint determinant-chart Haar domination, no Jacobian formula
for `Y`, no exact Haar transport, no raw-Haar pushforward, no Haar
normalization, no original source-prior transport, no source-image/source-rank
coverage, no normal crossings, no pole order, and no RLCT extraction.

## 2026-07-01 Case 2 passive-theta raw-order reference image

Lean now names the actual raw-order image of the concrete passive-theta
reference source:

```text
case2PassiveThetaRawOrderReferenceImageMeasure
```

and proves:

```text
exists_open_subset_case2PassiveThetaRawOrderReferenceImageMeasure_support_and_domination
```

On the local determinant/punctured-sector shrink from the existing
raw-order/source-chart package, this image measure is supported on
`topologyTupleRawOrderSourceRecursiveDetChartSet`.  The same theorem pushes
passive-field scalar domination through the raw map to domination by this named
raw-order image measure.

Artifacts:

```text
reproduction-a2-case2-passive-theta-raw-order-reference.md
statement-card-a2-case2-passive-theta-raw-order-reference.md
review-a2-case2-passive-theta-raw-order-reference.md
```

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probe passed.  The
direct axiom probe reported only `[propext, Classical.choice, Quot.sound]`.

Nonclaims: no raw-Haar identification, no determinant-chart Haar domination,
no source-prior/original-volume transport, no source-image/source-rank
coverage, no normal crossings, no pole order, and no RLCT extraction.

## 2026-07-01 Case 2 endpoint-reference raw-order/source-chart handoff

Lean now proves:

```text
exists_open_subset_case2PassiveThetaEndpointReferenceImage_rawOrder_sourceChart_handoff
```

On the local determinant/punctured-sector shrink, the endpoint reference image
maps by `topologyTupleEdgeRawOrder` to the named raw-order reference image, and
the p.13 raw-order source chart maps that raw-order image to the direct
source-chart image of the theta-domain reference source.

Artifacts:

```text
reproduction-a2-case2-endpoint-reference-raw-order-source-chart-handoff.md
statement-card-a2-case2-endpoint-reference-raw-order-source-chart-handoff.md
review-a2-case2-endpoint-reference-raw-order-source-chart-handoff.md
```

Focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probe passed.
The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no raw-Haar identification, no determinant-chart Haar domination,
no original/source-prior transport, no source-image/source-rank coverage, no
normal crossings, no pole order, and no RLCT extraction.

## 2026-07-01 Case 2 raw-order reference density transport

Lean now proves:

```text
exists_open_subset_case2PassiveThetaRawOrderReferenceImage_withDensity_sourceChart_handoff
```

This specializes the existing raw-density transport bridge to the named
raw-order reference image.  A raw density a.e. measurable for that image
measure transports through the p.13 raw-order source chart to the direct
source-chart image of the theta-domain reference source with composed density.

Artifacts:

```text
reproduction-a2-case2-raw-order-reference-density-transport.md
statement-card-a2-case2-raw-order-reference-density-transport.md
review-a2-case2-raw-order-reference-density-transport.md
```

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probe passed.
The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no raw-Haar identification, no determinant-chart Haar domination,
no original/source-prior density construction, no source-image/source-rank
coverage, no normal crossings, no pole order, and no RLCT extraction.

## 2026-07-01 Case 2 raw-order reference same-shrink package

Lean now proves:

```text
exists_open_subset_case2PassiveThetaRawOrderReferenceImage_same_shrink_package
```

This packages the named raw-order reference image support/domination,
endpoint-reference to raw-order image equality, raw-order to source-chart
pushforward equality, and raw-density transport on a single local `V`.

Artifacts:

```text
reproduction-a2-case2-raw-order-reference-same-shrink-package.md
statement-card-a2-case2-raw-order-reference-same-shrink-package.md
review-a2-case2-raw-order-reference-same-shrink-package.md
```

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probe passed.
The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.  Xhigh reviewers `Jason the 3rd`
and `Fermat the 3rd` passed the same-shrink Lean/API and source-boundary
checks.

Nonclaims: no raw-Haar identification or raw-Haar pushforward, no
determinant-chart Haar domination, no full determinant-chart Haar target, no
exact Haar transport or scalar normalization, no p.13 source coverage, no
source-image/source-rank coverage, no original source-prior or original-volume
transport, no bounded-density construction, no normal crossings, no pole
order, and no RLCT extraction.

## 2026-07-01 Case 2 original-volume/source-image same-shrink conditional

Lean now proves:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_sourceImageReference_same_shrink_of_case2PassiveTheta_rawMap_eq_restrict_rawSource
```

This is the honest local source-image version of the p.13
raw-order/original-volume bridge.  It uses one local `V` for readback,
injectivity, continuity, source-image measurability, p.13 source containment,
and the conditional inverse-Haar density identity.  The raw-Haar raw-source
pushforward identity is still an explicit hypothesis.

Artifacts:

```text
reproduction-a2-case2-original-volume-source-image-same-shrink-conditional.md
statement-card-a2-case2-original-volume-source-image-same-shrink-conditional.md
review-a2-case2-original-volume-source-image-same-shrink-conditional.md
```

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probe passed.
The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no raw-Haar identification, no raw-Haar pushforward proof, no
determinant-chart Haar transport, no source-image/source-rank coverage, no
original source-prior transport, no normal crossings, no pole order, and no
RLCT extraction.

## 2026-07-01 Case 2 original-volume readback domination same-shrink conditional

Lean now proves:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_case2PassiveTheta_rawMap_eq_restrict_rawSource
```

This composes the same-shrink conditional original-volume/source-image bridge
with the direct readback-domination adapter.  It returns one local `V subset G`
with readback, injectivity, continuity, measurable image, and p.13 source-set
containment; on any measurable chart piece inside `sourceChart '' V`, the
explicit raw-Haar raw-source pushforward hypothesis gives readback
a.e. measurability and domination by the inverse Haar scalar times
`thetaReference.restrict G`.

Artifacts:

```text
reproduction-a2-case2-original-volume-readback-domination-same-shrink-conditional.md
statement-card-a2-case2-original-volume-readback-domination-same-shrink-conditional.md
review-a2-case2-original-volume-readback-domination-same-shrink-conditional.md
```

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probe passed.
The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no raw-Haar identification, no raw-Haar pushforward proof, no
determinant-chart Haar transport, no source-image/source-rank coverage, no
original source-prior transport, no scalar normalization, no normal crossings,
no pole order, and no RLCT extraction.

## 2026-07-02 A2 with-following original-volume source-image inverse-Haar density

Lean now proves:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_sourceReference_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource

exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_sourceImageReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
```

The p.13 theorem reproduces the exact scalar calculation: the with-following
raw-order/source-chart two-stage identity and a supplied exact raw-source
pushforward give

```text
sourceRef = c • originalVolume.restrict p13SourceSet.
```

After restricting to a measurable p.13 chart piece and using `0 < c`, this
becomes:

```text
originalVolume.restrict chartPiece =
  (sourceRef.withDensity (fun _ => c^-1)).restrict chartPiece.
```

The source-image theorem shrinks through the existing with-following
source-image support package, so chart pieces contained in `sourceChart '' V`
automatically lie in the p.13 source set.  It also returns readback,
injectivity, continuity, measurable image, and p.13 support on the final
shrink.

Artifacts:

```text
reproduction-a2-with-following-original-volume-source-image-invhaar-density.md
statement-card-a2-with-following-original-volume-source-image-invhaar-density.md
```

Focused local build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeBridge`,
full local `lake build DLNFibre`, `scripts/sorries`, `git diff --check`,
touched Lean-file forbidden-marker scan, direct axiom probes, and xhigh review
passed.  Both declarations report
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: exact raw-pushforward remains a hypothesis.  This is not
determinant-Haar transport, raw-Haar transport, source-prior/original-prior
transport, arbitrary source-density positivity, global source-image coverage,
source-rank coverage, normal crossings, pole order, or RLCT extraction.

## 2026-07-01 Case 2 reverse raw-source density lower adapter

Lean now proves the generic lower-density adapter:

```text
smul_restrict_le_restrict_withDensity_of_ae_le
measure_le_inv_smul_of_smul_le
measure_le_smul_of_le_smul_of_smul_le
measure_le_smul_map_restrict_withDensity_of_le_smul_map_restrict_of_ae_le
weighted_map_ref_le_smul_map_comp_withDensity_comp_of_le_smul_map
```

and the concrete Case 2 reverse raw-source theorem:

```text
exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveTheta_rawMap_baseJ_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple

exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveTheta_rawMap_coordinateSourceMeasure_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
```

The first concrete theorem turns an explicit determinant-side reverse
domination

```text
rawHaar.restrict rawDetChart
  <= Cdet • Measure.map Y (passiveSource.restrict V)
```

into

```text
rawHaar.restrict rawSourceSet
  <= Cdet • Measure.map rawMap (baseJ.restrict V).
```

The second theorem adds an explicit lower bound

```text
epsilon <= sourceDensity z
```

for `baseJ.restrict V`-a.e. `z`, plus `Cdet < infinity`, `epsilon != 0`,
and `epsilon != infinity`, and concludes

```text
rawHaar.restrict rawSourceSet
  <= (Cdet * epsilon^{-1}) •
     Measure.map rawMap (coordinateSourceMeasure.restrict V)
```

with finite scalar.

Artifacts:

```text
reproduction-a2-case2-reverse-raw-source-density-lower-adapter.md
statement-card-a2-case2-reverse-raw-source-density-lower-adapter.md
review-a2-case2-reverse-raw-source-density-lower-adapter.md
```

Focused warning-clean elaboration, focused local module builds, full local
`lake build DLNFibre`, `scripts/sorries`, `git diff --check`, direct theorem
axiom audits, and xhigh read-only review passed.  The direct axiom probes
reported only `[propext, Classical.choice, Quot.sound]`.

Nonclaims: the determinant-side reverse domination and source-density lower
bound remain explicit hypotheses.  This does not prove determinant-chart Haar
transport, exact raw-Haar pushforward, raw-Haar normalization, source-image
coverage, source-rank coverage, original source-prior transport, normal
crossings, pole order, or RLCT extraction.

## 2026-07-01 Case 2 original-volume/source-image domination from formal-product domination

Lean now proves:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_same_shrink_of_formalProductMeasure_le_smul_sourceReference
```

On one local source-chart shrink `V subset G`, if a measurable chart piece is
contained in `sourceChart '' V`, then the already-proved source-image support
puts it inside the p.13 source edge-family set.  A supplied comparison

```text
formalProductMeasure.restrict chartPiece
  <= D * Measure.map sourceChart (thetaReference.restrict V)
```

therefore gives

```text
originalVolume.restrict chartPiece
  <= (cHaar^{-1} * D) *
     Measure.map sourceChart (thetaReference.restrict V).
```

Artifacts:

```text
reproduction-a2-case2-original-volume-source-image-domination-from-formal-product-domination.md
statement-card-a2-case2-original-volume-source-image-domination-from-formal-product-domination.md
review-a2-case2-original-volume-source-image-domination-from-formal-product-domination.md
```

Focused warning-clean elaboration, focused module build, dependent readback
module build, full local `lake build DLNFibre`, `lean/scripts/sorries`,
`git diff --check`, and direct theorem axiom audit passed.  The theorem
reports only `[propext, Classical.choice, Quot.sound]`.

Nonclaims: this theorem does not prove the formal-product/source-image
domination hypothesis, raw-Haar transport, source-prior transport, source-rank
coverage, normal crossings, pole order, or RLCT.  Xhigh scouts `Aquinas` and
`Descartes` both identified the remaining theorem as a genuine local
change-of-variables/source-coverage/lower-density comparison on actual chart
pieces.

## 2026-07-01 Case 2 source-image forward domination from raw domination

Lean now proves:

```text
aemeasurable_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_rawSourceSet

exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_le_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet_of_rawMap_le_smul_restrict_rawSource
```

A supplied one-way raw domination

```text
Measure.map rawMap (thetaReference.restrict V)
  <= C * rawHaar.restrict rawSourceSet
```

pushes forward to

```text
Measure.map sourceChart (thetaReference.restrict V)
  <= (C * cHaar) * originalVolume.restrict p13SourceSet.
```

Artifacts:

```text
reproduction-a2-case2-source-image-forward-domination-from-raw-domination.md
statement-card-a2-case2-source-image-forward-domination-from-raw-domination.md
review-a2-case2-source-image-forward-domination-from-raw-domination.md
```

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct theorem axiom audits
passed for this checkpoint.  Both new declarations report only
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: this is the forward direction only.  It does not prove the reverse
comparison needed for original-volume readback domination, does not remove the
raw-pushforward equality in the finite-integral theorem, and does not prove
raw-Haar identification, source-image coverage, source-rank coverage,
normal crossings, pole order, or RLCT.

## 2026-07-01 Case 2 original-volume finite integral raw-pushforward conditional

Lean now proves:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolume_readback_invHaar_of_case2PassiveTheta_rawMap_eq_restrict_rawSource_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

The theorem calls the direct original-volume finite-integral front end, then
uses the same-shrink readback bridge with `G := W`.  It returns `V subset W`;
for measurable chart pieces inside both `U inter sourceStratum` and
`sourceChart '' V`, the explicit raw-Haar raw-source pushforward for
`coordinateSourceMeasure.restrict V` discharges the readback a.e.
measurability and domination hypotheses, so bounded original-prior densities
give the finite p.13 regular-coordinate integral.

Artifacts:

```text
reproduction-a2-case2-original-volume-finite-integral-raw-pushforward-conditional.md
statement-card-a2-case2-original-volume-finite-integral-raw-pushforward-conditional.md
review-a2-case2-original-volume-finite-integral-raw-pushforward-conditional.md
```

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probe passed.
The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.

Nonclaims: no raw-Haar identification, no raw-Haar pushforward proof, no
determinant-chart Haar transport, no source-image/source-rank coverage, no
original source-prior transport, no scalar normalization, no normal crossings,
no pole order, and no RLCT extraction.
