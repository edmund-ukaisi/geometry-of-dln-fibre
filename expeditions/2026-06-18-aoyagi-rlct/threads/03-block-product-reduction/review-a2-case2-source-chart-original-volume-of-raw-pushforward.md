# Review - A2 Case 2 source-chart original-volume identity from raw pushforward

Date: 2026-07-01.

Status: local controller review pass; xhigh Lean/fidelity and mathematical
boundary reviews pass.

## Target

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeBridge.lean
```

Public theorems:

```text
exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_eq_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet_of_rawMap_eq_restrict_rawSource

exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_sourceReference_of_case2PassiveTheta_rawMap_eq_restrict_rawSource
```

Statement and reproduction:

```text
statement-card-a2-case2-source-chart-original-volume-of-raw-pushforward.md
reproduction-a2-case2-source-chart-original-volume-of-raw-pushforward.md
```

## Fidelity Check

The Lean statements keep the raw-pushforward identity as an explicit
hypothesis:

```text
Measure.map rawMap (thetaReference.restrict V) =
  rawHaar.restrict rawSourceSet
```

The first theorem only composes that supplied identity with the already-proved
local two-stage source-chart equality and the p.13 raw-order
original-volume bridge.  It does not prove that the passive-theta raw map has
raw Haar pushforward.

The second theorem restricts the first theorem to a measurable chart piece
contained in the named p.13 source edge-family set, uses positivity of the
tuple-side Haar scalar to invert

```text
sourceRef.restrict chartPiece =
  c • originalVolume.restrict chartPiece,
```

and rewrites scalar multiplication as constant `withDensity`.  The returned
a.e. density bound is reflexive.

## Precision Check

The theorem names include both the concrete Case 2 passive-theta source chart
and the raw-pushforward hypothesis.  They do not contain `rlct`,
`normalCrossing`, `sourceCoverage`, or `sourceRankCoverage`.  The file
docstring and theorem docstrings state the same nonclaims as the statement
card.

The scalar is not normalized to `1`; it remains

```text
(Measure.map paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
  rawHaar).addHaarScalarFactor originalTupleVolume.
```

## Boundary

This review finds no claim that Aoyagi p.13 proves a full raw Haar
pushforward.  The theorem is a conditional consumer of the missing raw-measure
transport statement.  It also does not prove original source-prior transport,
source-image coverage, source-rank coverage, normal crossings, pole order, or
RLCT extraction.

The next non-socket mathematical frontier remains the actual local
raw-pushforward/density theorem or a bounded-density comparison to the
passive-theta source-image reference.

## Xhigh Reviews

Pascal the 3rd checked the Lean signatures and found no hidden overclaim or
typeclass issue.  The only wording issue was a docstring phrase saying
`thetaReference` rather than `thetaReference.restrict V`; this was corrected.

Euler the 3rd checked the source boundary and found no blocking defect.  The
bridge is an honest conditional consumer: it assumes
`Measure.map rawMap (thetaReference.restrict V) = rawHaar.restrict rawSourceSet`
and does not infer it from Aoyagi p.13.  Euler also confirmed that the
inverse-density corollary is valid from the positive scalar identity.  The
recommended wording guardrails were applied: the reproduction now says the
pushforward equality is assumed, the Lean docstring says
`chart-produced source reference`, and the statement card refers to the
previously formalized raw-order p.13-coordinate volume bridge.

## Verification

Commands run locally:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeBridge.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeBridge
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_original_volume_bridge_axioms.lean
```

All passed.  The direct axiom probe for both public theorem names reported
only `[propext, Classical.choice, Quot.sound]`.  The focused and full builds
emitted existing linter warnings from imported modules.
