# Review - A2 p.13 Formal-volume Source-reference Domination

Date: 2026-07-01.

Reviewers: controller proof check; xhigh read-only review by Hubble the 2nd.

Status: PASS after focused checks, full local build, no-sorry audit,
whitespace check, direct axiom probes, and xhigh review.

## Scope

Audit the p.13 formal-volume source-reference domination bridge in:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13SourceMeasureBridge.lean
```

Public Lean names:

```text
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_le_smul_sourceMeasure_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_readback_le_smul_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure
```

## Findings

The first theorem only uses the existing p.13 chart-piece equality
`muP13 = c • volume.restrict chartPiece` and a supplied hypothesis
`volume.restrict chartPiece <= D • sourceRef`.  Pointwise scalar-measure
calculus gives `muP13 <= ((c : ENNReal) * D) • sourceRef`.

The second theorem composes this source-reference domination with the generic
readback handoff.  It requires `AEMeasurable readback sourceRef` and
`Measure.map readback sourceRef = thetaRef` as explicit hypotheses.

Focused elaboration passed for `OriginalEdgeFamilyP13SourceMeasureBridge.lean`;
focused Lake build passed for
`DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13SourceMeasureBridge`.  The downstream
`OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean` file also elaborated.

## Independent xhigh Review

Hubble the 2nd returned PASS.  The reviewer confirmed that the scalar
`((c : ENNReal) * D)` is the honest composition of the existing `NNReal` Haar
scalar equality with the supplied `D : ENNReal` domination, and that the
readback theorem remains conditional on source-reference a.e.-measurability and
the supplied pullback identity.

Wording discipline from the review: describe these as conditional
domination-transfer and readback-transfer lemmas, not as a proof of
restricted-volume domination or an identification of `thetaRef`.

## Nonclaims Checked

No proof of the restricted-volume domination is included.  There is no
identification of `sourceRef`, no passive-theta source-image equality, no
source coverage, no chart-image equality, no Haar scalar normalization, no
normal crossings, no pole order, and no RLCT extraction.
