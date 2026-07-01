# Review - A2 p.13 Original-prior Volume-source-reference Readback

Date: 2026-07-01.

Reviewers: controller proof check; xhigh read-only review by Linnaeus the 2nd.

Status: PASS after focused checks, full local build, no-sorry audit,
whitespace check, direct axiom probes, and xhigh review.

## Scope

Audit the composed original-prior readback bridge in:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13SourceMeasureBridge.lean
```

Public Lean names:

```text
originalEdgeFamilyPrior_map_readback_restrict_chartPiece_le_smul_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure
originalEdgeFamilyPrior_p13VolumeReadbackDominationScalar_lt_top
```

## Findings

The theorem composes two previously checked bridges.  First, restricted
original edge-family volume domination plus the supplied source-reference
readback identity gives readback domination of the formal p.13 chart-piece
measure.  Second, the existing original-prior-to-formal-p.13 bridge transfers
that domination to the locally bounded original prior.

The scalar is intentionally unsimplified:

```text
(ENNReal.ofReal K * ((c^-1 : NNReal) : ENNReal)) * ((c : ENNReal) * D)
```

No cancellation or normalization of the Haar scalar is claimed.  The companion
lemma proves this displayed scalar is finite when `D < ∞`.

Focused elaboration passed for `OriginalEdgeFamilyP13SourceMeasureBridge.lean`;
focused Lake build passed for
`DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13SourceMeasureBridge`.

## Independent xhigh Review

Linnaeus the 2nd returned PASS.  The reviewer confirmed that the scalar
composition is conservative: the theorem keeps the product
`ENNReal.ofReal K * ((c^-1 : NNReal) : ENNReal) * ((c : ENNReal) * D)`
without cancelling or normalizing Haar factors.  The reviewer also confirmed
that the finiteness lemma honestly needs only `D < ∞`, since `ofReal K` and
coerced `NNReal` factors are finite ENNReal scalars.

## Nonclaims Checked

No proof of restricted-volume domination is included.  There is no
identification of `sourceRef` or `thetaRef`, no passive-theta source-image
equality, no source coverage, no chart-image equality, no Haar scalar
normalization or cancellation, no normal crossings, no pole order, and no RLCT
extraction.
