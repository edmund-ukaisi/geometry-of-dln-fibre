# Review - A2 p.13 Original-prior Readback Domination

Date: 2026-07-01.

Reviewer: Euclid the 2nd, xhigh no-shell audit over line-numbered snippets.

Status: PASS.

## Scope

Audit the new conditional p.13 original-prior readback bridge:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13SourceMeasureBridge.lean
threads/03-block-product-reduction/reproduction-a2-p13-original-prior-readback-domination.md
threads/03-block-product-reduction/statement-card-a2-p13-original-prior-readback-domination.md
```

## Findings

No issues found.

The theorem matches the intended contract.  It assumes
`AEMeasurable readback muP13` and
`Measure.map readback muP13 <= Cformal • thetaRef`, then concludes both
readback a.e.-measurability and mapped-measure domination for
`originalPriorPiece`.

The scalar orientation is correct.  The source-side prior domination is

```text
originalPriorPiece <= alpha • muP13,
```

with

```text
alpha := ENNReal.ofReal K * ((c^-1 : NNReal) : ENNReal),
```

and composing it with the supplied readback domination gives
`(alpha * Cformal) • thetaRef`.

The a.e.-measurability transfer uses absolute continuity from the source-side
scalar domination.  The generic helper
`measure_le_smul_of_le_smul_of_le_smul` is the expected scalar-domination
composition lemma.

## Residual Risks and Nonclaims

Correctness still depends on the upstream p.13 bounded-prior comparison lemma
having the intended p.13 Jacobian/Haar scalar content.  The theorem also still
requires `chartPiece` to be measurable and contained in the p.13 source set.

This theorem does not prove readback measurability, formal readback
domination, passive-theta image containment, source coverage, Haar scalar
normalization, restricted Haar structure, normal crossings, pole order, or
RLCT extraction.  It also does not identify the formal p.13 chart measure with
a passive-theta source-image measure.
