# Review - A4 Case 2 transition source-current stack supplied successor

Date: 2026-06-24.

Reviewer: xhigh subagent `Euclid the 2nd`.

Verdict: pass.

## Scope

Reviewed the theorem

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.
  sourceChartTransitionPoint_displayed_continuingSourceCurrentStack_suppliedCsucc_sourceSubstitution_of_displayed_normalized_ne_zero
```

in `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`, together
with the reproduction artifact
`reproduction-case2-transition-source-current-stack-supplied-successor-a4.md`.

No files were edited by the reviewer.

## Findings

The statement keeps the intended boundary.  The transition-generated target
data are explicit through `targetU` and `targetResidual` equations; `data` is
typed over `targetU`; and `ob` is typed over `targetResidual`.

The continuing guard `hnext` is present and is passed directly to the
supplied-obligation source-current stack consumer.

The original source selected substitution block is used only in two places:

- the displayed target substitution-block equality;
- the lower-left block of the source-current stack identity.

The post-pivot residual block, Schur block, displayed paper matrices, weights,
`Csucc`, and center/principalization outputs remain target-displayed, using
`targetU` and `targetResidual`.

The theorem does not construct `SourceProductionObligation`, `Csucc`, `Cterm`,
suffixes, successor charts, chart coverage, transition regularity, normal
crossings, pole order, or RLCT data.

## Verification

Reviewer verification:

```text
lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean
```

Controller focused build:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
```
