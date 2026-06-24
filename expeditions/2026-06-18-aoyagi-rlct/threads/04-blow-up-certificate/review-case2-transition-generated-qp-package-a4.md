# Review - A4 Case 2 transition-generated Q/P package

Date: 2026-06-24.

Reviewer: `Cicero the 2nd`, xhigh-effort independent subagent.

Status: pass.  No blocking findings.

## Scope

Reviewed the finite Case 2 transition-generated `Q/P` package:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- `reproduction-case2-transition-generated-qp-package-a4.md`;
- `statement-card-a4-case2-transition-generated-qp-package.md`.

The review checked the denominator hypothesis, the shared
transition-generated target data, the supplied target-pivot `Q/P` identity,
the lower-right Schur formula, and the absence of source-production or
analytic-transition overclaims.

## Findings

No blocking findings.

The theorem

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_sourceSelectedQP_package_of_target_normalized_ne_zero
```

sets the denominator to the source normalized target coordinate, then uses
the same target data throughout:

```text
targetU = u * denom
targetResidual q = sourceNormalized q / denom
```

The nonzero hypothesis is exactly the normalized target coordinate, not
`u * denom`.

The `Q/P` conjunct instantiates the existing supplied target-pivot
source-selected theorem at `targetChart` with those `targetU` and
`targetResidual` values.  The Schur conjunct uses the target
residual-subtype lower-right block with the same normalized denominator and is
discharged by the existing denominator-cleared block lemma.

The statement packages only the three advertised finite facts: chart-map
equality, supplied target-pivot `Q/P`, and denominator-cleared lower-right
Schur overlap.  It does not assert source production of successor residual
matrices or following factors, raw residual-function equality, analytic
transition regularity, chart coverage, normal crossings, pole order, RLCT, or
repair of the printed Case 2 vector mismatch.

## Gates

Passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry audit reports:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

The full `DLNFibre` build completed with pre-existing Core/style warnings
outside this slice.

## Minimal Repair

None required.
