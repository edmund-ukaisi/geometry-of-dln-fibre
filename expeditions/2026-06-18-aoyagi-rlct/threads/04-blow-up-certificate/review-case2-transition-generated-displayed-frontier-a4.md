# Review - A4 Case 2 transition-generated displayed frontier

Date: 2026-06-24.

Reviewer: `Faraday the 2nd`, xhigh-effort independent subagent.

Status: pass.  No blocking findings.

## Scope

Reviewed the uncommitted finite displayed-overlap reducer:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- `reproduction-case2-transition-generated-displayed-frontier-a4.md`;
- `statement-card-a4-case2-transition-generated-displayed-frontier.md`.

The review checked the displayed chart index, denominator hypothesis,
transition-generated target data, displayed frontier/continuing certificate
instantiation, and overclaim risks.

## Findings

No blocking formalisation or mathematical issues were found.

The denominator is the normalized displayed coordinate
`x_(J+1,J+1) != 0`, not the finite center value
`u * x_(J+1,J+1)`.  The displayed chart index is the finite chart whose
selected pivot is `(J+1,J+1)`.

The target data are consistently

```text
targetU = u * denom
targetResidual q = sourceNormalized q / denom
```

and the displayed frontier and continuing certificates are instantiated only
at these transition-generated displayed data.  They are not statements about
the original arbitrary source-chart data.

The formal theorem proves finite chart-map equality plus existing displayed
frontier/continuing package instantiation.  It does not prove source
production, analytic transition regularity, chart coverage, normal crossings,
pole order, or RLCT.

## Non-Blocking Note

This slice is not the separate substitution-block rewrite identified by the
source scout.  It does not identify the displayed substitution block or `Q/P`
block with a source-side block expression.

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
