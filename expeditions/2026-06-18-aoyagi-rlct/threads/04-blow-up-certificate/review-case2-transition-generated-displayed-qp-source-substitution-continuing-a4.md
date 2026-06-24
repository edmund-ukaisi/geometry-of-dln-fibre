# Review - A4 Case 2 displayed Q/P source-substitution continuing handoff

Date: 2026-06-24.

Reviewer: `Averroes the 2nd`, xhigh-effort independent subagent.

Status: pass.  No blocking findings.

## Scope

Reviewed the uncommitted displayed `Q/P` source-substitution handoff:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- `reproduction-case2-transition-generated-displayed-qp-source-substitution-continuing-a4.md`;
- `statement-card-a4-case2-transition-generated-displayed-qp-source-substitution-continuing.md`;
- expedition summary updates.

The deeper displayed reindexed next-source product theorem was not part of the
landed slice; the review only checked that it was not claimed.

## Findings

No blocking formalisation or mathematical issues were found.

The denominator is correctly the source-normalized displayed coordinate
`x_(J+1,J+1)`, not the finite center value `u*d`.

The `Q/P` rewrite only replaces the left substituted residual block with the
original source selected substitution block.  The normalized block, Schur
block, successor weights, transported following factor, frontier package, and
continuing certificate remain displayed transition-generated target data.

The documents state the correct boundary: no deeper reindexed next-source
product with the source-side substitution block is claimed, and no analytic
regularity, coverage, source production, normal crossings, pole order, or RLCT
extraction is claimed.

## Gates

Reviewer read-only checks passed:

```text
git diff --check 58a60d61
```

The reviewer also found no `sorry`, `admit`, `axiom`, `native_decide`,
`#exit`, or `unsafe` in the changed reviewed files.

The reviewer did not run Lean builds because builds write artifacts.  The
controller ran:

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

## Minimal Repair

None required.
