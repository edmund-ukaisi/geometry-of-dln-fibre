# Review - A4 Case 2 displayed reindexed product source-substitution

Date: 2026-06-24.

Reviewer: `Harvey the 2nd`, xhigh-effort independent subagent.

Status: pass.  No blocking findings.

## Scope

Reviewed the uncommitted displayed reindexed-product source-substitution
slice:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`;
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- `reproduction-case2-displayed-reindexed-product-source-substitution-a4.md`.

The review checked statement fidelity, denominator choice, target/source data
boundaries, overclaim risk, and whether the product wrapper rewrites only the
intended substitution block.

## Findings

No blocking formalisation or mathematical issues were found.

The denominator is correctly the source-normalized displayed coordinate
`x_(J+1,J+1)`, not the finite center value `u*d`.

The supplied block rewrite is confined to the left substitution block.  The
right-hand side remains displayed transition-generated data through
`targetResidual` and the formula-level successor following factor.

The generic product wrapper is congruence-only over the existing displayed
product theorem: the supplied block `B` appears only where the displayed
substitution block previously appeared, and the wrapper does not alter post
residuals, successor following factor, exponent data, or recurrence-gap data.

## Residual Risk

The reviewer did not rerun Lean, keeping the audit read-only.  The controller
ran the targeted module gate and the full gate set.

The reviewer did not audit unrelated uncommitted expedition ledger updates
outside the requested slice.

## Minimal Repair

Optional wording only: use "lower-left block" rather than "left lower block"
in the product-wrapper documentation.  The controller applied this wording
cleanup.
