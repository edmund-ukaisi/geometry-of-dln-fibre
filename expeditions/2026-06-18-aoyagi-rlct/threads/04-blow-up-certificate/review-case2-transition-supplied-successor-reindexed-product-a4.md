# Review - A4 Case 2 transition supplied-successor reindexed product

Date: 2026-06-24.

Reviewer: xhigh subagent `Kant the 2nd`.

Verdict: pass after statement-shape tightening.

## Scope

Reviewed the proposed theorem composing:

- the displayed-overlap transition substitution rewrite in
  `SelectedEntryNormalCrossing.lean`;
- the supplied-`Csucc` reindexed product consumer in `BlowupArithmetic.lean`.

No files were edited by the reviewer.

## Findings

The target is source-boundary safe when stated as a pure consumer theorem.  It
must universally quantify over the displayed supplied boundary and over

```text
ob : SourceProductionObligation data targetResidual ...
```

and must not construct `ob`, construct `Csucc`, introduce an existential
source-production package, or call the canonical formula-level obligation
constructor as if it were source production.

The main Lean risk was dependent proof arguments: transition facts naturally
use the chart-family proofs `hS` and `hcont`, while the supplied-obligation
consumer returns the product in the types using `data.stage_pos` and
`data.continuation`.  The implemented theorem was tightened so that the final
product clause uses `data.stage_pos` and `data.continuation`, letting the
obligation consumer produce the row-operation witness in exactly the target
type.

The reviewer also noted that explicit `targetU` and `targetResidual`
parameters with equations are a valid way to make the transition-generated
target data available to the earlier `data` and `ob` binders.

## Boundary Check

Passed.  The theorem consumes a supplied obligation for the
transition-generated displayed data.  It does not construct source production,
successor charts, suffixes, coverage, transition regularity, analytic
Jacobian/volume data, normal crossings, pole order, or RLCT.

## Verification

After incorporating the statement-shape recommendation, the focused module
build passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
```
