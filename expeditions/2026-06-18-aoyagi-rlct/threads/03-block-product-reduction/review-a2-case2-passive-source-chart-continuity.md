# Review - A2 Case 2 Passive Source-Chart Continuity

Date: 2026-06-29.

Reviewer: Nash the 3rd, xhigh, read-only.

Verdict: PASS after two docstring wording fixes.

## Scope Checked

Lean theorems:

```text
continuous_case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport_withPassive
```

Artifacts reviewed:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

## Findings

No blocking formalisation or math-accuracy issues were found.

Low wording issue: the source-continuity docstring said "active determinant
unit hypotheses".  The actual hypotheses are determinant-chart unit hypotheses
for `Ctop` and passive `A1passive` blocks.  The controller changed this to
"determinant-chart unit hypotheses".

Low wording issue: the selected-entry continuity docstring said "finite
coordinate regularity", while the theorem is stated for arbitrary `rho`
without `[Fintype rho]`.  The controller changed this to
"coordinatewise/product-topology regularity".

## Assessment

The selected-entry continuity lemma's hypotheses match the implementation:
the passive fields are continuous on `eta`, the selected-entry `C` component
is obtained by composing the existing selected-entry datum continuity with
`Prod.snd`, and the proof assembles the product tuple before applying
`continuous_ofTopologyTuple`.  It does not prove determinant membership.

The source-chart continuity lemma uses the pointwise determinant assumptions
exactly to package `rawData` and `transportedData` into determinant-chart
subtypes.  The proof then composes raw-data continuity, endpoint-transport
continuity, and fixed-base source-chart continuity.  It does not use or imply
source-prior, Jacobian, measure, normal-crossing, or RLCT claims.

Proof-term/content-wise, the theorem is independent of source-prior,
Jacobian, and RLCT claims.  Module-level, it currently lives in
`RetainedPassiveCase2LocalJacobianMeasure.lean`, which imports the local
Jacobian-measure bridge; a later import-lightening pass may move it to a
lighter source/chart bridge file if that matters.

## Gates

Controller gates:

```text
git diff --check
scripts/sorries
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
lake env lean /tmp/aoyagi_case2_passive_source_chart_continuity_axioms.lean
```

Results before the docstring wording patch: whitespace clean; `0 sorry,
0 #exit, 0 native_decide, 0 axiom`; focused build passed; direct axiom probes
for both theorem names report only `[propext, Classical.choice, Quot.sound]`.
The controller reran gates after the wording patch before banking.

## Decision

Accept and bank.  Next target is the concrete passive product-measure package:
construct the passive-domain product measure, use continuity for a.e.
measurability, and compose with the already-banked passive chart-produced
support theorem.  Do not claim source-prior transport, determinant-chart Haar
pushforward, Jacobian accounting, normal crossings, pole order, or RLCT from
this continuity step.
