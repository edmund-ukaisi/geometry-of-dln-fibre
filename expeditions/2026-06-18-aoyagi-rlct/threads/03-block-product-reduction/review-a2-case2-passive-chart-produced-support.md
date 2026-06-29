# Review - A2 Case 2 Passive Chart-Produced Support

Date: 2026-06-29.

Reviewer: Peirce the 3rd, xhigh, read-only.

Verdict: PASS.

## Scope Checked

Lean theorems:

```text
measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_restrict_retainedPassiveP13LocalSource_eq_self
measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_restrict_sourceRankStratum_eq_self
```

Artifacts reviewed:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
reproduction-a2-case2-passive-chart-produced-support.md
statement-card-a2-case2-passive-chart-produced-support.md
theorem-ledger.md
```

## Findings

No issues found.

The two Lean wrappers only prove restriction/support identities for

```text
mu := Measure.map sourceChart sourceMeasure
```

The local-source theorem proves `mu.restrict localSource = mu`.  The
source-rank theorem proves `mu.restrict sourceStratum = mu`.

Both theorems require explicit `AEMeasurable sourceChart sourceMeasure`.  The
source-rank theorem additionally requires `hprod`, `hr0`, and an a.e.
successor-rank equation on the passive-domain measure.

The proofs are narrow: they turn pointwise or a.e. chart membership into a
measure-restriction identity via the generic support lemmas.  They do not
construct a product measure, determinant-chart pushforward, source prior,
Jacobian formula, normal-crossing chart, pole order, or RLCT extraction.

The reproduction, statement card, and ledger state the same nonclaim boundary:
no concrete passive product measure, no passive source-chart continuity
theorem, no source-rank coverage, no source-image equality, no determinant-
chart pushforward, no source-prior transport, no normal crossings, pole order,
or RLCT.

## Gates

Controller gates:

```text
git diff --check
scripts/sorries
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
lake env lean /tmp/aoyagi_case2_passive_chart_support_axioms.lean
```

Results: whitespace clean; `0 sorry, 0 #exit, 0 native_decide, 0 axiom`;
focused build passed; direct axiom probes for both theorem names report only
`[propext, Classical.choice, Quot.sound]`.

## Decision

Accept and bank.  Next boundary is not another support wrapper unless it
feeds a downstream theorem directly; the source-measure frontier needs a
concrete passive product-measure/continuity package or a larger
passive-selected-entry chart construction with local inverse, image, and
Jacobian accounting.
