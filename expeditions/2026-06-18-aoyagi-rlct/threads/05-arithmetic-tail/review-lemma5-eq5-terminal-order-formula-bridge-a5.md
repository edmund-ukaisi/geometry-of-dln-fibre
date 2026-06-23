# Review - Lemma 5 Eq5 terminal order formula bridge

Date: 2026-06-23.

Reviewer: Singer, xhigh-effort subagent.

## Verdict

Pass.

## Findings

No formal or source-boundary issue was found.  The theorem is a pure finite
bookkeeping rewrite of the existing Eq5 terminal cardinality theorem

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze
```

whose conclusion is

```text
TC.terminalMinimumLabels.card = a * (N + 1 - a) + 1.
```

Specializing `a := data.aParam` and `M := data.ceilWidth` is faithful.
`data.aParam_le` supplies the existing theorem's `a <= N+1` hypothesis, and
`data.selectedSum_eq` is definitionally the selected-sum identity needed by
the Eq5 theorem.  The final rewrite is exactly the definition of
`data.theorem2OrderFormula`.

All other Eq5 payload hypotheses remain explicit.  The module imports only the
Eq5 terminal classifier and final-formula notation; it does not import or use
normal-crossing, final-assembly, or RLCT extraction interfaces.

## Residual Risk

The only naming risk is that `theorem2OrderFormula` is final notation, but the
theorem statement itself remains scoped to `TC.terminalMinimumLabels.card`.
The result should continue to be described as an Eq5 supplied-payload handoff,
not as source-backed Lemma 5 exactness, pole order, normal crossings, or RLCT.
