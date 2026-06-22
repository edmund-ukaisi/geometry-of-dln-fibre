# Statement card - A5 Lemma 5 terminal exactness cardinal-bound equivalence

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_card_bound_and_branchLabel_injOn`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_injOn_and_card_bound`

## Claim

For a supplied terminal-candidate family, once the supplied branch labels are
known to attain the terminal minimum, terminal-minimum exactness is equivalent
to the conjunction of:

- branch-label injectivity on the supplied full branch set; and
- a supplied numeric upper bound
  `C.terminalMinimumLabels.card <= a * (n + 1 - a) + 1`.

## Proved

Lean proves the finite cardinal squeeze:

```text
C.branchLabelImage subset C.terminalMinimumLabels
|C.branchLabelImage| = a * (n + 1 - a) + 1
C.terminalMinimumLabels.card <= a * (n + 1 - a) + 1
---------------------------------------------------------
C.terminalMinimumLabels = C.branchLabelImage
```

The equivalence theorem packages this as
`TerminalMinimumLabelExactness iff branch-label injectivity plus the supplied
terminal-minimum cardinal upper bound`.

## Assumed

The terminal-candidate family, `a <= n+1`, the selected-width sum, supplied
branch-label injectivity, and the supplied terminal-minimum cardinal upper
bound where used.

## Deferred

Source proof of the terminal-minimum cardinal upper bound, source construction
of branch-label injectivity, source classifier or back-to-label map,
source-label legality, source branch coverage, minimum-to-lambda bridge, chart
coverage, pole order, normal crossings, and RLCT extraction.

## Cited

None.  This is finite set/cardinality bookkeeping over supplied hypotheses.

## Verification

Focused, module, and full-library checks pass:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.Lemma5TerminalBridge
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reports only pre-existing Core warnings.

Independent xhigh review is recorded in
`review-lemma5-terminal-exactness-card-bound-equivalence-a5.md`.
