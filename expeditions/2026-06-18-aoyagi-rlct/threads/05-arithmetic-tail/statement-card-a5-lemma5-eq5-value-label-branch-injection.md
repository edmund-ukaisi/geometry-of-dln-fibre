# Statement card - A5 Lemma 5 Eq5 value-label branch injection

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_nonbase_valueLabel`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_nonbase_valueLabel_terminalEndpointBase`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze`

## Claim

For a supplied terminal-candidate family, nonbase branch-label injectivity
follows from selected-block membership, the supplied value-label relation
`TC.family.value b = branchLabel(some b).2 - 1`, and the supplied family's
one-coordinate value injectivity.  With the terminal-endpoint base label, this
gives full branch-label injectivity and can be composed with the existing
terminal pAlpha counted-datum injection in the finite cardinal squeeze.

## Proved

Lean proves branch-label injectivity on `TC.fullBranches`, then proves
conditional `TC.TerminalMinimumLabelExactness` and

```text
TC.terminalMinimumLabels.card = a * (N + 1 - a) + 1.
```

## Assumed

The supplied terminal-candidate family, selected cutpoints, nonbase selected
block membership, nonbase value-label relation, terminal-endpoint base label,
`a <= N+1`, selected-width sum, source width inequalities, Eq5 piecewise
source-vector data for every terminal-minimum label, own-block membership for
terminal labels, last-point source range, selected-width source hypotheses,
the terminal-label Eq5 label formula, terminal-label nonbase inequality, and
terminal `(p, alpha)` injectivity.

## Deferred

Eq5 branch construction, source proof of the value-label relation, source
production of terminal Eq5 payloads, source proof of terminal `(p, alpha)`
injectivity, direct counted-datum back-to-label coverage, upper-bound
classifier construction from source, source-backed no-extra terminal-minimum
coverage, Lemma 5 order count, pole order, normal crossings, and RLCT
extraction.

## Cited

None; this is finite Lean bookkeeping over supplied hypotheses and previously
formalized definitions.

## Verification

Focused Lean check:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean
```

## Review

Independent xhigh review passed after wording repair.  Review artifact:
`review-lemma5-eq5-value-label-branch-injection-a5.md`.
