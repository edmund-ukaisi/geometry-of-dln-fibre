# Statement card - A5 Lemma 5 Eq5 terminal pAlpha endpoint cardinal squeeze

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_endpointBase_cardSqueeze`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_endpointBase_cardSqueeze`

## Claim

For a supplied terminal-candidate family, the Eq5 terminal cardinal squeeze
gives terminal-minimum exactness and the exact finite count after replacing
both the opaque counted-datum injectivity hypothesis and the opaque
base/nonbase branch-label separation hypothesis by structured supplied data.

## Proved

Lean composes:

- `terminalMinimumCountDatum_injOn_of_eq5OwnBlock_pAlpha_injOn`;
- `branchLabel_injOn_of_eq5AlphaIndexed_nonbase_terminalEndpointBase`;
- the existing Eq5 own-block common-domain cardinal-squeeze wrappers.

The result proves `TC.TerminalMinimumLabelExactness` and

```text
TC.terminalMinimumLabels.card = a * (N + 1 - a) + 1.
```

## Assumed

The terminal-candidate family, `a <= N+1`, selected-width sum, source width
inequalities, Eq5 piecewise source-vector data for every terminal-minimum
label, own-block membership for terminal labels, last-point source range,
selected-width source hypotheses, the terminal-label Eq5 label formula,
terminal-label nonbase inequality, terminal `(p, alpha)` injectivity,
coordinatewise branch alpha injectivity, nonbase branch source-coordinate block
membership, the nonbase Eq5 branch-label formula, and the explicit
terminal-endpoint base label.

## Deferred

Eq5 branch construction, alpha-domain coverage, source production of terminal
Eq5 payloads, source proof of terminal `(p, alpha)` injectivity, counted-datum
back-to-label coverage, upper-bound classifier construction from source,
no-extra terminal-minimum coverage, Lemma 5 order count, pole order, normal
crossings, and RLCT extraction.

## Cited

None; this is finite Lean bookkeeping over supplied hypotheses and previously
formalized definitions.

## Verification

Focused Lean check:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean
```

## Review

Independent xhigh hardener review by Lagrange passed on 2026-06-22.  Review
artifact:
`review-lemma5-eq5-terminal-palpha-endpoint-cardinal-squeeze-a5.md`.
