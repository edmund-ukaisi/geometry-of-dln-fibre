# Statement card - A5 Lemma 5 Eq5 terminal alpha-injection cardinal squeeze

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_alphaIndexedBranch_cardSqueeze`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_alphaIndexedBranch_cardSqueeze`

## Claim

For a supplied terminal-candidate family, the Eq5 terminal counted-datum
cardinal squeeze gives terminal-minimum exactness and the exact finite count
after replacing the opaque supplied branch-label injectivity hypothesis by
the explicit Eq5 alpha-indexed branch-label injection hypotheses.

## Proved

Lean composes:

- the Eq5 terminal counted-datum cardinal-squeeze wrappers;
- `branchLabel_injOn_of_eq5AlphaIndexed_nonbase`.

The result proves `TC.TerminalMinimumLabelExactness` and
`TC.terminalMinimumLabels.card = a * (N + 1 - a) + 1`.

## Assumed

The terminal-candidate family, `a <= N+1`, selected-width sum, Eq5 piecewise
source vector data for every terminal-minimum label, own-block membership for
terminal labels, last-point source range, selected-width source hypotheses,
the terminal-label Eq5 label formula, terminal-label nonbase inequality,
counted-datum injectivity, the branch alpha map, coordinatewise branch alpha
injectivity, branch source-coordinate block membership, the nonbase branch
Eq5 label formula, and base/nonbase branch-label separation.

## Deferred

Eq5 branch construction, alpha-domain coverage, source production of terminal
Eq5 payloads, counted-datum injectivity, counted-datum back-to-label coverage,
upper-bound classifier construction, no-extra terminal-minimum coverage,
Lemma 5 order count, pole order, normal crossings, and RLCT extraction.

## Verification

Focused Lean check:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean
```

## Review

xhigh reviewer `Jason` passed; see
`review-lemma5-eq5-terminal-alpha-injection-cardinal-squeeze-a5.md`.
