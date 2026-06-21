# Statement Card - A5 Lemma 5 Terminal Exactness Source Frontier

## Claim

Aoyagi's Lemma 5 upper-bound paragraph suggests an upper classifier from
terminal lambda-vectors to the counted interval data, but it does not yet
discharge the Lean no-extra field
`terminalMinimumLabels subset branchLabelImage`.

## Current Lean Boundary

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.TerminalMinimumLabelExactness`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_exactness`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_exactness`

Commit pin for this boundary: `4f47996`.

## Proved

The Lean development proves the finite count from supplied exactness:
branch-label injectivity on `fullBranches` plus no-extra containment from
`terminalMinimumLabels` to `branchLabelImage`.

## Assumed

- Source terminal labels and their terminal exponent certificates.
- Terminal least-value-zero data.
- Numerator normalization to the isolated Lemma 5 minimum.
- Branch-label injectivity.
- No-extra containment, unless a future classifier theorem discharges it.

## Cited

None in this finite source-boundary audit.  The general normal-crossing-to-RLCT
extraction theorem remains the only planned analytic citation and is not used
here.

## Deferred

- Source-backed label-to-vector bridge.
- Source-backed minimum-to-lambda bridge.
- A classifier from terminal lambda-vectors to counted interval data.
- The Case 1(2) uniqueness/injection theorem behind the source's `J`-increase
  sentence.
- The back-to-label bridge from counted interval data to `branchLabelImage`.

## Status

Source audit recorded; not formalisation-ready as a source-backed no-extra
theorem.
