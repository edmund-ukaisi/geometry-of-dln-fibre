# Review - Lemma 5 Eq5 structured injection adapters

Reviewer: xhigh `Newton`.

Scope:

- `aoyagiLemma5Eq5_ownBlock_countDatum_injOn_of_pAlpha_injOn`;
- `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumCountDatum_injOn_of_eq5OwnBlock_pAlpha_injOn`;
- `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_none_ne_some_of_terminalEndpointLabel_and_nonbaseBlock`;
- `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_eq5AlphaIndexed_nonbase_terminalEndpointBase`;
- reproduction and statement card for the slice.

## Findings

Low: the reproduction and statement card initially said implementation and
verification were pending after the Lean had landed.  This was corrected.

## Verdict

Pass.  The counted-datum injection lemma keeps Eq5 payloads, own-block
membership, and supplied `(p, alpha)` injectivity explicit.  It does not derive
`(p, alpha)` injectivity or claim coverage.  The terminal wrapper is only a
specialization over `TC.terminalMinimumLabels`.

The base/nonbase separation lemma uses the explicit terminal-endpoint base
label and nonbase block membership, then applies the half-open selected-block
endpoint exclusion.  The composed branch-label injectivity adapter remains
conditional on alpha injectivity, block membership, branch label formula, and
the base endpoint label.

No hidden claim of no-extra terminal-minimum coverage, exact source-derived
count, pole order, normal crossings, or RLCT extraction was found.

## Commands Run

- `cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5CountDatumBridge.lean`
- `cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`
- `git diff --check`

## Residual Risk

The adapters remain conditional.  In particular, `(p, alpha)` injectivity,
terminal Eq5 payloads, branch construction, and no-extra coverage are still
explicitly unproved.
