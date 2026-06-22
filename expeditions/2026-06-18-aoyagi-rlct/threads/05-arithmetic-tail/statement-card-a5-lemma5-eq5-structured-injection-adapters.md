# Statement card - A5 Lemma 5 Eq5 structured injection adapters

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_countDatum_injOn_of_pAlpha_injOn`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumCountDatum_injOn_of_eq5OwnBlock_pAlpha_injOn`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_none_ne_some_of_terminalEndpointLabel_and_nonbaseBlock`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_eq5AlphaIndexed_nonbase_terminalEndpointBase`

## Claim

Eq5 own-block value formulas turn supplied `(p,alpha)` injectivity into
injectivity of the counted-datum map

```text
label |-> some (pOf label, T label label.1).
```

Separately, a supplied terminal-endpoint base label is distinct from every
nonbase Eq5 branch label whose first component lies in a selected block.

## Proved

Finite injectivity adapters only.

## Assumed

The Eq5 payloads, own-block source-row membership, supplied `(p,alpha)`
injectivity on the label set, the terminal endpoint base label, and nonbase
branch block membership.

## Deferred

Source construction of Eq5 branch families, source proof of `(p,alpha)`
injectivity, counted-datum back-to-label coverage, no-extra terminal-minimum
coverage, exact terminal-minimum count from source, pole order, normal
crossings, and RLCT extraction.

## Review

xhigh `Newton` passed the slice with one low doc-status correction, now fixed.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5CountDatumBridge.lean`
- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`
- `lake build DLNFibre.DLN.Aoyagi.Lemma5Eq5CountDatumBridge`
- `lake build DLNFibre.DLN.Aoyagi.Lemma5Eq5TerminalClassifier`
- `lake build DLNFibre`
- `scripts/sorries`
- `git diff --check`
