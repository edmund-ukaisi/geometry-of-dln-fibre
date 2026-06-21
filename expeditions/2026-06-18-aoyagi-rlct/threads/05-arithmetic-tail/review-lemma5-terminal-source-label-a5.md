# Review - Lemma 5 Terminal Source Label

Reviewer: Singer (xhigh read-only subagent).

Status: pass; no blocking findings.

## Scope Reviewed

- `lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`
- `reproduction-lemma5-terminal-source-label-a5.md`
- `statement-card-a5-lemma5-terminal-source-label.md`
- Expedition ledger updates in `priorities.md`, `thread.md`, `synthesis.md`,
  `theorem-ledger.md`, and `claims.md`.

## Findings

No findings.

## Audit Notes

`aoyagiLemma5_terminalSourceIndex_pos` soundly proves
`1 <= C.point ell - 1` from `1 <= ell`, positivity of `C.point 0`, and strict
cutpoint monotonicity.

`aoyagiLemma5_terminal_actualWidthLabel_of_lastPoint` uses only the explicit
terminal source range `C.point ell <= L + 1` and width positivity
`1 <= n(C.point ell)` for the label `k=1`.

`aoyagiLemma5_terminal_intervalValue_mem_introducedLabelFinset_of_terminalZero`
relies on the supplied equality `T(C.point ell - 1)=0` and the existing
terminal singleton theorem.  It does not construct a source branch.

The reproduction, statement card, and ledgers avoid the forbidden overclaims:
no terminal branch construction, source-realisation proof, terminal-label
exactness, classifier coverage, injectivity, back-to-label coverage, pole
order, normal crossings, or RLCT extraction.

## Verification

The reviewer independently ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean
```

from the `lean/` project root, and it passed.

## Residual Risk

This slice is intentionally narrow.  It does not reduce the larger A5 gaps
around source-backed terminal branch construction or terminal-label exactness.
