# Review - Theorem 2 Eq5 terminal-order bridge

Date: 2026-06-23.

Reviewers: Darwin and Hypatia, xhigh-effort subagents; controller follow-up
after implementation.

## Verdict

Pass as a conditional supplied-boundary bridge.

## Source-Fidelity Check

The slice is faithful only because it does not claim to construct Aoyagi's Eq5
endpoint family or prove Lemma 5 exactness from the source.  It packages the
already-supplied Eq5 endpoint block-width payload, extracts the existing exact
terminal-count theorem, and feeds that equality into the existing A6
exact-count sockets.

The payload and wrapper names include `Supplied`, and the file header states
the open obligations.  The final-boundary wrappers use the same selected
cutpoints `P.cut` carried by the supplied Eq5 payload, rather than accepting a
separate cutpoint object.

## Lean/API Check

Focused build passes:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.Theorem2Eq5TerminalOrderBridge
```

The proof path is direct:

```text
P.terminalMinimumLabels_card_eq_theorem2OrderFormula
```

is passed to the corresponding exact-count theorem in
`Theorem2TerminalOrderEqualityBridge.lean`.

The module is imported from `lean/DLNFibre.lean`, so a full `scripts/lb`
build covers it.

## Nonclaims

- No construction of Eq5 endpoint families or terminal Eq5 payloads.
- No source proof that Aoyagi's printed Eq3/Eq4/Eq5 families cover all
  terminal minima.
- No source-backed Lemma 5 exactness, classifier, back-to-label,
  branch-label injectivity, or no-extra coverage.
- No selected cutpoint existence, rank-width proof, active-ratio lower-bound
  proof, or displayed-ratio chart-count theorem.
- No global chart production, chart coverage, transition regularity,
  normal-crossing certificate construction, or Case 1/Case 2
  source-production progress.
- No citation of Aoyagi Lemma 1, Aoyagi Theorem 4, regular-coordinate
  additivity, or analytic ideal transport.
- No pole-order or RLCT theorem beyond the explicit normal-crossing
  extraction hypothesis.

## Residual Risk

The bundled payload hides a large hypothesis list behind one argument.  The
`Supplied` name and statement card are intended to keep that boundary visible.
