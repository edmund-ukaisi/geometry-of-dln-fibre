# Review - Theorem 2 terminal order equality bridge

Date: 2026-06-23.

Reviewer: Banach, xhigh-effort subagent.

## Verdict

Pass.

## Findings

No blocking findings were found.  The Lean scope is correct:
`Theorem2TerminalOrderEqualityBridge.lean` accepts

```text
TC.terminalMinimumLabels.card = data.theorem2OrderFormula
```

directly and composes it only with supplied minimum, order, and chart-count
hypotheses.  It does not prove A5 exactness, chart production, or analytic
extraction.

The active-ratio and chart-count variants use the existing finite certificates
in the right direction.  The final-boundary wrappers add only selected-width
provenance plus the explicit normal-crossing extraction hypothesis.

The reproduction note treats the terminal equality as input and keeps A5
source exactness, chart production, and RLCT obligations deferred.  The
`_card_eq` suffix distinguishes this direct-equality bridge from the existing
bridge deriving equality from injectivity plus an upper bound.

## Verification

The reviewer ran:

```text
scripts/lb DLNFibre.DLN.Aoyagi.Theorem2TerminalOrderEqualityBridge
scripts/lb DLNFibre
scripts/sorries
git diff --check
```

The focused and full builds passed with unrelated pre-existing linter
warnings.  `scripts/sorries` reported `0 sorry`, `0 #exit`,
`0 native_decide`, and `0 axiom`.

## Residual Risk

The exact terminal count remains a supplied input to this module.  This bridge
should not be described as source-backed Lemma 5 exactness, chart production,
normal crossings, pole order without A0, or RLCT extraction.
