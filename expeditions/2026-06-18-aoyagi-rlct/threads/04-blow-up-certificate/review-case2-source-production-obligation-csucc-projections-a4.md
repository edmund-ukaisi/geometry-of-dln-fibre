# Review - Case 2 obligation Csucc projections

Date: 2026-06-22.

Reviewer: xhigh scout Hilbert the 2nd.

## Verdict

Pass after one documentation precision fix.

## Finding

Hilbert found that the actual-width projection was documented as if it only
consumed `Csucc_eq_formula`, while the Lean proof also consumes the supplied
terminal-row field

```text
ob.actualWidth_Cterm_eq hwidth.
```

The Lean theorem was correct, but the docstring and several ledger summaries
understated the supplied-data dependency.

## Resolution

The Lean docstring, reproduction, statement card, `claims.md`, and
`priorities.md` now state that:

- `continuing_Csucc_tail_eq_original` consumes `Csucc_eq_formula` and the
  existing next-tail restriction identity;
- `actualWidth_Cterm_eq_originalRows_Csucc` consumes the supplied
  `actualWidth_Cterm_eq` branch field, the actual-width collapse identity, and
  `Csucc_eq_formula`.

No theorem-name mismatch, quiver leakage, or citation-boundary issue was
found.  The proofs remain supplied-obligation consumers only and do not
construct `Csucc`, `C'^(S+1)`, suffixes, charts, transition data, normal
crossings, pole order, or RLCT.
