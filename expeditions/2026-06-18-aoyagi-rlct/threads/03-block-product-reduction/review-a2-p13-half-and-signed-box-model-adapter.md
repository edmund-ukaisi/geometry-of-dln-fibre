# Review - A2 p.13 half bound and signed-box model adapter

Date: 2026-06-25.

Reviewer: xhigh independent reviewer Hume the 4th.

## Verdict

No blocking issues found.

## Checks

- The constants are correct: the half-bound follows from
  `L_clean <= 2 * L_lit`, the supplied-loss handoff gives `c/2`, and the
  signed-box adapter gives `c/K`.
- The Lean theorem names match their content.
- The p.13 source fidelity is sound: the notes use the displayed block
  `C1-Er`, `-F2`, `-F3`, and `prod_s C^(s)-F3F2`, and treat the factor-`2`
  comparison as finite square-sum bookkeeping rather than a source-printed
  analytic theorem.
- The docstrings and notes do not claim original DLN loss comparison, analytic
  chart construction, Jacobian/prior transport, normal crossings, pole order,
  or RLCT extraction.

## Nonblocking Suggestions

- The supplied-loss wrapper is true with `c >= 0`, but downstream
  integrability will usually need a strictly positive constant.
- The signed-box model-loss adapter should be read as a one-way comparison
  theorem using `modelLoss <= K * loss`; it is not a two-sided comparability
  result.
