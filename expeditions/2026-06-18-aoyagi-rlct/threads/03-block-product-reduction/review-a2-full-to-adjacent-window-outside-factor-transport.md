# Review - A2 full-to-adjacent-window outside-factor transport

Reviewer: xhigh `Mencius the 4th`.

## Findings

None.

## Checks

- The generic split keeps the order
  `P(j,hi) * (P(hi,lo) * P(lo,i))`.
- The middle replacement theorem substitutes only the adjacent two-edge
  factor, leaving both outside products explicit.
- The Case 2 bridge conclusion still has the left outside product and right
  outside product around the selected-entry matrix.
- The reproduction and statement card include the necessary nonclaims about
  no outside-factor identity or absorption, no source chart, no analytic
  transport, and no RLCT extraction.

## Residual Risk

The theorem is finite product bookkeeping.  It does not construct the source
or analytic hypotheses needed to make the outside factors harmless in a
concrete chart.
