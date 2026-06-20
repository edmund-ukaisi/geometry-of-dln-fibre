# Review - A4 principalized source-chart actual-width boundary

Reviewed objects:

- `sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary_withFiniteCenterIdeal`
- `reproduction-case2-principalized-source-chart-actual-width-a4.md`
- `statement-card-a4-principalized-source-chart-actual-width.md`

Verdict: no blocking source/math or Lean API issue found.

The theorem is a safe conjunction of the existing actual-width terminal
original-row boundary with finite residual-block center facts for the displayed
source-coordinate chart.  The statement keeps the important boundaries
visible:

- `chartFamily` remains supplied.
- The following matrix `F` remains arbitrary supplied data.
- Actual-width exhaustion is exactly `n(S+1)=J+1`.
- The center conclusion is only the finite residual-block center value ideal
  `Ideal.span {...} = Ideal.span {u}`.

The theorem does not claim terminal-product principalization, chart coverage,
source production of `C'^(S+1)`, production of the following product, Jacobian
arithmetic, normal crossings/RLCT extraction, termination, transition
invariance, or repair of the printed Case 2 vector mismatch.

Nonblocking wording suggestions were applied:

- the reproduction now says "finite residual-block center ideal" rather than
  "finite blow-up center";
- the statement card says "Lean exposes" rather than "Lean should expose";
- the theorem name was shortened to `withFiniteCenterIdeal` to avoid a new
  long-line linter warning while keeping the finite-center scope visible.
