**Q1 Verdict:** Mostly yes, but “conormal free” is not quite the analytic interface.

RLCT `= c/2` is real-analytic: it uses constant-rank/Morse-Bott-type normal coordinates for `K = ‖F‖²`.
A worthwhile algebraic intermediate is: at a real smooth fibre point, `dF` has rank `c`, so after choosing `c` output coordinates, `F` is locally a submersion onto `ℝ^c`.
Formal completions / regular sequences de-risk only the algebraic smoothness story; they do not prove the RLCT value.

**Q2 Verdict:** If the standard-smooth chart is already banked, this should be bounded; otherwise it is a sub-wall.

The hard part is not `free_cotangent`; it is connecting the DLN presentation `mult(A)-B` to the chart relations and proving the rank is exactly `c` at the chosen point.
If your regular-local proof already constructs/uses a standard-smooth chart at the same prime, reuse that certificate.
If it only proves abstract smoothness after several equivalences, extracting a usable DLN conormal statement may be painful bookkeeping.

**Q3 Verdict:** Do not bet on a clean Mathlib “regular system of parameters extends equations” route.

A regular local ring gives parameters for its maximal ideal, not automatically generators for the ambient fibre ideal.
To say “the fibre equations extend to parameters” is a regular-immersion/conormal statement, essentially the lci API Mathlib lacks.
Without Koszul or regular-immersion infrastructure, proving a literal length-`c` regular sequence is likely bespoke commutative algebra.

**Q4 Verdict:** The hidden logical hole is realness and presentation, not algebraic smoothness.

You need a real smooth zero of `K`, not merely a closed point over algebraically closed `k`.
You also need the cited analytic theorem stated for the actual square loss `Σ F_i²` with redundant equations, or after an explicitly justified rank-`c` coordinate extraction.
Global upper bound needs the convention `rlct_global ≤ rlct_local_at_that_point`; make that part of the cited interface.

Biggest risk: you prove a beautiful algebraic smoothness theorem about the fibre scheme over `k`, but the cited analytic theorem needs a concrete real analytic map `F : ℝ^N → ℝ^r`, a real point on `F⁻¹(0)`, Jacobian rank `c` there, and the rule converting that local model into the global upper bound. If that interface is not stated exactly, the regular-sequence work will not connect to R2.