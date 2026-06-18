<task>
Adjudicate a discrete-optimization support-localization claim and audit a proposed proof of it.

SETUP. Fix N >= 1 and a weakly-increasing positive integer vector d' = (d'_0, d'_1, ..., d'_N),
i.e. d'_0 >= 1 and d'_0 <= d'_1 <= ... <= d'_N (all integers). Consider the integer program:

  minimise  Phi(e) := sum_{i=1}^{N} (e_i - s_i)^2  ,   s_i := d'_0 - d'_i   (note s_i <= 0)
  over      e = (e_1,...,e_N) in Z^N,  e_i >= 0,  sum_{i=1}^N e_i = d'_0.

(This equals, up to an additive constant and factor 2, minimising the quadratic form
 G_d(e) = sum_{1<=j<=i<=N} e_i (e_j + d'_j - d'_{j-1}) over the same feasible set.)

Define the integer  m := max{ l in {1,...,N} : sum_{i=0}^{l} d'_i  >=  l * d'_l }.

QUESTIONS.
(Q1) Is m well-defined: is the set {l : sum_{i=0}^{l} d'_i >= l d'_l} always nonempty (does l=1 always
     qualify), and is "take the max" the right reading (could the qualifying set be non-contiguous, and
     does that matter for the definition)?
(Q2) Prove or refute: EVERY minimiser e* of the program above satisfies e*_i = 0 for all i > m.
(Q3) For the m<N case, is the strict separation  m * d'_{m+1} > sum_{i=0}^{m} d'_i  a theorem
     (consequence of m being the max), and is it the load-bearing inequality for (Q2)?

A PROPOSED PROOF OF (Q2) TO AUDIT (find any gap):
  Suppose a minimiser e* has e*_k >= 1 for some k > m. Let u_i := e*_i - s_i = e*_i - d'_0 + d'_i.
  Move one unit from coordinate k to a coordinate j <= m chosen to minimise u_j over {1..m}; call the
  result e'. Then Phi(e') - Phi(e*) = 2(u_j - u_k + 1). Claim u_j - u_k + 1 < 0, i.e. u_k - u_j >= 2,
  giving a strict decrease and contradicting minimality. Bounds:
    - u_k >= 1 + d'_k - d'_0 >= 1 + d'_{m+1} - d'_0   (since e*_k>=1 and d'_k >= d'_{m+1});
    - u_j = min_{1<=j<=m} u_j <= (1/m) sum_{j=1}^m u_j <= S_m/m - d'_0, where S_m = sum_{i=0}^m d'_i
      (using sum_{j<=m} e*_j <= d'_0 and sum_{j=1}^m d'_j = S_m - d'_0);
    - hence u_k - u_j >= 1 + d'_{m+1} - S_m/m, which is > 1 by the separation m d'_{m+1} > S_m;
    - u_k - u_j is an integer > 1, so >= 2.  QED.
</task>

<output_contract>
- Verdict on (Q1), (Q2), (Q3): each TRUE / FALSE / NEEDS-CONDITION, with reasoning.
- A line-by-line check of the proposed proof: flag any non-rigorous step (esp. the "average bound" on u_j,
  the integer-gap rounding, the j<=m membership of the chosen transfer target, and feasibility/nonneg of e').
- Any hidden hypothesis the argument silently uses (e.g. positivity d'_0>=1, weak-increase, m<N).
- If you find a counterexample to any claim, give the explicit d' and the minimiser.
- Mark each statement as PROVEN / PLAUSIBLE / UNCERTAIN (fact vs your inference).
</output_contract>

<grounding_rules>
- Exact integer/rational arithmetic only. No floating point.
- Do not assume e* is unique. Do not assume the continuous relaxation transfers without justification.
- If a step needs e* to be a minimiser vs any feasible point, say which.
- Withhold nothing about gaps; this is a red-team, not a rubber stamp.
</grounding_rules>
