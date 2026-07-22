<task>
I am elaborating the PATH-LEVEL / cover step of the resolution in Miki Aoyagi (2023), "Consideration on
the learning efficiency of multiple-layered neural networks with linear units" (pp.6, 22-26), into a
template a formaliser can render statements from. I need an INDEPENDENT read of how the chart family
covers, because the paper is terse here. Adjudicate the reading; do not rederive the whole proof.

FACTS (from the paper, take as ground truth):
- Hironaka gives a proper analytic g: Q -> V (V a neighbourhood of the singular point) with, in each
  local chart U with coordinates (u_1,...,u_d):  K(g(u)) = u_1^{2k_1}...u_d^{2k_d}  and
  |g'(u)| phi(g(u)) = u_1^{h_1}...u_d^{h_d}, and then (p.6, the "boxed rule")
      lambda = min_U min_{1<=j<=d} (h_j+1)/(2k_j),     theta = max_u Card{j: (h_j+1)/(2k_j)=lambda}.
- g is built as a composition of blow-up charts along a root-to-leaf path of a recursive blow-up tree.
  Each blow-up of a codim-c centre has c charts (indexed by which centre-coordinate is the "pivot"
  that is NOT divided out); in the pivot chart, |Jac| = u^{c-1} (a monomial) and the other c-1 centre
  coords x_i become x_i = u * x_i'. I have verified (exact algebra): the composite Jacobian is a PURE
  MONOMIAL prod_{s,k} u_{s,k}^{M_{s,k}-1} (each blow-up contributes u^{codim-1}; the intervening Q,P
  clearing matrices are det-1 shears, contributing 1). At a terminal chart the loss is
  b_1^2 + ... + b_M^2 with b_1 | ... | b_M (a divisibility chain of monomials), = b_1^2 * (unit-valued
  function that equals 1 at the origin).

THE QUESTIONS:
(1) COVER. How does the family of terminal charts (all root-to-leaf paths of the blow-up tree)
    cover a neighbourhood of the singular point, and what does "cover a.e. (up to measure zero)"
    exclude exactly? Is the correct picture: the charts form an OPEN COVER of the blown-up manifold Q,
    push down via g to cover V EXCEPT the (lower-dimensional, measure-zero) exceptional divisors /
    blow-up centres? Or must one restrict each chart to a SECTOR (e.g. {|x_pivot| >= |x_other|}) to get
    an a.e.-DISJOINT partition so that the integral over V is a sum over charts WITHOUT overcounting?
    Which is needed to justify  integral_V = sum_charts integral_chart  ?
(2) MIN-OVER-CHARTS. Given the cover, why is the GLOBAL log-canonical threshold the MIN over charts of
    the per-chart threshold (rather than, say, a sum or the max)? State the convergence argument:
    integral_V |F|^{-c} phi dw < infinity  iff  c < (per-chart threshold) for EVERY chart. Is the min
    the correct aggregator for lambda, and separately, what is the correct aggregator for the ORDER
    theta (the pole multiplicity)?
(3) WHAT THE PAPER LEAVES IMPLICIT. Given only "we use a recursive blow-up process" and the boxed rule,
    which of (1)-(2) does the paper actually PROVE versus ASSERT/cite as standard resolution theory?
    Name the single step most likely to be a hidden gap a formaliser must reconstruct rather than cite.
</task>

<output_contract>
Three numbered sections (1),(2),(3), each <= 200 words. For each: the concrete reading, then
"CONFIDENCE: high|medium|low" + strongest reason. If (1) genuinely admits both the open-cover and the
sector-partition reading, give both and say which is standard in singular-learning-theory RLCT
computations (Watanabe/Aoyagi lineage). End with one line "SHARPEST GAP" naming the step most likely to
need reconstruction.
</output_contract>

<grounding_rules>
Reason from the stated facts + standard resolution-of-singularities / RLCT theory. Distinguish
"the paper proves this" from "this is standard and cited" from "this is a gap the paper skips". Do not
invent notation. If my transcription of the boxed rule or the Jacobian claim would be internally
inconsistent, flag it (that is the finding).
</grounding_rules>
