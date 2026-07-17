<task>
Adjudicate one convergence question about an iterated integral arising in a deep-linear-network
(DLN) real-log-canonical-threshold computation. Give a firm FINITE vs DIVERGENT verdict with an exact
threshold, plus the mechanism.
</task>

<context>
Let Q = A_1 · A_2 · … · A_ℓ be a PRODUCT of ℓ ≥ 2 real matrices ("deep linear" composite), where each
factor A_i is a FREE parameter matrix ranging over a bounded box (say entries in [-1,1]) with Lebesgue
measure. Widths: A_1 is n × m_1, A_2 is m_1 × m_2, …, so Q is n × q. Assume the widths permit Q to be
generically full row rank n (i.e. all intermediate widths m_i ≥ n and q ≥ n); if some intermediate
width m_i < n, Q is structurally rank-deficient.

Consider the OUTER integral over ALL the factor parameters A = (A_1,…,A_ℓ):

    J = ∫ det( Q(A) · Q(A)ᵀ )^{ -a/2 } dA          (a ≥ 1 a fixed positive integer, a/2 the exponent)

integrated against the rank-drop boundary { A : rank Q(A) < n }.

BASELINE FACT (please confirm): for a SINGLE FREE matrix Q of shape n × q (no product structure, ℓ=1),
the analogous integral ∫ det(QQᵀ)^{-a/2} dQ over a bounded box is finite iff a < q − n + 1 (the classical
Wishart / determinantal threshold: rank-r stratum has codim (n−r)(q−r), the r=n−1 boundary binds).
</context>

<question>
For the PRODUCT Q = A_1 ⋯ A_ℓ (ℓ ≥ 2), is J finite under the same a < q − n + 1 baseline, OR does the
composite/product parametrization change the convergence threshold?

Specifically:
1. Take the two-factor case Q = L·R with L an n×n SQUARE factor and R an n×q factor. Compute det(QQᵀ) in
   terms of det(L) and det(RRᵀ). What extra divisor does the pullback of {det(QQᵀ)=0} acquire in L-space,
   what is its codimension and the vanishing order of det(QQᵀ) along it, and what is the resulting
   convergence threshold on a for the L-integral alone? Compare to the free baseline a < q − n + 1.
2. More generally, is the map A ↦ Q = ∏A_i SUBMERSIVE onto n×q matrix space along the rank-drop locus, or
   does it fail to be submersive there (so that the pushforward of Lebesgue measure acquires a density that
   blows up relative to the free-matrix measure)? What does that do to J vs the free baseline?
3. Is this composite-Wishart outer integral a "tractable classical Wishart integral" reducible by peeling
   one factor and applying an induction on a shorter chain, or is there genuinely-new content at the
   rank-drop boundary that a single free-matrix Wishart bound does not capture?
</question>

<output_contract>
- LEAD with: FINITE-under-free-baseline, or THRESHOLD-LOWERED (diverges where the free baseline would
  converge).
- The exact convergence threshold on a for the two-factor square-L case, with the codim + vanishing-order
  power count.
- Whether A ↦ ∏A_i is submersive along the rank-drop; one sentence on the measure-pushforward consequence.
- Whether a one-factor-peel induction reduces J to a classical free-matrix Wishart, or leaves residual
  boundary content.
- Mark each claim [EXACT] (algebra/power-count you can defend) vs [HEURISTIC].
</output_contract>

<grounding_rules>
- Exact algebra / power counting, not vibes. For the square-L case det(QQᵀ)=det(L)²det(RRᵀ) is exact — use it.
- Near a codim-1 hypersurface {f=0} with f vanishing to transverse order k, ∫ |f|^{-s} converges iff s·k < 1.
- Do not assume the answer; derive the threshold from the geometry.
</grounding_rules>
