<task>
Setting: resolving finiteness of a deep-linear-network loss integral by a layer-peeling recursion.
A "chain" is a width vector M = (M_0, M_1, ..., M_L) of positive integers (L+1 nodes). The loss is
||A_0 A_1 ... A_{L-1}||_F^2 (A_j is an M_j x M_{j+1} real matrix), integrated over a box, raised to -c'.
We want finiteness for all c' < (1/2)*minAdm(M), where minAdm is defined by the recursion:

  minAdm(M) = 0                          if L = 0 (single node)
            = M_0 * M_1                  if L = 1 (two nodes, a free matrix; loss = sum of squares)
            = min over t in [0, min(M_0,M_1)] of  (M_0 - t)(M_1 - t) + minAdm(redChain(t, M))   else
  where redChain(t, M) = (t, M_2, M_3, ..., M_L)   (peel the leading layer keeping pivot rank t).

The recursion peels the leading layer at a pivot cut t (>=1), giving a corank block Gamma of shape
p x q with p = M_0 - t, q = M_1 - t (block "charge" = p*q). Gamma couples to the deeper factor
Q_b, which is the q non-pivot rows of node 1 pushed through the deeper product of widths (M_2,...,M_L);
its generic rank is r = min(q, min(M_2,...,M_L)). The map Gamma |-> Gamma * Q_b has linear rank p*r.

Two ANALYTIC bricks are available and PROVEN for one peel of a p x q corank block coupled to an
arbitrary non-negative deeper core W(z) >= 0 through Gamma's Frobenius energy:

  (regime A)  if c' > p*r/2 and W(z) > 0 STRICTLY and Q_b has FULL ROW RANK (r = q):
              the peel shifts the exponent c' -> c' - p*q/2 and hands the deeper integral
              ∫ (W z)^{-(c' - p*q/2)} to the induction hypothesis (box-finiteness of the strictly
              shorter chain redChain(t, M)); a soundness gate minAdm(M) <= p*q + minAdm(redChain(t,M))
              makes the shifted exponent land below (1/2)*minAdm(redChain(t,M)).

  (regime B)  if c' < p*r/2 (effective Morse dimension = p*r, the linear rank of Gamma |-> Gamma*Q_b):
              the block Morse-dominates and the integral is finite directly, for ANY W(z) >= 0
              (the flat kernel directions of Gamma, dimension p*(q-r), integrate to a bounded constant).

A THIRD, more expensive object (a "monomial terminal", a normal-crossing / toric endpoint) is only
needed when NEITHER regime covers a chart: i.e. the chart is rank-deficient (r < q) AND its effective
Morse dimension p*r is below the local threshold, p*r < minAdm(M_cur), so there exists
c' in (p*r/2, (1/2)*minAdm(M_cur)) covered by neither A nor B.

<questions>
Q1. Is the effective Morse dimension of the coupled corank block correct as p*r (r = min(q, min(M_2..M_L)))?
    i.e. is the linear rank of the map Gamma (p x q) |-> Gamma * Q_b equal to p * rank(Q_b), with the
    p*(q-r) kernel directions genuinely flat in ||Gamma*Q_b||^2 (hence a bounded box integral)?

Q2. Derive independently the exact condition on (chain M_cur reached in the recursion, cut t) under which
    the monomial terminal is genuinely load-bearing (neither regime A nor B covers some admissible c').
    Give the condition in closed form.

Q3. For the specific chains M = (3,3,4), (2,2,2,2), (3,3,3,4): enumerate every chart (M_cur, t) the
    recursion visits and state whether ANY is load-bearing per Q2. (i.e. does the monomial terminal ever
    get reached for these three chains, or are they entirely covered by regimes A and B + the L=1
    free-matrix base?)

Q4. If the three chains are fully covered by A/B/base, then the statement "(1/2)*minAdm(remChain) <=
    monomialThreshold(terminal)" is vacuously uniform on them (no monomial terminal reached). Is that a
    sound reading? And separately: for chains that ARE load-bearing (e.g. (3,4,2) at t=1: p=2,q=3,r=2,
    p*r=4, minAdm=6, so c' in (2,3) is uncovered), what is the cleanest way to see whether the toric
    monomial endpoint achieves threshold >= (1/2)*minAdm there (i.e. does the resolution achieve
    rlct = (1/2)*codim, Aoyagi's theorem, at that leaf)?
</questions>
</task>

<output_contract>
Answer Q1-Q4 in order, terse. For Q2 give the closed-form condition. For Q3 give a yes/no per chain with
the reasoning. For Q4 give a yes/no soundness call + the cleanest discriminating argument. Flag any place
my setup (effective Morse dim = p*r, the load-bearing condition) is WRONG.
</output_contract>
