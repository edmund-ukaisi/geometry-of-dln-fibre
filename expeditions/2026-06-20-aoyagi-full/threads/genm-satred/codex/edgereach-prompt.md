<constraints>Do NOT run any shell commands, file reads, or tools. The problem is FULLY SPECIFIED below;
answer from mathematical reasoning ALONE. Any filesystem exploration will fail (read-only exec).</constraints>

<task>
Adjudicate one truth-value about an RLCT (real-log-canonical-threshold) reduction. Argue whichever way it
goes; I have NOT told you the expected answer.

Deep-linear-network setup. A "chain" M=(M0,M1,...,ML) of positive integer widths; parameters are matrices
A0 (M1xM0), A1 (M2xM1), ..., and prod(M) = A_L...A1 A0. The box integral
   RMBTF(M)(c) : ∫_{all Ai in [-1,1]-boxes} frobSq(prod(M))^{-c} dA  <  ∞    iff   c < (1/2) minAdm(M),
where minAdm is the recursion minAdm(M) = min_{0<=t<=min(M0,M1)} [ (M0-t)(M1-t) + minAdm(redChain t M) ],
redChain t M = (t, M2, ..., M_last). (This equals the paper's codimension / 2, Aoyagi.)

At a "cut" u with corank width b = M1 - u = 1 (the "edge") and pivot deficit a = M0 - u >= 1, after a
change of variables the leading layer becomes z~0 = X . Y, where X = [P | B12] is u x M1 (full row rank u,
P invertible u x u, B12 the u x 1 cross block) and Y = [z0 ; A_cor] is M1 x M2 (z0 the u x M2 pivot rows,
A_cor the 1 x M2 corank row), all over boxes. Then frobSq(P.Q~p) = frobSq(z~0 . Z_deep) =
frobSq(prod(redChain u M) with leading layer replaced by z~0). The reduced object to bound is
   EDGE(c) := ∫_p |v'(p)|^{-a} · ∫_{X,Y} frobSq(z~0(X,Y) . Z_deep(p))^{-(c - a/2)}    (b=1)
where |v'(p)|^{-a} is a fragile-direction weight with ∫ over the sphere finite because a < u, and Z_deep
depends on the same deep parameters as Y.

Two established facts: (F1) the TRUE finiteness threshold of EDGE(c) is c < (1/2) minAdm(M) in all cases
(the object equals RMBTF(M) restricted to the full-measure chart {P invertible}). (F2) The pushforward
density rho(z~0) of the map (X,Y) -> X.Y is NOT uniformly bounded; a NAIVE pointwise fold
rho <= const · frobSq^{-A/2} with density order A = max_{1<=j<=min(u,M2)} j*(M2-1-j) reduces EDGE to
RMBTF(redChain u M)(c - a/2 + A/2), which reaches the true threshold IFF A <= 2*Delta + a, where
2*Delta = minAdm(redChain u M) - minAdm(M). A finite check finds A > 2*Delta + a for a MAJORITY of edge
cells (the naive pointwise fold undershoots).

QUESTIONS.
Q1. Given (F1) (true threshold is always (1/2)minAdm(M)) but the naive pointwise fold undershoots for most
    edge cells, what is the cleanest CORRECT route to prove EDGE(c) < ∞ for c < (1/2)minAdm(M)? Options:
    (a) a JOINT rank-sector / determinantal-stratification resolution (stratify rank(z~0)=r, reduce each
        stratum to a DIFFERENT shorter chain redChain(u') with u'=u+(deficit), min over strata = minAdm(M));
    (b) a single-chain reduction to RMBTF(redChain u M)(c-a/2) with a LOGARITHMIC/delta-slack correction
        absorbing the marginal shortfall; (c) something else. Rank them.
Q2. Does the coupled route (this X.Y structure) INTRODUCE, AVOID, or merely RELOCATE the corank-one
    "tie logarithm" that a separate/decorated route (integrating the corank block on its own, giving the
    scalar model ∫_{[-1,1]^2}(w+x^2 y^2)^{-p} ~ w^{1/2-p} log(1/w)) is known to produce? Is there a clean
    (no-log, no-delta) single-chain reduction, or is a log/delta-slack or the joint rank-sector
    unavoidable here?
Q3. If the joint rank-sector (a) is needed, is it a genuine analytic escalation over the naive fold, or
    does the shifted exponent (c - a/2 instead of c) plus the a<u sphere-disposal make the strata min
    reach EXACTLY (no residual log)? State the exponent bookkeeping.
</task>

<output_contract>
Answer Q1-Q3 in order. Q1: rank the routes, 1 line each + why. Q2: VERDICT (introduces/avoids/relocates)
+ 3-5 sentences. Q3: VERDICT (genuine escalation / clean strata-min) + the exact exponent bookkeeping.
End with one line: "CLEANEST EDGE ROUTE: ___".
</output_contract>

<grounding_rules>
Distinguish PROVEN (from F1/F2 or exact bookkeeping you show) from INFERENCE. Do not assume my expected
answer. If a route needs an extra hypothesis (e.g. a<u, or a uniform singular-value bound), name it.
</grounding_rules>
