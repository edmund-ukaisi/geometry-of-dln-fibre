Do NOT use web search. Answer from mathematical reasoning only. Be concise and adversarial: your job
is to FIND A COUNTEREXAMPLE or a genuine obstruction, not to confirm. Mark each claim FACT or INFERENCE.

SETTING (exact algebra over R). L matrices C^(1),...,C^(L), C^(j) of size M^j x M^{j+1}; L+1 widths
M^1..M^{L+1}. f(C) = || C^(1)...C^(L) ||^2_Frob, a sum of squares. We resolve { product = 0 } at the
origin to compute the real-log-canonical-threshold (rlct = sup{c : |f|^{-c} locally integrable}).

Strata of {prod=0}: t_j = rank(C^(1)...C^(j)), weakly decreasing, t_j <= min(t_{j-1}, M^{j+1}),
t_0=M^1, t_L=0. Codim of stratum S(t) is Mval(t) = sum_{j=1..L} (t_{j-1}-t_j)(M^{j+1}-t_j).
Claimed: rlct(f at 0) = (1/2) min_{admissible t} Mval(t).

THE PROPOSED RESOLUTION (per-node recursion): blow up the rank-defect of the FIRST factor C^(1) (a
coordinate-subspace center after a det-1 Schur straighten that normalizes a unit pivot to a hard 1);
core∘φ = u^2·(residual), Jacobian |det Dφ| = u^{c-1} for a codim-c center; descend on the Schur-reduced
chain (smaller matrix-chain core), base case L=1 (smooth sum of squares, rlct = M^1 M^2 / 2).

I want you to attack THREE specific failure modes and tell me if any GENUINELY breaks the claim
rlct = (1/2) min_Adm Mval, or holds only under a scoped condition you must name:

(i) MISSED / SPURIOUS STRATUM. The first-factor blow-up center {rank C^(1) <= s} is NOT contained in
{prod=0} (a point with C^(1) rank-deficient but product nonzero is in it). Codim of {rank C^(1)=s} is
(M^1-s)(M^2-s), which for s = min(M^1,M^2)-1 can be as small as 1 -- far below min_Adm Mval. Does
blowing this up create an exceptional divisor of ratio (M^1-s)(M^2-s)/2 that UNDERCUTS (1/2) min_Adm
Mval? Or is it harmless, and exactly why? Conversely, can the first-factor-only recursion MISS an
admissible stratum (one whose rank drop is caused by a LATER factor, not the running first factor), so
the atlas inf OVER-estimates the rlct?

(ii) MULTIPLICITY-2 DIVISOR. The lower bound needs k_E = 1 (core vanishes to order exactly 2) on every
exceptional divisor; axisRatio = (h+1)/(2k), so a k_E=2 divisor HALVES the ratio. Can any blow-up in
this recursion -- a deep stratum, a rank drop >= 2 at one layer, a composed sequence of blow-ups, or a
terminal residual -- produce an exceptional divisor along which f pulls back with u-order 4 (k_E=2)
instead of 2? Think about the (x^2+y^2)^2 phenomenon: is there a center where the strict transform of f
is a SQUARE of a sum of squares?

(iii) NON-TERMINATION / STUCK DESCENT. Is there a chain and a node where the Schur-reduced residual is
a NONZERO core but sum(M') = sum(M) (the descent measure fails to drop), or where a non-terminal node
has no valid hard-1 pivot, so the recursion loops or gets stuck?

For each: a concrete counterexample (give the M and the point), or a proof it cannot happen + the
scoped condition that an implementation must respect to stay sound.
