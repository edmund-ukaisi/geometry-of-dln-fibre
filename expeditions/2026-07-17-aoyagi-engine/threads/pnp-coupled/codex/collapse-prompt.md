<task>
Real-analytic RLCT of F = ||C1 C2 ... CL||_Frob^2 (product of real matrices) at 0. Known value:
rlct_0 = (1/2) min_t Mval(t). Focus on ONE algebraic joint at a coupled corank>=2 minimizer.

After a Schur block-elimination (unit pivot, unipotent-polynomial Q1,Q2, ideal-preserving) the core splits:
  F_core = ||T||^2 + ||Delta*S||^2,
where T is the retained-rank "pivot" part (has a coordinate entry = 1, the cleared unit), Delta is a
k x k residual block whose entries are FREE local coordinates (= m_ij - bilinear, m_ij free), S is a
deeper free block. This peel is ideal-preserving but does NOT preserve the sum-of-squares value.

To resolve ||Delta*S||^2 the construction does a RADIAL blow-up of the coordinate subspace {Delta=0}:
in a chart Delta = u * Dbar (u a scalar exceptional coord, Dbar normalized), so ||Delta*S||^2 = u^2 * G
with G = ||Dbar*S||^2. Then it JOINS the pivot exceptional q (from ||T||^2 = q^2 * U_T, U_T(0)=1) with u:
blow up {q=u=0}, q-chart q=E, u=E*alpha. Result on that chart: F o g = E^2 * (U_T + alpha^2 * G).

Observed (exact algebra, several coranks k=2,3 and pivots t1=1,2): the u-factor is clean for ANY k; the
join gives E^2 * (factor) with factor(0) = U_T(0) = 1; and G(0) = 0 (G is itself a lower-dim core, NOT a
unit). The Jacobian discrepancy telescopes h_E = (n*t1 - 1) + (k^2 - 1) + 1 = Mval - 1, and F vanishes to
order exactly 2 along E, giving divisor ratio (h_E+1)/2 = Mval/2.

<questions>
Q1. Is the per-block step "Delta = u*Dbar" (radial blow-up of the coordinate subspace {Delta=0}) a GENERAL
    move valid for ANY block size k (any coupled corank>=2), or is there a k>=2 obstruction that makes it
    instance-specific? State the load-bearing reason.
Q2. Does this radial step by itself "collapse the coupled k x k block to a single monomial" (a per-block
    principality), or does it merely factor one exceptional coordinate and leave a genuinely deeper core G
    that must recurse? i.e. is the "collapse to a single monomial" a property of the STEP, or only of the
    terminal chart of the FULL recursion (where a retained-rank pivot supplies the leading unit)?
Q3. THE DECISIVE ONE. To get the RLCT VALUE, must one monomialise the block (produce the single-monomial
    normal form / principal generator), or can the value be read off the DIVISOR RATIO (h_E+1)/(2 a_E)
    alone, where a_E = min-order-of-vanishing of F along E and h_E = Jacobian discrepancy? Specifically:
    (a) for the UPPER bound rlct <= Mval/2 (one divisor suffices), is a_E = 1 obtainable directly from the
        PIVOT entry's pullback order (=1) WITHOUT the block normal form?
    (b) for the LOWER bound rlct >= (1/2) min (needs ALL divisors), does one need the block collapse, or
        only (per divisor: a_E from the entries + h_E from the blow-up) PLUS a covering family of charts?
</questions>
</task>

<output_contract>
Q1/Q2/Q3 with a one-sentence verdict each, then <=6 lines. Mark [FACT] vs [INFERENCE]. For Q3 give a
crisp separation: what the value-read-off NEEDS vs what the normal-form/collapse adds beyond it. Be
adversarial: if the radial step secretly needs the block to be already-nice (e.g. a specific rank
condition on Dbar*S), say so.
</output_contract>

<grounding_rules>
Standard blow-up / toric / Newton-polyhedron RLCT facts allowed. Flag anything about THIS DLN core you
cannot derive from the stated facts as [INFERENCE]. If my "read the value off the ratio without the
collapse" framing is wrong, say why.
</grounding_rules>
