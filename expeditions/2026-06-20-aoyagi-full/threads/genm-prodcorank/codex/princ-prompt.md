<task>
A resolution-of-singularities / RLCT question about the PRODUCT-CORANK ideal of a deep-linear (DLN) loss.
Adjudicate ONE truth-value: is the RLCT of the loss reachable by a NATIVE, self-contained resolution
(iterated single-factor blow-ups + any bespoke extra blow-ups), NON-circularly — or does the joint
product-corank incidence genuinely require a bespoke joint (non-submersive) resolution?

SETUP. Square DLN chain: free real matrices P, Z, W (each n x n), loss f = || P Z W ||^2 (Frobenius,
sum of squares of the entries of the triple product) near the origin. RLCT (largest pole of ∫|f|^{z}) is
known (cited, Aoyagi) to equal c* = (1/2)·minAdm(n,n,n,n), where minAdm is the fibre/quiver-orbit
codimension (the paper's geometric codimension). We are trying to establish this RLCT by an EXPLICIT
resolution, WITHOUT invoking "RLCT = (1/2)codim ⟹ no smaller-ratio divisor" (that is the very thing to be
proved — using it is circular).

EXACT FACTS I have verified (take as given; do not re-derive):
 (F1) The middle product Y = P·Z (n x n, product of two free n x n matrices) has product-corank variety
      V_k = {rank(PZ) ≤ n−k}. Its MINIMAL codimension is C_k = k^2 − floor(k^2/4), NOT the naive k^2.
      C_1=1, C_2=3, C_3=7, C_4=12, ...
 (F2) That minimal codim C_k is achieved on a BALANCED component: rank(P) drops by a≈k/2, rank(Z) drops by
      c≈k/2, AND im(Z) ∩ ker(P) has forced dimension e≈k/2 (a Schubert/alignment condition). On this
      binding component the FIRST factor's corank is only ⌈k/2⌉, not k. (Verified: n=4,k=4 optimum
      (a,c,e)=(2,2,2); numerical Jacobian-rank codim = C_k confirmed.)
 (F3) Stratifying the outer peel by the deeper corank m and pairing each stratum with the reduced chain:
      - "naive m^2" accounting: T_m = m^2/2 + (1/2)minAdm(n−m,n,n) ≥ c* for EVERY m, min = c* (binding
        strata marginal). Verified n=3..8.
      - "product C_m" accounting: T_m = C_m/2 + (1/2)minAdm(n−m,n,n) UNDERSHOOTS c* (< c*) for n≥4 (e.g.
        n=4,m=2: 3/2+7/2 = 5 < 11/2 = c*). Verified n=4..8.
      So the two accountings give OPPOSITE verdicts.
 (F4) After one first-factor peel, the residual loss is ||Γ·Q_b·(I−P_pivot)||^2 with Γ a FREE a×b block
      but Q_b itself a deeper matrix PRODUCT (nested factors), NOT a free matrix. So the pullback from the
      free-block determinantal resolution to the actual deeper-factor variables need not be submersive at
      the rank-drop locus.

THE QUESTIONS (answer in order, flag PROVEN vs INFERENCE for each):
 Q1. Does resolving the FIRST factor's rank strata alone (submersive, free-block, discrepancy m^2) —
     iterated down the chain — PRINCIPALIZE the joint ideal of the product P·Z·W (i.e. produce a
     normal-crossings model)? Or does a residual joint incidence survive on the balanced component (F2)
     where BOTH the first factor and the deeper product drop by ≈k/2 and align? Give the smallest case
     where a residual survives, if any.
 Q2. On the balanced binding component (F2), is the first-factor determinantal blow-up TRANSVERSE to the
     deeper-product rank strata, so the standard "|det J| = exceptional^{codim−1}" discrepancy (giving the
     naive m^2 of F3) applies? Or is the pullback non-submersive there, so the actual discrepancy is NOT
     the naive m^2 and must be computed by a bespoke joint resolution?
 Q3. If a residual survives (Q1), is that residual SELF-SIMILAR — a strictly smaller product-corank
     instance the SAME iterated procedure closes by induction (so the whole thing is "detail-at-scale",
     buildable by bookkeeping) — or does it require, at each stage, a NON-standard blow-up with
     branch-selection (choosing which factor/coordinate to blow up), i.e. a genuinely new resolution
     construction per instance?
 Q4. NET: can the RLCT c* be reached by an explicit NATIVE resolution non-circularly (with a
     formaliser-ready discrepancy bookkeeping), or is establishing that the iterated cover principalizes
     the joint product-corank ideal with discrepancies ≥ c* genuinely equivalent to re-proving the
     product-corank (Vandermonde-matrix-type) resolution theorem? State precisely what the minimal
     genuinely-new theorem is, if one is needed.
</task>

<output_contract>
Answer Q1–Q4 in order, each flagged PROVEN (state the standard fact) vs INFERENCE. Q1/Q2 are the crux:
whether the first-factor resolution principalizes / is transverse on the balanced component. Be concrete
about the smallest failing case. End with a one-line verdict:
NATIVE-REACHABLE-DETAIL-AT-SCALE / WALL-REQUIRES-JOINT-RESOLUTION / UNDECIDABLE-WITHOUT-<X>.
I have withheld my own tentative verdict; do not assume it. Do not paste Lean or long code.
</output_contract>

<grounding_rules>
Distinguish the exact arithmetic (F1–F4, given) from the analytic/geometric claim about principalization
and discrepancy on the balanced component. The load-bearing question is whether the iterated single-factor
cover resolves the balanced product-corank component (F2) with the naive m^2 discrepancy, or whether that
component's non-submersive pullback forces a bespoke joint resolution. Do NOT use "RLCT = (1/2)codim
(Aoyagi) ⟹ no smaller divisor" — that is circular for a native proof. If the honest answer is that a
genuinely-new resolution theorem is required, say so and name it minimally.
</grounding_rules>
