<task>
An RLCT / singular-learning determinant-integral question. I need an INDEPENDENT determination of
whether a specific "joint determinantal rank-sector resolution" reaches a target learning coefficient,
or whether it undershoots (leaving a residual). Argue from scratch; do not assume it works.

BACKGROUND. For a width vector M=(M0,M1,M2,M3) (nonneg ints), the deep-linear-network zero-target loss
is F(A)=||A0·A1·A2||_F^2 (A_i the layer matrices, sizes M0xM1, M1xM2, M2xM3). Its real log-canonical
threshold (RLCT / learning coefficient) is known (Aoyagi): lambda(M) = (1/2)·minAdm(M), where
  minAdm(M) = min over 0<=t<=min(M0,M1) of [ (M0-t)(M1-t) + minAdm(t,M2,M3) ],   base minAdm(x,y)=x*y.
So ∫_{box} F(A)^{-c'} dA < ∞  iff  c' < (1/2)minAdm(M).

THE CORNER SUB-INTEGRALS. A layer-peeling proof of finiteness cuts the front (between M0,M1) at rank
u, giving a=M0-u, b=M1-u, and a "shell" restricting the deep factor S=A1·A2 (M1xM3, generic rank
rho=min(M1,M2,M3)) to a fixed rank stratum. Two families of corner sub-integrals resist a naive bound:

 (I) DEEP-CORANK cut (a>=1,b>=1, a+b>=rho+2): the corank charge
       Ch = ∫_{Acor} det( (Acor·S)(Acor·S)^T )^{-a/2} dAcor        (Acor is b x M2)
     is +∞ (Wishart: finite iff a < rho-b+1, i.e. a+b<=rho). A polar blow-up of the freed corank block
     Gamma (a x b) gives a clean reduction ab/2, but the residual "angular front charge"
       J = ∫_{Acor}∫_{Omega in S^{ab-1}} ||Omega·Acor·S||_F^{-ab} dOmega dAcor
     is finite (log) only at a+b=rho+1 and POWER-DIVERGENT at a+b>=rho+2. So the clean ab/2 route
     UNDERSHOOTS the target (1/2)minAdm(M) by a positive amount at these deep cuts.

 (II) SATURATED cut (a=0, u=M0<=M1, b=M1-M0): the loss collapses to F=||P·A0·(deep)||^2 with P (M0xM0)
     invertible, A0 (M1xM2 leading tail layer restricted). Reducing to the shorter chain via the
     pushforward density rho(z) of z=P·A0 (or [P|B12]·[A0]) undershoots when the pointwise density
     order A=max_{1<=j<=min(u,M2)} j(M2-b-j) exceeds 2Delta=minAdm(redChain)-minAdm(M): the pointwise
     bound consumes A/2 > Delta and reaches only (1/2)minAdm(M) - (A/2-Delta).

THE PROPOSED FIX ("joint determinantal rank-sector resolution"): instead of the factored charge (I) /
pointwise density (II), stratify the relevant matrix-product intermediate by its RANK r, blow up along
each rank-r determinantal stratum carrying the true Jacobian, and reduce each stratum to a
shorter-chain box integral (the induction hypothesis on arity-3 chains).

QUESTIONS.
(Q1) Does the joint determinantal rank-sector resolution REACH the target (1/2)minAdm(M) for the deep
     corank cuts (I) and the saturated A>2Delta cells (II)? Or does it ALSO undershoot at some cell
     (a genuine residual)? Verify at the tight cells: M=(2,1,2,2) at u=0 (a=2,b=1,rho=1,k=2, target 1),
     M=(2,2,3,3) at u=0 (a=2,b=2,rho=2,k=2, target 2), and the saturated M=(2,2,2,2) at u=2 (target 1.5).
(Q2) What is the exponent contributed by each rank-r stratum, and is the MIN over r equal to
     (1/2)minAdm(M)? Is there a clean correspondence between the rank-r strata and the terms of the
     minAdm recursion?
(Q3) WHY does the naive factored/pointwise bound undershoot while the stratified resolution reaches the
     target — is the naive bound a lossy over-estimate of the singularity (giving a smaller finiteness
     threshold than the true RLCT), or is it computing a genuinely different (smaller) quantity?
(Q4) Each stratum reduces to a shorter (arity-3) chain box integral. Which shorter chains appear, and is
     the induction hypothesis "finiteness for ALL arity-3 chains below their own (1/2)minAdm" enough to
     close each stratum — or does some stratum need a threshold its reduced chain cannot supply?
</task>

<output_contract>
- Q1: crisp verdict per cell — reaches (1/2)minAdm, or undershoots (with the residual).
- Q2: the per-rank-r stratum exponent, and whether min_r = (1/2)minAdm(M); the minAdm-recursion link.
- Q3: lossy-over-estimate vs different-quantity, with the mechanism.
- Q4: the shorter chains per stratum; whether the arity-3 IH suffices.
- Separate PROVEN from ARGUED. Give at least one tight cell worked fully explicitly.
</output_contract>

<grounding_rules>
- Exact algebra / lct / determinantal-variety / Wishart reasoning in scope; MC only a guide.
- Do NOT assume the resolution works; the point is an independent check, incl. a possible undershoot.
- If a stratum genuinely undershoots the target, say so and identify it (that would be a real obstruction).
</grounding_rules>
