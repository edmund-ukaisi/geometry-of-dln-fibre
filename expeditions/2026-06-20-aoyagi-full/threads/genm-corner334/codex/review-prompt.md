<task>
You are red-teaming the SOUNDNESS of a Lean formalisation's stratification design. No Lean syntax needed; judge the mathematical logic.

CONTEXT. We formalise a finiteness bound for a local-model "corner-slice" fiber integral arising in the RLCT (real log-canonical threshold) analysis of deep linear networks, for the dimension tuple (3,3,3,4) at a binding corank-2 cut. The integrand over the unit box [0,1]^2 (radial variables u0,u1) is:

    ( u0^2 * U0  +  u1^2 * U1 )^(-c')  *  ( |u0|^3 * |u1|^2 )

with "deep-data units":
    U0 = ||w1 * A2||^2 + delta^2 * ||w2 * A2||^2
    U1 = a_piv^2 * ||vbar * A2||^2
where A2 is a 2xq real matrix (deep data), w1,w2,vbar are fixed row-vectors in R^2, and w*A2 means vecMul (row-vector times matrix). The claim: this integral is < infinity for every c' < 7/2, where 7/2 = (1/2)*minAdm(3,3,3,4) is the branch threshold.

THE ADDITIVE (coupled-corner) MECHANISM. The threshold 7/2 comes from the two codimensions ADDING: block dims 4 and 3, so 4+3=7, threshold 7/2. This is proved (banked) by weighted AM-GM at the min-cut weights (4/7,3/7): (u0^2*U0+u1^2*U1)^(-c') is dominated by a SEPARATED monomial |u0|^(3-8c'/7)|u1|^(2-6c'/7), both exponents > -1 iff c'<7/2, GIVEN U0,U1 >= a > 0 (units bounded below). Contrast: an independent scalar split of the two divisors would take the MIN (3/2), the z^2(x^2+y^2) RLCT-collapse. So the "units bounded below by a>0" hypothesis is exactly what pins the coupled (additive/sum) branch.

THE STRATIFICATION. The units U0,U1 are bounded below by a positive constant IFF A2 has full row rank (rank 2). "Full row rank" is encoded as Function.Injective (A2.vecMul), i.e. the map w -> w*A2 is injective, i.e. the 2 rows of A2 are linearly independent. On this SECTOR the finiteness at 7/2 is proved UNCONDITIONALLY. The COMPLEMENT {A2 : rank-drop, ¬injective} is NOT proved finite; it is routed to an explicit NAMED hypothesis hDeeper : (¬ injective A2.vecMul) -> (integral < infinity). The top-level theorem is a by_cases cover: sector branch discharged by the proved theorem; complement branch = hDeeper. The design doc asserts (as deferred follow-on, NOT proved here) that the complement is a "strictly-deeper corank stratum (higher Mval, threshold >= 1/2 * minAdm), resolved by the general recursion, NOT an a.e.-drop, because the weight is unbounded near it."

The units U0,U1 in the fiber integral are CONSTANT in the radial variables u0,u1 (a "fixed vertical slice" — the deep data A2 and angular data are held fixed). The follow-on integrates over A2 by Tonelli; that assembly is explicitly deferred.
</task>

<output_contract>
Answer these, each a short paragraph, label INFERENCE vs FACT:
1. Is routing the rank-drop complement to a NAMED hypothesis hDeeper (rather than proving it, a.e.-dropping it, or globally assuming units>0) the HONEST way to express a partial stratified result? Or is there a hidden hole / circularity / vacuity risk in a by_cases cover where one branch is a hypothesis?
2. Is "Function.Injective (A2.vecMul)" for a 2xq matrix a FAITHFUL encoding of "A2 full row rank"? Any edge case (q=0, q=1) where it fails to mean what's intended?
3. Does the additive endpoint genuinely deliver the SUM threshold 7/2 and not silently collapse to the MIN 3/2? Is using CONSTANT-in-radial units (min(U0,U1) as the uniform lower bound a) a legitimate use of the additive endpoint, or does holding the units constant hide the coupling that produces 7/2?
4. THE KEY WORRY: is the design's assertion "complement is a strictly-deeper stratum, so it can't be a.e.-dropped because the weight is unbounded near it" internally consistent with routing it to a hypothesis hDeeper that ASSERTS finiteness of THE SAME integrand on the complement? I.e., on the rank-drop complement, the units U0/U1 can VANISH, so the integrand (u0^2*U0+u1^2*U1)^(-c') can blow up — is it even TRUE that the integral is finite on the complement, or is hDeeper potentially a FALSE hypothesis being smuggled in (making the of_deeper theorem vacuously/unsoundly "provable" downstream)?
5. Anything else that would make this "validation slice" subtly overclaim relative to "the (3,3,3,4) corner additive mechanism is finite at 7/2 on the full-rank sector".
</output_contract>

<grounding_rules>
Distinguish what you can DERIVE (FACT) from what you SUSPECT (INFERENCE). If a concern depends on the precise meaning of hDeeper (which is an ASSUMED hypothesis, not proved), say so explicitly — the point of #4 is whether assuming it is dangerous (could it be provably false, contaminating downstream consumers?).
</grounding_rules>
