<task>
Exact-analysis follow-up: does a dyadic-shell + Hölder bound, using ONLY an UNWEIGHTED
reduced-chain black box, reach the sharp finiteness threshold for the SQUARE depth-3 chain
(n,n,n,n) with n >= 3 (the previous question settled n=2, which reached threshold)?

Setup (same family, general n). Over real matrices, entries in [-1,1], Lebesgue:
    I_n(c') = ∫_{P ∈ [-1,1]^{n×n}, det P≠0} ∫_{Z∈[-1,1]^{n×n}} ∫_{W∈[-1,1]^{n×n}}
                 ‖P·Z·W‖_F^{-2c'} dP dZ dW.
Known (do not re-derive): I_n finite iff c' < c*_n := ½·minAdm(n,n,n,n). Values:
  n=2: minAdm=3, c*=3/2 (dim of Y=P·Z is n²=4, origin density order A_scale=1, β=dim−A_scale=3=minAdm — TIGHT, shell reaches it).
  n=3: minAdm=6, c*=3.
Black box B_n (the "plain unweighted arity-IH"): J_n(c'') := ∫_{Z,W ∈ [-1,1]^{n×n}}
  ‖Z·W‖_F^{-2c''} dZ dW < ∞ for all c'' < ½·minAdm(n,n,n) (n=3: minAdm(3,3,3)=7, so c''<7/2).
You may invoke B_n at any c''<½minAdm(n,n,n), any finite constant, any sub-box.

The mechanism to test. Decompose I_n by dyadic shells E_r={r/2<σ_max(Y)≤r}, Y=P·Z. Rescale
Y=rX. The shell contributes r^{n²−2c'} ∫_{X-shell,W} ρ_ang(X) ‖X·W‖^{-2c'} dX dW, where
ρ_ang(X)=ρ(X)|_{σ_max(X)≍1} is the (angular) pushforward density of the n×n product
restricted to σ_max≍1, and ρ(rX)≍r^{-A_scale}ρ_ang(X). The bracket is bounded by Hölder:
‖ρ_ang‖_{L^p(shell)} · (∫‖X·W‖^{-2c'q})^{1/q}, 1/p+1/q=1, using B_n at exponent c'q.

The questions:

(U1) Compute the ORIGIN homogeneity order A_scale of the n×n-product pushforward density ρ
(order of ρ(rX) as r→0, X invertible fixed). Is A_scale = n²−minAdm(n,n,n,n) exactly (so the
shell exponent β=n²−A_scale=minAdm is tight)? Give A_scale for n=2,3,4.

(U2) THE CRUX. Characterize the singularities of ρ_ang(X) on the rank-drop strata of X at
σ_max(X)≍1: for each rank r'<n (rank-r' locus, codimension (n−r')², i.e. σ_{r'+1},…,σ_n→0),
is ρ_ang ~ log (order 0) or a genuine power dist^{-γ_{r'}} with γ_{r'}>0? Give γ_{r'} for n=3
(strata rank 2 codim 1, rank 1 codim 4, rank 0 codim 9) and n=4.

(U3) Is ρ_ang ∈ ∩_p L^p(σ_max≍1 shell) (i.e. all γ_{r'}=0, only log)? If NOT, for which p is
ρ_ang ∈ L^p? The condition γ_{r'} p < codim_{r'} = (n−r')² for every stratum bounds p, hence
bounds q>1, hence bounds the reachable c' = c*'... 

(U4) THE DECISION. Does the Hölder bracket ∫_{X-shell,W} ρ_ang(X)‖X·W‖^{-2c'} dX dW stay
FINITE for ALL c' < c*_n = ½minAdm(n,n,n,n)? Equivalently: is the reachable threshold
(governed by min over strata of the Hölder budget vs B_n's headroom ½minAdm(n,n,n)) equal to
c*_n, or STRICTLY LESS? If strictly less for some n≥3, give the first n and quantify the gap,
AND say whether the JOINT structure (ρ_ang's rank-r' singularity coincides with the locus where
‖X·W‖ also degenerates, so B_n at exponent c'q already "sees" the extra codim) rescues it —
i.e. can the pure-Hölder split be replaced by a rank-stratified bound that still uses ONLY the
unweighted B_n and reaches c*_n?

(U5) VERDICT. For the square family (n,n,n,n): does the shell(+possibly rank-stratified) route
using ONLY the unweighted B_n reach the sharp threshold for ALL n, or only n≤2? If it fails for
n≥3, state precisely what extra ingredient is forced (a weighted/coupled black box that carries
ρ_ang, OR charts pinned to σ_min(P)≥δ) — and whether that is strictly stronger than the
unweighted B_n.
</task>

<output_contract>
Answer U1–U5 in order, labelled. U1: A_scale for n=2,3,4 + tightness yes/no. U2/U3: the
per-stratum singularity orders γ_{r'} and the L^p range. U4: FINITE-for-all-c'<c*_n yes/no,
first failing n if any, gap size, and whether joint/rank-stratified structure rescues it with
unweighted B_n only. U5: crisp verdict (all n | only n≤2) + the forced extra ingredient if any.
Be quantitative; distinguish PROVEN from INFERRED. ≤ 750 words.
</output_contract>

<grounding_rules>
Real matrices, [-1,1], Lebesgue. minAdm(3,3,3,3)=6, minAdm(3,3,3)=7, minAdm(2,2,2,2)=3,
minAdm(2,2,2)=3 (given). The product of two independent uniform n×n matrices has a classical
pushforward density; reason analytically (Schur/SVD/coarea). The n=2 case reaches threshold via
shell+Hölder (established). Distinguish proven from inferred; do not write code you cannot run.
</grounding_rules>
