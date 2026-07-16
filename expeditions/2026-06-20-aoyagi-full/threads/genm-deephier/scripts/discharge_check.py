"""
Confirm the two claims the coordinator's Q1/Q2 hinge on:
 (Q1a) C_k^single (deepGate_branch formula) is NOT a lower bound on the true per-cell codim:
        C_k^hier <= C_k^single, STRICT at deep strata -> single-scale formula OVER-estimates true codim.
 (Q1b/Q2) The two codim objects are DISTINCT and must not be conflated:
        kappa_k = CR(deep, rho-k)         [deep-param MEASURE codim, ~k^2]  -- banked as productRankLocus codim
        RRRfloor = minAdm((u,)+deep)      [loss-fibre codim of (u-row front)x(deep) product] -- the honest floor
   Show kappa_k != RRRfloor in general (so the banked productRankLocus codim is the WRONG object for the floor),
   and RRRfloor >= 2T1q (t=u term), and min_k C_k^hier = RRRfloor.
"""
import itertools
from deephier_lp import Ck_hier_LP, minAdm, binding_cut
from deepgate_scan import analyze, CR

W=8
strict=0; nstrat=0; kappa_ne_floor=0; ncut=0
for M in itertools.product(range(1,W+1),repeat=4):
    M0,M1,M2,M3=M; deep=(M2,M3)
    tstar,r=binding_cut(M)
    for j in range(1,r):
        u=tstar+j; a=M0-u;b=M1-u
        if a<1 or b<1: continue
        info=analyze(M,u); rho=info['rho']; exc=abs(M2-M3)
        if not (a+b<=rho-1): continue
        ncut+=1
        floor=minAdm((u,)+deep)
        for k in range(1,rho+1):
            nstrat+=1
            Cs=info['recs'][k-1][4]            # C_k^single
            Ch=Ck_hier_LP(u,rho,k,k+exc,a,b,charge=True)
            kap=CR(deep,rho-k)
            if Ch < Cs-1e-6: strict+=1          # hierarchical strictly below single-scale
            if kap != floor: kappa_ne_floor+=1   # kappa_k (measure codim) != RRR floor
print(f"cuts={ncut} strata={nstrat}")
print(f"(Q1a) strata with C_k^hier STRICTLY < C_k^single (single-scale over-estimates true codim): {strict}")
print(f"(Q1b) strata with kappa_k != minAdm((u,)+deep) (measure codim NOT the RRR floor): {kappa_ne_floor}")
# worked example (4,4,4,4)@u=3
M=(4,4,4,4);u=3;info=analyze(M,u);deep=(4,4);exc=0;rho=4
print(f"\n(4,4,4,4)@u=3: RRRfloor=minAdm(3,4,4)={minAdm((3,4,4))}, 2T1q={info['target']}")
for k in range(1,5):
    Cs=info['recs'][k-1][4]; Ch=Ck_hier_LP(u,rho,k,k+exc,1,1,charge=True); kap=CR(deep,rho-k)
    print(f"  k={k}: kappa_k(measure)={kap}  C_single={Cs}  C_hier(TRUE)={Ch}  [floor=10]")
