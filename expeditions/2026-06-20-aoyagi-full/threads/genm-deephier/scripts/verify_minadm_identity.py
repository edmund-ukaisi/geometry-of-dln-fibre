"""
Test the emergent identity for SINGLE deep matrix (loss-only):
   C_k^hier  ==  minAdm( (u, M2, n) )   for ALL k   (k-independent!)
and the gate reduction:  minAdm((u,M2,n)) >= minAdm(M) - a*b   (t=u term of the minAdm recursion).
Also test WITH charge whether C_k^hier stays == minAdm((u,)+deep) or the charge lowers it below.
"""
import itertools, numpy as np
from functools import lru_cache
from deephier_lp import Ck_hier_LP, minAdm, binding_cut

W=9
bad_id=0; bad_id_charge=0; bad_gate=0; ncut=0; nstrat=0
min_slack=None; worst_charge_below_id=None
examples_slack0=0
for M in itertools.product(range(1,W+1),repeat=4):
    M0,M1,M2,M3=M
    deep=(M2,M3)
    tstar,r=binding_cut(M)
    for j in range(1,r):
        u=tstar+j; a=M0-u;b=M1-u
        if a<1 or b<1: continue
        rho=min(M2,M3); n=M3; exc=abs(M2-n)
        mA=minAdm(M); target=mA-a*b
        mAudeep=minAdm((u,)+deep)     # minAdm(u,M2,M3)
        ncut+=1
        gate_ok = (mAudeep >= target)
        if not gate_ok: bad_gate+=1
        for k in range(1,rho+1):
            p=k+exc
            Chl=Ck_hier_LP(u,rho,k,p,a,b,charge=False)   # loss-only
            Ch =Ck_hier_LP(u,rho,k,p,a,b,charge=True)     # with charge
            nstrat+=1
            # identity loss-only
            if Chl is None or abs(Chl-mAudeep)>1e-6: bad_id+=1
            # with charge: is it still == minAdm((u,)+deep)? or lower?
            if Ch is not None:
                if Ch < mAudeep-1e-6:
                    bad_id_charge+=1
                    if worst_charge_below_id is None or (mAudeep-Ch)>worst_charge_below_id[0]:
                        worst_charge_below_id=(mAudeep-Ch,M,u,k,Ch,mAudeep,target)
                slack=Ch-target
                if min_slack is None or slack<min_slack: min_slack=slack
        if mAudeep==target: examples_slack0+=1

print(f"cuts={ncut} strata={nstrat}")
print(f"loss-only identity  C_k^hier == minAdm((u,M2,n))  FAILS: {bad_id}")
print(f"gate reduction      minAdm((u,)+deep) >= 2T1q      FAILS: {bad_gate}")
print(f"with-charge  C_k^hier < minAdm((u,)+deep) (charge lowers below RRR codim): {bad_id_charge}")
print(f"min slack (C_k^hier WITH charge - 2T1q): {min_slack}")
print(f"cuts where minAdm((u,)+deep)==2T1q (tight, u is a minAdm-minimizer): {examples_slack0}")
if worst_charge_below_id: print("  worst charge-below-identity:", worst_charge_below_id)
