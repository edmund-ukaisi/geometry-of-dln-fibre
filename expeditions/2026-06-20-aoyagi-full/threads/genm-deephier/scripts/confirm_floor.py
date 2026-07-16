import itertools, numpy as np
from deephier_lp import Ck_hier_LP, minAdm, binding_cut

W=9
below=0; above=0; eq=0; mink_ne=0; ncut=0
worst_below=None
for M in itertools.product(range(1,W+1),repeat=4):
    M0,M1,M2,M3=M; deep=(M2,M3)
    tstar,r=binding_cut(M)
    for j in range(1,r):
        u=tstar+j; a=M0-u;b=M1-u
        if a<1 or b<1: continue
        rho=min(M2,M3); n=M3; exc=abs(M2-n)
        mAudeep=minAdm((u,)+deep); ncut+=1
        Cks=[]
        for k in range(1,rho+1):
            p=k+exc
            Ch=Ck_hier_LP(u,rho,k,p,a,b,charge=True)  # WITH charge (honest)
            Cks.append(Ch)
            if Ch is None: continue
            if Ch < mAudeep-1e-6:
                below+=1
                if worst_below is None or (mAudeep-Ch)>worst_below[0]: worst_below=(mAudeep-Ch,M,u,k,Ch,mAudeep)
            elif Ch > mAudeep+1e-6: above+=1
            else: eq+=1
        Cks=[c for c in Cks if c is not None]
        if abs(min(Cks)-mAudeep)>1e-6: mink_ne+=1
print(f"cuts={ncut}")
print(f"WITH-charge C_k^hier vs minAdm((u,)+deep):  below={below}  equal={eq}  above={above}")
print(f"cuts where min_k C_k^hier != minAdm((u,)+deep): {mink_ne}")
if worst_below: print("worst below:",worst_below)
