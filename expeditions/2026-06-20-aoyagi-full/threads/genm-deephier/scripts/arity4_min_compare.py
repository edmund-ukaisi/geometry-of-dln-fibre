import itertools
from deephier_lp import Ck_hier_LP, minAdm, binding_cut
from deepgate_scan import analyze

W=9
ncut=0; single_gt_hier=0; single_gt_floor=0; hier_lt_floor=0; hier_lt_target=0
worst_gap=None
for M in itertools.product(range(1,W+1),repeat=4):
    M0,M1,M2,M3=M; deep=(M2,M3)
    tstar,r=binding_cut(M)
    for j in range(1,r):
        u=tstar+j; a=M0-u;b=M1-u
        if a<1 or b<1: continue
        info=analyze(M,u); rho=info['rho']; exc=abs(M2-M3)
        if not (a+b<=rho-1): continue
        ncut+=1
        floor=minAdm((u,)+deep); target=minAdm(M)-a*b
        minS=min(rec[4] for rec in info['recs'])                      # single-scale min_k C_k
        minH=min(Ck_hier_LP(u,rho,k,k+exc,a,b,charge=True) for k in range(1,rho+1))
        if minS>minH+1e-6:
            single_gt_hier+=1
            if worst_gap is None or (minS-minH)>worst_gap[0]: worst_gap=(minS-minH,M,u,minS,minH,floor,target)
        if minS>floor+1e-6: single_gt_floor+=1
        if minH<floor-1e-6: hier_lt_floor+=1
        if minH<target-1e-6: hier_lt_target+=1
print(f"arity 4 widths 1..{W}: cuts={ncut}")
print(f"  min_k C_k^single  >  min_k C_k^hier  (hierarchical lowers the BINDING min): {single_gt_hier}")
print(f"  min_k C_k^single  >  minAdm((u,)+deep) floor: {single_gt_floor}")
print(f"  min_k C_k^hier    <  minAdm((u,)+deep) floor [should be 0]: {hier_lt_floor}")
print(f"  min_k C_k^hier    <  2T1q  [KILL-condition, should be 0]: {hier_lt_target}")
if worst_gap: print("  worst single>hier gap:",worst_gap)
