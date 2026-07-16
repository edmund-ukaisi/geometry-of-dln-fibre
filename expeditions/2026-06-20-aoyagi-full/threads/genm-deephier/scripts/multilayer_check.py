"""
Multi-layer (arity 5,6): show (a) single-scale deepgate min_k C_k OVER-estimates the honest RRR floor
minAdm((u,)+deep) [hierarchical erosion is REAL for multi-layer too], and (b) minAdm((u,)+deep) >= 2T1q.
Rigorous obstruction (all arities): C_k^hier >= RLCT_total = minAdm((u,)+deep) >= 2T1q, since the
deep-rank strata PARTITION the full integral whose honest RLCT-codim = minAdm((u,)+deep) (paper+Aoyagi;
the minAdm recursion over intermediate ranks IS the multi-scale-across-layers resolution).
"""
import itertools
from functools import lru_cache
from deepgate_scan import CR, minAdm, binding_cut, analyze  # reuse deepgate's single-scale C_k

def check(arity,W):
    ncut=0; single_over=0; below_floor_single=0; gate_fail=0; minslack=None
    worst=None
    for M in itertools.product(range(1,W+1),repeat=arity):
        deep=M[2:]
        tstar,r=binding_cut(M)
        for j in range(1,r):
            u=tstar+j; a=M[0]-u;b=M[1]-u
            if a<1 or b<1: continue
            info=analyze(M,u); rho=info['rho']
            if not (a+b<=rho-1): continue
            ncut+=1
            floor=minAdm((u,)+deep); target=minAdm(M)-a*b
            # single-scale min_k C_k (deepgate, comparable model)
            mins_single=min(rec[4] for rec in info['recs'])   # C*(k)
            if mins_single>floor: single_over+=1               # single-scale is an OVER-estimate of honest floor
            if floor<target: gate_fail+=1
            slack=floor-target
            if minslack is None or slack<minslack: minslack=slack
            # sanity: honest floor should be <= single-scale min (hierarchical can only lower)
            if floor>mins_single+1e-9:
                below_floor_single+=1
                if worst is None: worst=(M,u,floor,mins_single)
    return ncut,single_over,gate_fail,minslack,below_floor_single,worst

for arity,W in [(5,7),(6,5)]:
    ncut,so,gf,ms,bad,worst=check(arity,W)
    print(f"arity {arity} widths 1..{W}: cuts={ncut}")
    print(f"   single-scale min_k C_k STRICTLY > honest RRR floor minAdm((u,)+deep) (erosion real): {so}/{ncut}")
    print(f"   gate  minAdm((u,)+deep) < 2T1q : {gf}   min slack (floor-2T1q): {ms}")
    print(f"   (sanity) honest floor > single-scale min [should be 0]: {bad}  {worst if worst else ''}")
