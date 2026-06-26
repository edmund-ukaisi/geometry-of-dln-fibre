#!/usr/bin/env python3
"""
hfin_all_strata.py — the CRITICAL refinement: hfin must cover ALL strata of routeMBaseNbhd, not just
the achiever path. So the obstruction is whether ANY leaf/stratum (any admissible path) has a corank>=2
drop — because the cover must resolve EVERY stratum the base neighborhood meets.

The base neighborhood routeMBaseNbhd = (-1,1)^N contains points of EVERY rank stratum. The cover's
leaves are ALL admissible paths. Even if the ACHIEVER (min) path is corank-1, OTHER paths (other rank
drops) realise corank>=2 strata that the cover must still resolve for the integral to be bounded
EVERYWHERE. So the relevant question: does ANY admissible path have a corank>=2 drop? (Almost always
yes for M with M_s>=3 somewhere, since dropping rank by >=2 at a boundary with both dims >=2 is admissible.)
"""
import sys
sys.path.insert(0, '/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/26-r1-genM-chart/scripts')
from genM_structure import all_adm, Mval, redChain

def path_steps_coranks(M, T):
    """For an admissible path T, the per-step residual coranks along the peel."""
    M=tuple(M); coranks=[]
    cur=M; idx=0
    while len(cur)>=3:
        t=T[idx]
        coranks.append(min(cur[0]-t, cur[1]-t))
        cur=redChain(t,cur); idx+=1
    coranks.append(min(cur[0],cur[1]))  # leaf
    return coranks

def report(M):
    M=tuple(M)
    anycorank2=False; achiever_corank2=False
    best=None;bT=None
    for T in all_adm(M):
        v=Mval(M,T)
        if best is None or v<best: best=v;bT=T
    for T in all_adm(M):
        cks=path_steps_coranks(M,T)
        if max(cks)>=2: anycorank2=True
    achiever_corank2 = max(path_steps_coranks(M,bT))>=2
    print(f"M={M} minAdm={best} achiever T*={bT}: ANY-path-corank>=2={anycorank2} ; achiever-corank>=2={achiever_corank2}")
    return anycorank2, achiever_corank2

if __name__ == "__main__":
    print("hfin must cover ALL strata. Obstruction bites if ANY admissible path has corank>=2.\n")
    for M in [(2,2,2),(2,1,2),(2,3,2),(3,3,3,3),(3,3,4),(2,2,4),(4,4,2,2)]:
        report(M)
