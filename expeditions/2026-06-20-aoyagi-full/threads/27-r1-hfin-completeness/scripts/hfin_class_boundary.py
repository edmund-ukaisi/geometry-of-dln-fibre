#!/usr/bin/env python3
"""
hfin_class_boundary.py — characterize the M-class where the single-divisor leaf cover SUFFICES for hfin
vs where the corank-2 obstruction bites.

The hfin per-chart upper bound on a leaf requires F (on that chart's stratum) to be NORMAL-CROSSING
presentable by the leaf's divisor data. This works iff the binding strata along that path are
SMOOTH-center blow-ups (corank <= 1 drops -- each Schur peel removes a rank-1 pivot, a smooth center),
and FAILS where a path's drop has corank >= 2 (a determinantal center, not a single smooth divisor).

CLASS BOUNDARY (the achiever path's per-step corank):
- A descent step at boundary s drops rank from t_{s-1} to t_s. The block codim is
  (t_{s-1}-t_s)(M_s - t_s). The CORANK of the drop is min(t_{s-1}-t_s, ...) -- actually the residual
  block is (M_{s-1}-... ) -- the relevant corank is whether the per-step Schur residual is a rank-1
  (scalar, smooth) or rank->=2 (matrix, determinantal) drop.
- The (3,3,4) achiever t=(1,0): step drops M_0=3 -> t_1=1, a corank-2 partial drop (residual 2x2 Delta)
  -> determinantal -> the single-divisor leaf is geometrically inadequate (obstruction).
- The (2,2,2) achiever t=(1,0): drops 2->1, corank-1 residual (1x1 scalar Delta) -> SMOOTH -> single
  divisor suffices (threshold-only = coupled, agree).

We compute, per M, the achiever path's per-step residual-block dimensions (drop-rows x drop-cols) and
flag corank>=2 (the obstruction) vs corank<=1 (single-divisor OK).
"""
import sys
sys.path.insert(0, '/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/26-r1-genM-chart/scripts')
from genM_structure import minAdmRec, all_adm, Mval, redChain

def minim(M):
    best=None;bT=None
    for T in all_adm(tuple(M)):
        v=Mval(tuple(M),T)
        if best is None or v<best: best=v;bT=T
    return bT,best

def achiever_coranks(M):
    """Per descent step: residual block (drop_rows x drop_cols) and the corank = min(drop_rows,drop_cols)."""
    M=tuple(M);L=len(M)-1
    T,minAdm=minim(M)
    t=[M[0]]+[T[s] for s in range(L-1)]+[0]
    steps=[]
    cur=M
    idx=0
    while len(cur)>=3:
        ti=T[idx]
        drop_rows=cur[0]-ti   # M_0 - t (rows dropped)
        drop_cols=cur[1]-ti   # M_1 - t (cols dropped)
        corank=min(drop_rows,drop_cols)
        steps.append((cur,ti,drop_rows,drop_cols,corank))
        cur=redChain(ti,cur); idx+=1
    # leaf: cur is 2-width, the (t_last x M_last) product -- corank = min of leaf dims
    leaf_corank=min(cur[0],cur[1])
    steps.append((cur,None,cur[0],cur[1],leaf_corank))
    return steps,minAdm

def report(M):
    M=tuple(M)
    steps,minAdm=achiever_coranks(M)
    maxcorank=max(s[4] for s in steps)
    obstruction = maxcorank>=2
    print(f"M={M} minAdm={minAdm} achiever steps (chain, t, drop_rows x drop_cols, corank):")
    for (chain,ti,dr,dc,cr) in steps:
        tag=' <-- CORANK>=2 (determinantal, single-divisor INADEQUATE)' if cr>=2 else ' (corank<=1, smooth, OK)'
        print(f"   {chain} t={ti}: residual {dr}x{dc}, corank {cr}{tag}")
    print(f"   => hfin from single-divisor leaf: {'OBSTRUCTED (needs coupled charts)' if obstruction else 'REACHABLE (smooth-center cover)'}")
    print()
    return obstruction

if __name__ == "__main__":
    res={}
    for M in [(2,2,2),(2,1,2),(3,3,4),(2,2,4),(4,4,2,2),(3,3,3),(3,3,3,3),(5,3,4),(2,3,2)]:
        res[M]=report(M)
    print("OBSTRUCTED (corank>=2 binding):", [M for M,o in res.items() if o])
    print("REACHABLE (corank<=1):", [M for M,o in res.items() if not o])
