#!/usr/bin/env python3
"""
iterfibre_criterion.py — the EXACT criterion for iterfibre(M) = ½·minAdm.

From iterfibre_class.py: best-iterfibre(M) = max over peel-orders of min(peeled outer-dims, terminal
Morse). This is a SMALL number (bounded by max single width / 2 roughly). ½·minAdm can be MUCH larger
(it's a SUM of block codims along the descent). So iterfibre = ½·minAdm only when ½·minAdm is itself
small — specifically when minAdm is achieved with a SINGLE binding block and the rest clean.

Conjecture to test: iterfibre(M) = ½·minAdm  iff  minAdm(M) = the iterfibre value = a single
factor's contribution (no ACCUMULATION across layers). Equivalently, ½·minAdm ≤ max-achievable-single-
peel-min. Let's just characterize by: does ½·minAdm equal min(some outer dim /2, some terminal)?

Test the hypothesis: iterfibre MATCHES iff L ≤ 2 with the binding being the leaf/Morse OR a single
2-width-ish structure. Survey a broad family and classify by (L, whether minAdm is "additive" = sum of
>1 nonzero blocks).
"""
import sys
sys.path.insert(0,'/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/26-r1-genM-chart/scripts')
from genM_structure import minAdmRec, all_adm, Mval
from fractions import Fraction as F
from functools import lru_cache
from iterfibre_class import best_iterfibre

def nonzero_blocks(M):
    """# of nonzero block codims in the minAdm descent (the 'accumulation depth')."""
    M=tuple(M)
    best=None;bT=None
    for T in all_adm(M):
        v=Mval(M,T)
        if best is None or v<best: best=v;bT=T
    L=len(M)-1
    blocks=[]
    for j in range(L):
        tprev=M[0] if j==0 else bT[j-1]
        blocks.append((tprev-bT[j])*(M[j+1]-bT[j]))
    return sum(1 for b in blocks if b>0), blocks

def report(M):
    M=tuple(M)
    it=best_iterfibre(M); ma=F(minAdmRec(M)[0],2)
    nz,blocks=nonzero_blocks(M)
    match = it==ma
    print(f"M={M}: iterfibre={it} ½minAdm={ma} match={match}  #nonzero-blocks={nz} blocks={blocks}")
    return match, nz

if __name__=="__main__":
    print("Hypothesis: iterfibre MATCHES ½·minAdm iff the minAdm descent has #nonzero-blocks ≤ 1\n")
    import itertools
    cases=[(2,2,2),(2,1,2),(4,4,2,2),(2,2,4),(3,3,3),(3,3,4),(3,3,3,3),(4,4,4),(5,3,4),(2,3,4,2),
           (1,1,2),(2,2,3),(2,3,2),(1,2,3),(3,3,2),(2,2,5),(2,4,2)]
    agree=True
    for M in cases:
        match,nz=report(M)
        # hypothesis: match iff nz<=1
        hyp = (nz<=1)
        if match!=hyp: agree=False; print("    *** hypothesis violated ***")
    print("\nHypothesis 'match iff #nonzero-blocks ≤ 1' holds on all tested:", agree)
