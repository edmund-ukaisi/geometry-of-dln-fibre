#!/usr/bin/env python3
"""leaf_data.py — compute routeLayerAtlas leaf (d,k,h) + thresholds exactly, mirroring the Lean defs.
Each leaf = a descent path; carries SINGLE divisor foldDivisors[acc'] with acc' = path total Mval.
foldDivisors[c] : d=1, k=[1], h=[c-1] (the appendDivisor (1,c-1) onto the empty d=0 leaf... but the
leaf base is d=0; appendDivisor adds ONE axis -> d=1). threshold = c/2.
NOTE the leaf base leafMonoData 0 has d=0; foldDivisors[c] = appendDivisor c onto it -> d=1, k=[1], h=[c-1].
"""
import sys
sys.path.insert(0, '/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/26-r1-genM-chart/scripts')
from genM_structure import redChain
from fractions import Fraction as F
from itertools import product as iproduct

def leaves(M, acc=0):
    """Yield (path, total_codim) for every descent leaf, mirroring routeLayerAtlasAcc."""
    M = tuple(M); L = len(M) - 1
    if L == 0:
        yield ((), acc); return
    if L == 1:
        yield ((), acc + M[0]*M[1]); return
    for t in range(min(M[0], M[1]) + 1):
        block = (M[0]-t)*(M[1]-t)
        for (p, tot) in leaves(redChain(t, M), acc + block):
            yield ((t,)+p, tot)

def report(M):
    M = tuple(M)
    ls = list(leaves(M))
    totals = [tot for (_,tot) in ls]
    mn = min(totals)
    print(f"M={M}: {len(ls)} leaves; path-totals (=Mval) range [{mn}..{max(totals)}]; minAdm={mn}")
    # each leaf: single divisor foldDivisors[tot] -> (d=1,k=[1],h=[tot-1]), threshold tot/2
    print(f"   leaf thresholds = tot/2; min = {F(mn,2)} = minAdm/2; achiever leaf tot={mn}")
    # show a few leaves
    for (p,tot) in sorted(ls, key=lambda x:x[1])[:5]:
        print(f"      path t={p} -> total codim {tot} -> leaf (d,k,h)=(1,[1],[{tot-1}]) threshold {F(tot,2)}")
    return ls

if __name__ == "__main__":
    for M in [(2,2,2),(3,3,4),(4,4,4),(3,3,3,3)]:
        report(M); print()
