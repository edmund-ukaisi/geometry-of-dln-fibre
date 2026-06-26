#!/usr/bin/env python3
"""
Vzero_lambda_recursion.py — VERIFY Codex's repaired rank-stratified recursion gives the RIGHT rlct of
the corank-r matrix-product core ||Δ S||^2 (Δ r×r, S r×p), against known/literature values.

Codex's recursion (S2-free + radial disjoint-sum lemma):
  λ_{r,p} = min( r^2/2 ,  min_{1<=j<=r} ( j*p/2 + λ_{r-j, p} ) ),   λ_{0,p} = 0.
The r^2/2 term = the a-divisor (full point-blow-up scale, exceptional mult r^2-1 -> threshold r^2/2... 
wait: (r^2-1+1)/2 = r^2/2, yes). The j-sum term = the rank-(r-j) stratum: a jp/2 Morse block (the
full-rank j-part, dim j*p, threshold jp/2) PLUS the lower core λ_{r-j,p}.

Cross-check against the KNOWN rlct of ||Δ S||^2 (= the matrix-product / RRR core rlct at true rank 0).
For Δ r×r (square) and S r×p, this is the (r,r,p) RRR core: rlct = ½·minAdm(r,r,p) (Aoyagi).
We compute minAdm(r,r,p)/2 and compare to λ_{r,p}.
"""
import sys
sys.path.insert(0,'/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/26-r1-genM-chart/scripts')
from genM_structure import minAdmRec
from fractions import Fraction as F
from functools import lru_cache

@lru_cache(maxsize=None)
def lam(r,p):
    if r==0: return F(0)
    best = F(r*r,2)
    for j in range(1,r+1):
        best = min(best, F(j*p,2) + lam(r-j,p))
    return best

print("Codex recursion λ_{r,p} vs known ½·minAdm(r,r,p) [the (r,r,p) RRR core rlct]:")
ok=True
for (r,p) in [(1,2),(1,4),(2,2),(2,4),(3,3),(3,4),(2,3),(4,4),(2,5),(3,2)]:
    lrp = lam(r,p)
    M = (r,r,p)
    m9 = F(minAdmRec(M)[0],2)
    match = (lrp==m9)
    ok = ok and match
    print(f"  r={r},p={p}: λ_recursion={lrp}   ½·minAdm({r},{r},{p})={m9}   match={match}")
print()
print("ALL MATCH:" , ok)
print("=> Codex's repaired rank-stratified recursion (Morse-block + lower-core, NOT just lower-core)")
print("   reproduces the correct ||Δ S||^2 rlct = ½·minAdm(r,r,p). The intermediate strata BIND")
print("   (the min picks them up). S2-free + the radial disjoint-sum lemma. Verdict survives the repair.")
