#!/usr/bin/env python3
"""Adversarial + mechanism probes for the rank-corrected charge closure.
   (imports pure functions from rankcharge; suppress its anchor printout by capturing.)"""
import io, contextlib
_buf = io.StringIO()
with contextlib.redirect_stdout(_buf):
    import rankcharge as R
from itertools import product, permutations

minAdm = R.minAdmRec            # validated == brute
minAdmRank = R.minAdmRank
redChain = R.redChain

# ---- 1. ADVERSARIAL: wide-early / narrow-deep, big gaps (rank cap bites hardest) ----
print("== 1. ADVERSARIAL wide-early/narrow-deep (rank loss a*(b-n) large) ==")
adv = [(9,9,1),(10,10,1,1),(12,12,2,1),(8,8,1,1,1),(9,1,9),(1,9,9),
       (10,10,10,1),(10,2,2,10),(7,7,7,1,1),(12,3,12,3),(6,6,6,6,1),
       (15,15,1),(20,20,3,2,1),(11,11,11,11,2)]
fails = 0
for M in adv:
    m = minAdm(M); mr = minAdmRank(M)
    tag = "CLOSES" if mr==m else f"FAIL {mr}<{m}"
    if mr!=m: fails+=1
    print(f"   {str(M):<22} minAdm={m:>4}  minAdmRank={mr:>4}   {tag}")
print(f"   adversarial fails = {fails}")

# ---- 2. PERMUTATION INVARIANCE of minAdm (paper result) and of minAdmRank ----
print("\n== 2. permutation invariance ==")
def perm_check(base_set, tag):
    minAdm_noninv = 0; rank_noninv = 0; rank_ne_adm = 0
    for M in base_set:
        vals_adm = set(minAdm(p) for p in permutations(M))
        vals_rank = set(minAdmRank(p) for p in permutations(M))
        if len(vals_adm) > 1: minAdm_noninv += 1
        if len(vals_rank) > 1: rank_noninv += 1
        if minAdm(M) != minAdmRank(M): rank_ne_adm += 1
    print(f"   [{tag}] minAdm perm-noninvariant: {minAdm_noninv}   "
          f"minAdmRank perm-noninvariant: {rank_noninv}   minAdmRank!=minAdm: {rank_ne_adm}")
# unique multisets via sorted tuples
S3 = set(tuple(sorted(M)) for M in product(range(0,6),repeat=3))
S4 = set(tuple(sorted(M)) for M in product(range(0,6),repeat=4))
perm_check(S3, "L+1=3, w0..5")
perm_check(S4, "L+1=4, w0..5")

# ---- 3. FRAGILITY: how much can we shrink s before closure breaks? ----
# Replace s = min(b,n) by  s' = max(0, min(b,n) - delta).  If closure survives delta=0
# only, the geometry is TIGHT; if it survives delta>=1, there is margin.
print("\n== 3. fragility of the s-formula (shrink s by delta, does closure still hold?) ==")
def minAdmRank_delta(M, delta):
    from functools import lru_cache
    @lru_cache(maxsize=None)
    def rec(M):
        L=len(M)-1
        if L==0: return 0
        if L==1: return M[0]*M[1]
        n=min(M[2:])
        best=None
        for t in range(min(M[0],M[1])+1):
            a=M[0]-t; b=M[1]-t
            s=max(0, min(b,n)-delta)
            v=a*s+rec(redChain(t,M))
            best=v if best is None or v<best else best
        return best
    return rec(M)
for delta in [0,1,2]:
    fails=[]
    for M in product(range(0,5),repeat=4):
        if minAdmRank_delta(M,delta) < minAdm(M):
            fails.append(M)
    print(f"   delta={delta}: close_fails={len(fails)}   e.g. {fails[:5]}")

# ---- 4. does the BINDING cut of ab-recursion have s==b (full rank)? ----
print("\n== 4. at the ab-binding cut, is s == b (rank cap inactive)? ==")
def binding_cuts(M):
    n = min(M[2:]) if len(M)>=3 else None
    m = minAdm(M)
    out=[]
    for t in range(min(M[0],M[1])+1):
        a=M[0]-t;b=M[1]-t
        if a*b+minAdm(redChain(t,M))==m:
            s=min(b,n) if n is not None else b
            out.append((t,a,b,s,s==b or a==0))
    return out
cnt_all_full=0; cnt_has_deficient_binding=0; total=0
examples=[]
for M in product(range(1,5),repeat=4):
    if len(M)<3: continue
    total+=1
    bcs=binding_cuts(M)
    # is there a binding cut with rank cap inactive (s==b or a==0)?
    if any(bc[4] for bc in bcs): cnt_all_full+=1
    else:
        cnt_has_deficient_binding+=1
        if len(examples)<8: examples.append((M,bcs))
print(f"   chains with >=1 ab-binding cut where cap inactive (s==b or a==0): {cnt_all_full}/{total}")
print(f"   chains where EVERY ab-binding cut has s<b and a>0: {cnt_has_deficient_binding}")
for M,bcs in examples:
    print(f"      {M}: binding cuts (t,a,b,s,capInactive) = {bcs}")
