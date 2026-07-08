#!/usr/bin/env python3
"""
ADVERSARIAL battery for the front-peel closure (mirror the r1rankcharge cert's adversarial rigor):
wide-early/narrow-deep chains where the tail-rank drop is largest, plus permutation checks.

Claim under attack:  for every genuine chain M (L>=2),
    charge(q) := M_0*q + minAdm((M_1,...,M_L) - q)  >=  minAdm(M)   for all q in [0, min(M_1..M_L)],
with equality at the minimizing q  (i.e. minAdm(M) = min_q charge(q), the FRONT-PEEL identity).
"""
import io, contextlib
_buf = io.StringIO()
with contextlib.redirect_stdout(_buf):
    import rankcharge as R
from itertools import product, permutations

minAdm = R.minAdmRec
def sub(W,q): return tuple(max(0,w-q) for w in W)
def charge(M,q): return M[0]*q + minAdm(sub(M[1:],q))
def frontpeel(M): return min(charge(M,q) for q in range(min(M[1:])+1))

print("== ADVERSARIAL wide-early/narrow-deep (tail-rank drop largest) ==")
adv=[(9,9,1),(10,10,1,1),(12,12,2,1),(8,8,1,1,1),(9,1,9),(1,9,9),(10,10,10,1),
     (10,2,2,10),(7,7,7,1,1),(12,3,12,3),(6,6,6,6,1),(15,15,1),(20,20,3,2,1),
     (11,11,11,11,2),(2,20,20,2),(20,2,20,2),(3,3,3,3,3,3),(5,4,3,2,1)]
fails=0; below=0
for M in adv:
    m=minAdm(M); fp=frontpeel(M)
    lo=min(M[1:])
    bad=[q for q in range(lo+1) if charge(M,q)<m]
    tag="CLOSES" if fp==m and not bad else f"FAIL fp={fp} m={m} below={bad}"
    if fp!=m: fails+=1
    if bad: below+=1
    print(f"   {str(M):<20} minAdm={m:>4} frontpeel={fp:>4}  {tag}")
print(f"   frontpeel-identity fails={fails}   charge<minAdm chains={below}")

# per-q charge breakdown for the anchors (shows the binding q, often SUB-generic)
print("\n== per-q charge breakdown (which tail-rank q binds?) ==")
for M in [(4,4,2),(3,3,3,4),(4,4,2,2),(5,4,3,2),(2,3,2,4)]:
    m=minAdm(M); lo=min(M[1:]); gen=lo
    row=" ".join(f"q{q}={charge(M,q)}{'(B)' if charge(M,q)==m else ''}" for q in range(lo+1))
    binds=[q for q in range(lo+1) if charge(M,q)==m]
    print(f"   {str(M):<14} minAdm={m}: {row}   binding q={binds} (generic tail rank={gen})")

# permutation invariance of the front-peel value (should equal minAdm, which IS perm-invariant)
print("\n== permutation invariance of frontpeel (= minAdm, paper result) ==")
noninv=0; ne=0; tot=0
for M in set(tuple(sorted(x)) for x in product(range(0,6),repeat=4)):
    if len(M)<3: continue
    tot+=1
    vals=set(frontpeel(p) for p in permutations(M) if len(p)>=3)
    if len(vals)>1: noninv+=1
    if frontpeel(M)!=minAdm(M): ne+=1
print(f"   L+1=4 w0..5 multisets={tot}: frontpeel perm-noninvariant={noninv}  frontpeel!=minAdm={ne}")
