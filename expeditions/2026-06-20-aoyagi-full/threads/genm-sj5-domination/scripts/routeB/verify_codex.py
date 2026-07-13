from functools import lru_cache
from itertools import product
@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def binding_cuts(M):
    mA=minAdm(M)
    return [t for t in range(min(M[0],M[1])+1)
            if (M[0]-t)*(M[1]-t)+minAdm((t,)+tuple(M[2:]))==mA]
def rho(M): return min(M[1:])
def rev(M): return tuple(reversed(M))
def piv_strict(M):
    r=rho(M)
    for t in binding_cuts(M):
        if t>=1 and t*r<minAdm((t,)+tuple(M[2:])): return False
        for j in range(1,min(M[0]-t,M[1]-t)+1):
            u=t+j;a=M[0]-u;b=M[1]-u
            if a<1 or b<1: continue
            if u*r<minAdm((u,)+tuple(M[2:])): return False
    return True

# (a) Codex's upper-bound lemma: minAdm(u, tail) <= u * min(tail), all chains
print("(a) minAdm(chain) <= chain[0]*min(chain[1:])  over widths 1..7, lengths 2..6:")
bad=0
for Ln in range(2,7):
    for M in product(range(1,8),repeat=Ln):
        if minAdm(M) > M[0]*min(M[1:]): bad+=1
print("   violations (expect 0):", bad)

# (b) Codex's theorem: front-bad => M1 < min(M2..ML); both-ends-bad => 3 widths only
print("\n(b) front-bad(M) => M1 < min(M2..ML)?  and both-ends-bad only for 3 widths?")
front_bad_but_M1ge=0; bothbad_ge4=0; bothbad3=0
for Ln in [3,4,5,6]:
    for M in product(range(1,7),repeat=Ln):
        fb = not piv_strict(M)
        if fb and M[1] >= min(M[2:]): front_bad_but_M1ge+=1
        if not piv_strict(M) and not piv_strict(rev(M)):
            if Ln==3: bothbad3+=1
            else: bothbad_ge4+=1
print("   front-bad chains with M1 >= min(M2..ML) (expect 0):", front_bad_but_M1ge)
print("   both-ends-bad with >=4 widths (Codex: expect 0):", bothbad_ge4)
print("   both-ends-bad with 3 widths:", bothbad3)

# (c) 3-width exact family: both-bad <=> y < min(x,z)  (strict conv includes j=0)
print("\n(c) 3-width: both-ends-bad(strict) == (y<min(x,z))?  widths 1..8:")
mism=[]
for M in product(range(1,9),repeat=3):
    bb = not piv_strict(M) and not piv_strict(rev(M))
    wf = M[1] < min(M[0],M[2])
    if bb!=wf: mism.append((M,bb,wf))
print("   mismatches:", len(mism), mism[:6])

# (d) TRANSITIVE: >=4-width chains that are top-good from an end but forced to reduce to a bad waist
@lru_cache(maxsize=None)
def dischargeable(M):
    M=tuple(M)
    if len(M)<=2: return True
    for N in {M,rev(M)}:
        if not piv_strict(N): continue
        if all(dischargeable((t,)+tuple(N[2:])) for t in binding_cuts(N)): return True
    return False
ge4_topgood_but_stuck=0
for Ln in [4,5]:
    for M in product(range(1,7),repeat=Ln):
        topgood = piv_strict(M) or piv_strict(rev(M))
        if topgood and not dischargeable(M): ge4_topgood_but_stuck+=1
print("\n(d) >=4-width chains top-good from an end but NOT transitively dischargeable:", ge4_topgood_but_stuck)
print("    e.g.:", [M for M in product(range(1,5),repeat=4) if (piv_strict(M) or piv_strict(rev(M))) and not dischargeable(M)][:5])
