from functools import lru_cache
from itertools import product
@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==2: return M[0]*M[1]
    best=None
    for t in range(0,min(M[0],M[1])+1):
        v=(M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:])
        best=v if best is None or v<best else best
    return best
def R(t,tail): return minAdm((t,)+tail)
def binding_cuts(M):
    M=tuple(M); best=minAdm(M); return best,[t for t in range(0,min(M[0],M[1])+1)
        if (M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:])==best]

print("=== FLAG-CHARGE sweep: arity 3,4,5 (lengths 4,5,6). C_j=(a-j)(b-j)+R_{t+j} >= minAdm(M)? + tightness ===")
tot=0; under=0; tight_j0=0; tight_any=0; aGTm2=0; aEQm2=0
examples_tight=[]
for L,W in [(4,7),(5,5),(6,4)]:
    for M in product(range(1,W+1),repeat=L):
        best,cuts=binding_cuts(M); tail=M[2:]
        for t in cuts:
            a=M[0]-t; b=M[1]-t
            if a<1 or b<1: continue
            tot+=1
            if b==1:
                if a>M2 if (M2:=M[2]) else False: aGTm2+=1
                elif a==M[2]: aEQm2+=1
            mins=[]
            for j in range(0,min(a,b)+1):
                Cj=(a-j)*(b-j)+R(t+j,tail)
                mins.append(Cj)
                if Cj<best: under+=1
            if mins[0]==best: tight_j0+=1
            if min(mins)==best:
                tight_any+=1
                if len(examples_tight)<8 and b>=2: examples_tight.append((M,t,a,b,mins,best))
print(f"  genuine decorated cuts checked: {tot}")
print(f"  flag-charge undershoots (C_j<minAdm): {under}")
print(f"  cuts with a>M2 (b=1, atom-divergent): {aGTm2}   a==M2 (log): {aEQm2}")
print(f"  cuts tight at j=0 (C_0=minAdm, zero slack): {tight_j0}")
print(f"  cuts tight at some flag level: {tight_any}")
print("  sample b>=2 tight flag charges (M,t,a,b,[C_j...],minAdm):")
for e in examples_tight: print("    ",e)
