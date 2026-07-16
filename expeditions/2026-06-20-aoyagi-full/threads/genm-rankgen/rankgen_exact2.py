import itertools, random
from fractions import Fraction
from functools import lru_cache
@lru_cache(maxsize=None)
def minAdm(M):
    if len(M)==2: return M[0]*M[1]
    M0,M1=M[0],M[1]
    return min((M0-t)*(M1-t)+minAdm((t,)+M[2:]) for t in range(0,min(M0,M1)+1))
def tstars(M):
    M0,M1=M[0],M[1]
    vals=[((M0-t)*(M1-t)+minAdm((t,)+M[2:]),t) for t in range(0,min(M0,M1)+1)]
    m=min(v for v,_ in vals); return [t for v,t in vals if v==m]
def deep(M): return min(M[2:])
def matmul(A,B):
    n=len(A);k=len(A[0]);m=len(B[0])
    return [[sum(A[i][l]*B[l][j] for l in range(k)) for j in range(m)] for i in range(n)]
def rank_exact(A):
    A=[[Fraction(x) for x in row] for row in A]; n=len(A);m=len(A[0]);r=0
    for c in range(m):
        piv=next((i for i in range(r,n) if A[i][c]!=0),None)
        if piv is None: continue
        A[r],A[piv]=A[piv],A[r]; inv=Fraction(1)/A[r][c]; A[r]=[x*inv for x in A[r]]
        for i in range(n):
            if i!=r and A[i][c]!=0:
                f=A[i][c];A[i]=[a-f*b for a,b in zip(A[i],A[r])]
        r+=1
        if r==n:break
    return r
def deep_product_generic_rank(dw, trials=3):
    best=0
    for s in range(trials):
        random.seed(1000*s+len(dw))
        mats=[[[random.randint(-9,9) for _ in range(dw[L+1])] for _ in range(dw[L])] for L in range(len(dw)-1)]
        Z=mats[0]
        for Mt in mats[1:]: Z=matmul(Z,Mt)
        best=max(best, rank_exact(Z))
    return best, min(dw)

fails=0;checked=0;worst=[]
for arity in [4,5,6]:
    for M in itertools.product(range(1,6),repeat=arity):
        M0,M1=M[0],M[1];rho=deep(M)
        if not (rho<=M1):continue
        need=any(M1-(ts+j)>=1 for ts in tstars(M) for j in range(1,min(M0-ts,M1-ts)))
        if not need:continue
        rk,mn=deep_product_generic_rank(M[2:])
        checked+=1
        if rk!=mn: fails+=1; worst.append((M,M[2:],rk,mn))
print(f"arity 4..6 GOOD chains needing incidence: checked {checked}")
print(f"  generic (random exact) rank of deep product = deepTailMin: {checked-fails}/{checked}  fails={fails}")
for w in worst[:6]: print("   ",w)

# Also directly: b <= generic rank (the FACT) at binding strict shells
print("\n=== FACT check: b <= genericRank(Z_deep) = deepTailMin at ALL binding strict shells (arity 4..6) ===")
bf=0;bc=0
for arity in [4,5,6]:
    for M in itertools.product(range(1,6),repeat=arity):
        M0,M1=M[0],M[1];rho=deep(M)
        if not (rho<=M1):continue
        for ts in tstars(M):
            for j in range(1,min(M0-ts,M1-ts)):
                b=M1-(ts+j)
                if b<0:continue
                bc+=1
                if b>rho: bf+=1
print(f"  binding strict-shell cuts: {bc}, b>deepTailMin fails: {bf}")
