from itertools import product, permutations
from math import comb

def admBound(M,j): return min(M[0],M[1]) if j==0 else M[j+1]
def admissible(M,T):
    L=len(T)
    if any(T[j]>admBound(M,j) for j in range(L)): return False
    for i in range(L):
        for j in range(i,L):
            if T[j]>T[i]: return False
    if L>=1 and T[L-1]!=0: return False
    return True
def Mval(M,T):
    L=len(T); s=0
    for j in range(L):
        tprev=M[0] if j==0 else T[j-1]; s+=(tprev-T[j])*(M[j+1]-T[j])
    return s
def minimisers(M):
    L=len(M)-1; A=[T for T in product(range(max(M)+1),repeat=L) if admissible(M,T)]
    m=min(Mval(M,T) for T in A); return [T for T in A if Mval(M,T)==m]
def qipA(d,l):
    N=len(d)-1; return sum(d[min(i,N)] for i in range(l+1))-l*d[min(l,N)]
def qipM(d):
    N=len(d)-1; best=0
    for l in range(N+1):
        if qipA(d,l)>=0: best=l
    return best
def qipS(d):
    N=len(d)-1; m=qipM(d); return sum(d[min(i,N)] for i in range(m+1))
def ell_a(M):
    d=tuple(sorted(M)); l=qipM(d); S=qipS(d); cM=(S+l-1)//l; return l, S-(cM-1)*l

def boxpart(l,a):
    # antitone f: Fin a -> N with f i <= l-a
    b=l-a
    out=[]
    for f in product(range(b+1),repeat=a):
        if all(f[i]>=f[i+1] for i in range(a-1)):
            out.append(f)
    return out

def le_pt(x,y): return all(p<=q for p,q in zip(x,y))

def poset_iso(P,Q):
    # P,Q lists of tuples (possibly different arity), order = pointwise <=. brute force iso.
    if len(P)!=len(Q): return False
    n=len(P)
    # precompute relation matrices
    RP=[[le_pt(P[i],P[j]) for j in range(n)] for i in range(n)]
    RQ=[[le_pt(Q[i],Q[j]) for j in range(n)] for i in range(n)]
    # prune by up/down degree signature
    def sig(R):
        return sorted((sum(R[i]), sum(R[j][i] for j in range(n))) for i in range(n))
    if sig(RP)!=sig(RQ): return False
    for perm in permutations(range(n)):
        ok=True
        for i in range(n):
            for j in range(n):
                if RP[i][j]!=RQ[perm[i]][perm[j]]: ok=False;break
            if not ok: break
        if ok: return True
    return False

traps={'M1=[1,1,2,1]':(1,1,2,1),'M2=[2,2,4,3]':(2,2,4,3),'M3=[2,2,2,2,2]':(2,2,2,2,2)}
for name,M in traps.items():
    l,a=ell_a(M); mins=minimisers(M); bp=boxpart(l,a)
    iso=poset_iso(mins,bp)
    print(f"{name}: (l,a)=({l},{a})  |min|={len(mins)} |BoxPart|={len(bp)}  poset-iso to BoxPart: {iso}")

# also a small sweep of the iso itself (expensive, keep tiny)
print("\n=== poset-iso sweep (positive M, L<=3, W<=3) ===")
fails=0; tot=0; ex=[]
for L in range(1,4):
    for M in product(range(1,4),repeat=L+1):
        l,a=ell_a(M)
        if l==0 or not(0<=a<=l): continue
        tot+=1
        mins=minimisers(M); bp=boxpart(l,a)
        if not poset_iso(mins,bp):
            fails+=1
            if len(ex)<8: ex.append((M,l,a))
print(f"poset-iso {{Adm & Mval=minAdm}} ≅ BoxPart(l,a): {tot-fails}/{tot}  ({fails} fails)")
for e in ex: print("   FAIL",e)
