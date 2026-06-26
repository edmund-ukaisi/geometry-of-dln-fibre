import itertools
def admBound(M,j,L): return min(M[0],M[1]) if j==0 else M[j+1]
def adm(M):
    L=len(M)-1
    rngs=[range(admBound(M,j,L)+1) for j in range(L)]
    for T in itertools.product(*rngs):
        if all(T[i]>=T[j] for i in range(L) for j in range(L) if i<=j) and (L==0 or T[L-1]==0):
            yield T
def Mval(M,T):
    L=len(M)-1; tot=0
    for j in range(L):
        tprev = M[0] if j==0 else T[j-1]
        tot += (tprev-T[j])*(M[j+1]-T[j])
    return tot
def minAdm(M): return min(Mval(M,T) for T in adm(M))
def redM(M): return [M[s]-1 if s<=1 else M[s] for s in range(len(M))]

print("="*78)
print("CROSS-CHECK 1: the cover's per-node recursion min{mk/2, n/2+child} with n=M(last)")
print("  vs true minAdm. n=M(last)=the deepest tail width. Test L=2 vs L>=3.")
print("="*78)
def cover_rec(M):
    # cover claim: rlct = min{ (M0*M1)/2 , M(last)/2 + cover_rec(redM) }, base: leaf
    L=len(M)-1
    if L<=0 or min(M[:-1])<=0: return 0  # leaf-ish
    child = redM(M)
    # leaf base: if child is a leaf (some width 0 in the non-tail, or L collapses)
    if min(child[:-1])<=0:
        childval=0
    else:
        childval = cover_rec(child)
    from fractions import Fraction as F
    return min(F(M[0]*M[1],2), F(M[-1],2)+childval)

from fractions import Fraction as F
print("\nL=2 cases (cover n=M(last) should MATCH minAdm/2):")
f2=True
for (m,k,n) in itertools.product(range(1,6),range(1,6),range(1,8)):
    M=[m,k,n]; cov=cover_rec(M); tru=F(minAdm(M),2)
    if cov!=tru: f2=False; print(f"  MISMATCH {M}: cover={cov} true={tru}")
print("  all L=2 match?", f2)

print("\nL>=3 cases (does cover n=M(last) DIVERGE from minAdm/2?):")
for M in [[3,3,3,3],[2,2,2,2],[3,3,3,3],[2,2,2,3],[3,2,2,2],[2,3,3,2],[4,4,4,4]]:
    cov=cover_rec(M); tru=F(minAdm(M),2)
    print(f"  M={M}: cover(n=M_last)={cov}  minAdm/2={tru}  {'MATCH' if cov==tru else 'DIVERGE'}")
