from functools import lru_cache
# minAdmRec: Fin1->0; Fin2 (M0,M1)->M0*M1; >=3 widths -> min over t in [0,min(M0,M1)] of (M0-t)(M1-t)+minAdmRec(redChain t)
# redChain t M = (t, M2, M3, ...): pos0=t, pos i+1 = M(i+2)
def minAdm(M):
    M=tuple(M)
    if len(M)==1: return 0
    if len(M)==2: return M[0]*M[1]
    best=None
    for t in range(min(M[0],M[1])+1):
        red=(t,)+M[2:]
        val=(M[0]-t)*(M[1]-t)+minAdm(red)
        best=val if best is None else min(best,val)
    return best
def peel(M,t): return (M[0]-t)*(M[1]-t)
M=(5,5,3,3)
print("minAdm(5,5,3,3) =", minAdm(M), " (1/2 =",minAdm(M)/2,")")
for t in range(0,6):
    red=(t,3,3)
    print(f"  cut t={t}: a={M[0]-t} b={M[1]-t} peel={peel(M,t)} minAdm(redChain=({t},3,3))={minAdm(red)} sum={peel(M,t)+minAdm(red)} binding={peel(M,t)+minAdm(red)==minAdm(M)}")
print("tailMinWidth = min(M1,M2,M3)=min(5,3,3)=",min(M[1],M[2],M[3]))
print()
print("redChain(3,M)=(3,3,3): minAdm=",minAdm((3,3,3))," half=",minAdm((3,3,3))/2)
