import functools
@functools.lru_cache(None)
def minAdmRec(M):
    M=tuple(M)
    n=len(M)
    if n==1: return 0
    if n==2: return M[0]*M[1]
    # >=3 widths: inf over t in [0, min(M0,M1)] of (M0-t)(M1-t) + minAdmRec(redChain t)
    # redChain t = (t, M2, M3, ..., M_{n-1})
    best=None
    for t in range(0, min(M[0],M[1])+1):
        red=(t,)+M[2:]
        v=(M[0]-t)*(M[1]-t)+minAdmRec(red)
        best=v if best is None else min(best,v)
    return best

for M in [(4,4,2,2),(3,3,4),(2,2,2),(3,3,3,3),(2,2,1),(2,1,2),(3,3,2),(2,2,2,2)]:
    print(f"minAdm{M} = {minAdmRec(M)}")
