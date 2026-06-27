import functools
@functools.lru_cache(None)
def minAdmRec(M):
    M=tuple(M); n=len(M)
    if n==1: return 0
    if n==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:]) for t in range(0,min(M[0],M[1])+1))

# enumerate minimizing pivot sequence for (2,2,2). The recursion peels (M0,M1)->t, recurse on (t,M2).
def trace(M):
    M=tuple(M); n=len(M)
    if n<=2: return [(M, minAdmRec(M), None)]
    best=None;argt=None
    for t in range(0,min(M[0],M[1])+1):
        v=(M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:])
        if best is None or v<best: best=v;argt=t
    return [(M,best,argt)]+trace((argt,)+M[2:])

print("minAdm(2,2,2)=",minAdmRec((2,2,2)))
for (M,val,t) in trace((2,2,2)):
    print(f"  chain {M}: minAdmRec={val}, optimal peel t={t}")
# The recursion peels (2,2)->t giving (2-t)^2, then leaf (t,2)->t*2.
# total = (2-t)^2 + 2t, minimized:
for t in range(3):
    print(f"  t={t}: (2-t)^2 + 2t = {(2-t)**2 + 2*t}")
