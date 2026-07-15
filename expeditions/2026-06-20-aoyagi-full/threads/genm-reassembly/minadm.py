from functools import lru_cache
from itertools import product

def redchain(t, M):
    # M : tuple length L+3 (>=3). redChain t M = (t, M2, ..., M_last)
    return (t,) + M[2:]

@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(M)
    n = len(M)
    if n == 1:
        return 0
    if n == 2:
        return M[0]*M[1]
    best = None
    for t in range(min(M[0], M[1])+1):
        v = (M[0]-t)*(M[1]-t) + minAdm(redchain(t, M))
        if best is None or v < best:
            best = v
    return best

def argmins(M):
    M=tuple(M)
    vals=[]
    for t in range(min(M[0],M[1])+1):
        v=(M[0]-t)*(M[1]-t)+minAdm(redchain(t,M))
        vals.append((v,t))
    m=min(v for v,_ in vals)
    return m, [t for v,t in vals if v==m]

def deepTailMin(M):
    return min(M[2:])   # min of M2..Mlast

# search L=1 chains M=(M0,M1,M2,M3), good branch, strict shell j>=1 giving a,b>=1, and M2 > deepTailMin (rank-deficient deep)
print("Searching L=1 good chains with strict shell (a,b>=1) and M2 > deepTailMin(=M3-side):")
found=[]
for M0 in range(2,7):
  for M1 in range(2,7):
    for M2 in range(1,8):
      for M3 in range(1,8):
        M=(M0,M1,M2,M3)
        dtm=deepTailMin(M)
        if dtm > M1:   # good branch requires deepTailMin <= M1
            continue
        m,ts=argmins(M)
        for tstar in ts:
            r=min(M0-tstar, M1-tstar)
            for j in range(1,r):   # strict shell 1<=j<r
                u=tstar+j
                a=M0-u; b=M1-u
                if a>=1 and b>=1:
                    # descent gate
                    Mp=redchain(u,M)
                    gate = m <= a*b + minAdm(Mp)
                    rankdef = (M2 > dtm)   # deep Gram full-MxM det degenerate
                    if rankdef:
                        found.append((M,tstar,j,u,a,b,m,minAdm(Mp),dtm,gate))
# print a few
for f in found[:25]:
    M,tstar,j,u,a,b,m,mp,dtm,gate=f
    T1=(m-a*b)/2
    print(f"M={M} t*={tstar} j={j} u={u} a={a} b={b} minAdm={m} minAdm(M')={mp} deepTailMin={dtm} gate={gate}  T1={T1} carrierThr(M')={mp/2}")
print("total found:", len(found))
