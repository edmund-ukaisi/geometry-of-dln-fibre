import itertools
from functools import lru_cache

@lru_cache(maxsize=None)
def minAdm(M):
    if len(M)==2: return M[0]*M[1]
    M0,M1=M[0],M[1]
    return min((M0-t)*(M1-t)+minAdm((t,)+M[2:]) for t in range(0,min(M0,M1)+1))

def tstars(M):
    M0,M1=M[0],M[1]
    vals=[((M0-t)*(M1-t)+minAdm((t,)+M[2:]),t) for t in range(0,min(M0,M1)+1)]
    m=min(v for v,_ in vals)
    return [t for v,t in vals if v==m]

def deep(M): return min(M[2:])

# STEP 2: marginal g(t+1)-g(t) <= deepTailMin, where g(t)=minAdm((t,)+tail)
print("=== marginal minAdm((t+1,tail))-minAdm((t,tail)) <= deepTailMin(tail) ? ===")
viol=0; checked=0; maxexcess=None
for taillen in range(1,5):  # tail = (M2,...): arity of (t,tail) = 1+taillen
    for tail in itertools.product(range(1,8),repeat=taillen):
        rho=min(tail)
        for t in range(0,12):
            g0=minAdm((t,)+tail); g1=minAdm((t+1,)+tail)
            checked+=1
            d=g1-g0
            if d>rho: viol+=1; 
            ex=d-rho
            if maxexcess is None or ex>maxexcess: maxexcess=ex
print(f"  checked {checked}, violations(g1-g0>rho): {viol}, max(g1-g0-rho)={maxexcess}")

# STEP 3 consequence at binding cut: (M0-t*)+(M1-t*) <= deepTailMin + 1  (when t* < min(M0,M1), i.e. r>=1)
print("\n=== at binding t*, r>=1: (M0-t*)+(M1-t*) <= deepTailMin + 1 ? (GOOD chains) ===")
viol=0; checked=0
for arity in range(3,7):
    for M in itertools.product(range(1,7),repeat=arity):
        M0,M1=M[0],M[1]; rho=deep(M)
        if not (rho<=M1): continue  # GOOD
        for ts in tstars(M):
            r=min(M0-ts,M1-ts)
            if r>=1:
                checked+=1
                if not ((M0-ts)+(M1-ts) <= rho+1): viol+=1
print(f"  checked {checked} (binding, r>=1), violations: {viol}")

# Also WITHOUT GOOD assumption (does the mechanism need GOOD?)
print("\n=== same but NO good assumption (all chains) ===")
viol=0; checked=0; ex=[]
for arity in range(3,7):
    for M in itertools.product(range(1,7),repeat=arity):
        M0,M1=M[0],M[1]; rho=deep(M)
        for ts in tstars(M):
            r=min(M0-ts,M1-ts)
            if r>=1:
                checked+=1
                if not ((M0-ts)+(M1-ts) <= rho+1):
                    viol+=1; ex.append((M,ts,rho,(M0-ts)+(M1-ts)))
print(f"  checked {checked}, violations: {viol}")
for e in ex[:6]: print("   ",e)
