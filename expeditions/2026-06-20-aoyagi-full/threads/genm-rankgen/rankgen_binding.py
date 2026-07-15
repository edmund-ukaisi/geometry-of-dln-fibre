import itertools
from functools import lru_cache

@lru_cache(maxsize=None)
def minAdm(M):
    # M is a tuple of widths, arity = len(M) >= 2
    if len(M) == 2:
        return M[0]*M[1]
    M0,M1 = M[0],M[1]
    best = None
    for t in range(0, min(M0,M1)+1):
        red = (t,) + M[2:]
        v = (M0-t)*(M1-t) + minAdm(red)
        if best is None or v < best:
            best = v
    return best

def tstars(M):
    M0,M1 = M[0],M[1]
    vals = []
    for t in range(0, min(M0,M1)+1):
        red = (t,)+M[2:]
        vals.append(((M0-t)*(M1-t)+minAdm(red), t))
    m = min(v for v,_ in vals)
    return [t for v,t in vals if v==m]

def deepTailMin(M):
    return min(M[2:])

# For each GOOD chain, at binding cut(s) u = t* + j, strict shell 1<=j<r, check b<=deepTailMin.
def sweep(max_w, aritymin, aritymax):
    total=0; fails=[]
    for arity in range(aritymin, aritymax+1):
        for M in itertools.product(range(1,max_w+1), repeat=arity):
            if arity<3: continue
            M0,M1=M[0],M[1]
            deep = deepTailMin(M)
            if not (deep <= M1):  # GOOD
                continue
            for tstar in tstars(M):
                r = min(M0-tstar, M1-tstar)
                for j in range(1, r):   # strict shell
                    u = tstar+j
                    a=M0-u; b=M1-u
                    if a<0 or b<0: continue
                    total+=1
                    if b>deep:
                        fails.append((M,tstar,j,u,a,b,deep))
    return total, fails

for (amin,amax,mw) in [(3,3,7),(4,4,7),(5,5,6),(3,6,5)]:
    tot,fails = sweep(mw,amin,amax)
    print(f"arity {amin}..{amax} widths 1..{mw}: {tot} binding-cut strict-shells, {len(fails)} with b>deepTailMin")
    for f in fails[:10]:
        M,ts,j,u,a,b,deep=f
        print(f"   M={M} t*={ts} j={j} u={u} a={a} b={b} deepTailMin={deep}  minAdm={minAdm(M)}")

print("\n=== M=(3,4,3,1): t* and cut analysis ===")
M=(3,4,3,1)
print("minAdm=",minAdm(M),"t*=",tstars(M),"deepTailMin=",deepTailMin(M))
for t in range(0,min(M[0],M[1])+1):
    red=(t,)+M[2:]
    print(f"  t={t}: pivot=(M0-t)(M1-t)={(M[0]-t)*(M[1]-t)} + minAdm(redChain)={minAdm(red)} = {(M[0]-t)*(M[1]-t)+minAdm(red)}")

print("\n=== relationship t* vs M1 - deepTailMin at binding cuts (GOOD chains) ===")
import itertools
viol_ge=0; viol_strict=0; checked=0; margin_hist={}
for arity in range(3,6):
    for M in itertools.product(range(1,7),repeat=arity):
        M0,M1=M[0],M[1]; deep=min(M[2:])
        if not (deep<=M1): continue
        for ts in tstars(M):
            r=min(M0-ts,M1-ts)
            # check the strongest: at j=1, b=M1-ts-1
            for j in range(1,r):
                u=ts+j; b=M1-u
                if b<0: continue
                checked+=1
                margin = deep - b   # >=0 means fact holds
                margin_hist[margin]=margin_hist.get(margin,0)+1
                if b>deep: viol_ge+=1
    # test t* >= M1 - deep for GOOD
print("checked binding strict-shell cuts:",checked,"  b>deep violations:",viol_ge)
print("margin (deepTailMin - b) histogram:", dict(sorted(margin_hist.items())))

# Does t* >= M1 - deep hold for GOOD chains (giving b<=deep-j at binding)?
c=0; f=0
for arity in range(3,6):
    for M in itertools.product(range(1,7),repeat=arity):
        M0,M1=M[0],M[1]; deep=min(M[2:])
        if not (deep<=M1): continue
        for ts in tstars(M):
            c+=1
            if not (ts >= M1 - deep): f+=1
print(f"\n t* >= M1 - deepTailMin (GOOD): {c} argmins, {f} violations")
