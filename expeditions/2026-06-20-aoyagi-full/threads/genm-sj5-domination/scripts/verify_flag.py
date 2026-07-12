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

def R(t,tail):   # tail=(M2,M3,...);  R_t = minAdm(t, M2, ...)
    return minAdm((t,)+tail)

def binding_cuts(M):
    M=tuple(M); best=minAdm(M); res=[]
    for t in range(0,min(M[0],M[1])+1):
        if (M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:])==best: res.append(t)
    return best,res

# ---- CHECK A: at every b=1 binding cut, a <= M2 (so atom never diverges, only log at a=M2) ----
print("=== CHECK A: b=1 binding cuts -> is a <= M2 always? (a>M2 would be atom-divergent) ===")
viol=[]; eq=[]
for M in product(range(1,7),repeat=4):
    best,cuts=binding_cuts(M)
    for t in cuts:
        a=M[0]-t; b=M[1]-t; M2=M[2]
        if b==1 and a>=1:
            if a>M2: viol.append((M,t,a,M2))
            elif a==M2: eq.append((M,t,a,M2))
# also arity-4 (length-5) sample
for M in product(range(1,5),repeat=5):
    best,cuts=binding_cuts(M)
    for t in cuts:
        a=M[0]-t; b=M[1]-t; M2=M[2]
        if b==1 and a>=1 and a>M2: viol.append((M,t,a,M2))
print(f"  a > M2 violations (b=1): {len(viol)}   {viol[:8]}")
print(f"  a == M2 (borderline log) count: {len(eq)}  e.g. {eq[:6]}")

# ---- CHECK B: binding convexity  R_{t+1}-R_t >= (a-i)+(b-i)-1  and telescoped  R_{t+j}-R_t >= (a+b)j - j^2 ----
print()
print("=== CHECK B: telescoped convexity R_{t+j}-R_t >= (a+b)j - j^2  at binding cuts (all j) ===")
badB=[]
for M in product(range(1,7),repeat=4):
    best,cuts=binding_cuts(M)
    tail=M[2:]
    for t in cuts:
        a=M[0]-t; b=M[1]-t
        if a<1 or b<1: continue
        for j in range(0,min(a,b)+1):
            lhs=R(t+j,tail)-R(t,tail)
            rhs=(a+b)*j - j*j
            if lhs < rhs: badB.append((M,t,j,lhs,rhs))
print(f"  convexity violations: {len(badB)}  {badB[:6]}")

# ---- CHECK C: singular-FLAG charges C_j = (a-j)(b-j)+R_{t+j} >= minAdm(M)  (b>1 closure) ----
print()
print("=== CHECK C: flag charge C_j=(a-j)(b-j)+R_{t+j} >= minAdm(M) for all flag levels j ? ===")
badC=[]; tight=[]
for M in product(range(1,7),repeat=4):
    best,cuts=binding_cuts(M); tail=M[2:]
    for t in cuts:
        a=M[0]-t; b=M[1]-t
        if a<1 or b<1: continue
        for j in range(0,min(a,b)+1):
            Cj=(a-j)*(b-j)+R(t+j,tail)
            if Cj < best: badC.append((M,t,j,Cj,best))
print(f"  flag-charge undershoot C_j < minAdm(M): {len(badC)}  {badC[:6]}")

# ---- CHECK D: the (3,3,3) example: sigma_min-only vs flag ----
print()
print("=== CHECK D: M=(3,3,3), t=1, a=b=2 : sigma_min-only vs flag ===")
M=(3,3,3); best=minAdm(M); print(f"  minAdm(3,3,3)={best}, carrierThreshold={best/2}")
tail=M[2:]; t=1; a=M[0]-t; b=M[1]-t
# sigma_min-only bounded brick charge = (a)(b-1)+... Codex says gives (3+2)/2=5/2. Let me show flag closes at 7/2.
print(f"  a={a} b={b} tail={tail} R_t=R({t})={R(t,tail)} R_{{t+1}}={R(t+1,tail)} R_{{t+2}}={R(t+2,tail)}")
for j in range(0,min(a,b)+1):
    Cj=(a-j)*(b-j)+R(t+j,tail)
    print(f"    flag j={j}: C_j=(a-j)(b-j)+R_(t+j) = {(a-j)*(b-j)}+{R(t+j,tail)} = {Cj}   (>= minAdm {best}? {Cj>=best})")
# the sigma_min-only (drop just 1 sv): charge would use j=1 partial: freed (a)(b) with only tau_min small
# Codex: sigma_min-only gives 5/2. Show: naive single-sv bounded charge = a*b (freed) ... the undershoot
print("  [Codex: sigma_min-only split charges only (3+2)/2=5/2 < 7/2; the flag/det switch tau1*tau2~r^2 recovers 7/2]")
