"""
Exact binding-cell EQUALITY witnesses for each inequality-shaped condition in the d<=1 dispatch.
"""
from functools import lru_cache
from itertools import product
@lru_cache(maxsize=None)
def minAdmRec(M):
    n=len(M)
    if n<=1: return 0
    if n==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:]) for t in range(0,min(M[0],M[1])+1))
def redChain(t,M): return (t,)+M[2:]
def dens_order_A(M0,M1,M2):
    b=M1-M0; best=0
    for j in range(1,min(M0,M2)+1): best=max(best,j*(M2-b-j))
    return best
def gen(ar,w):
    for L in ar:
        for M in product(range(1,w+1),repeat=L): yield M

# (A) d=1 a=u boundary (the a<u disposal marginal). Find a d=1 cut with a==u, print minAdm and the shifted target.
print("=== (A) d=1 a==u boundary (INT ||Qtil w||^-a marginal at a=u) ===")
found=0
for M in gen([4],5):
    M0,M1=M[0],M[1]; mA=minAdmRec(M)
    for t in range(1,min(M0,M1)+1):
        a=M0-t; b=M1-t; d=min(a,b); u=t
        if d==1 and a==u:
            rc=redChain(t,M); mRC=minAdmRec(rc); peel=a*b
            # shifted target exponent bound: c' - peel/2 < mRC/2 ; c' < mA/2
            print(f"  M={M} t={t}: a={a} b={b} u={u} (a=u), minAdm={mA}, redChain={rc} minAdm={mRC}, peelCharge={peel}, "
                  f"cut-sound: {mA} <= {peel}+{mRC}={peel+mRC} -> {mA<=peel+mRC}")
            found+=1
            if found>=4: break
    if found>=4: break

# (B) b=0 tall: qbox marginal at M2=a+1 (converges iff M2<=a). Find M2==a and M2==a+1.
print("=== (B) b=0 tall qbox: conv iff M2<=a; marginal/diverge at M2=a+1 ===")
c_eq=0; c_marg=0
for M in gen([4],6):
    M0,M1,M2=M[0],M[1],M[2]
    if M1<M0:  # strict tall b=0
        a=M0-M1
        if M2==a and c_eq<2:
            print(f"  M={M}: a=M0-M1={a}, M2={M2}=a -> qbox STRICT (converges, one-shot).")
            c_eq+=1
        if M2==a+1 and c_marg<2:
            print(f"  M={M}: a={a}, M2={M2}=a+1 -> qbox MARGINAL boundary (a=q-b+1); one-shot FAILS, needs recursion.")
            c_marg+=1

# (C) a=0 wide: A vs 2Delta boundary. Find A==2Delta (fold marginal) and A>2Delta (fold fails).
print("=== (C) a=0 wide: A vs 2Delta (2Delta = minAdm(redChain M0 M) - minAdm M) ===")
c_eq=0;c_gt=0
for M in gen([4],6):
    M0,M1,M2=M[0],M[1],M[2]
    if M0<M1:  # a=0 wide
        A=dens_order_A(M0,M1,M2); mA=minAdmRec(M); twoD=minAdmRec(redChain(M0,M))-mA
        if A==twoD and A>0 and c_eq<3:
            print(f"  M={M}: A={A} == 2Delta={twoD} -> pointwise fold MARGINAL (and per Codex 2b the fold is unsound even here).")
            c_eq+=1
        if A>twoD and c_gt<3:
            print(f"  M={M}: A={A} > 2Delta={twoD} -> fold FAILS, needs front rank-sector blow-up.")
            c_gt+=1
