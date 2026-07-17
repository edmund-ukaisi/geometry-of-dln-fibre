"""
Wide a=0 build sub-order: bounded (M2<=b) / log (M2=b+1) / power-atlas (M2>=b+2), b=M1-M0.
And the per-dominant-minor CoV divergence check: |det F_sigma|^{-M2} over a free M0xM0 minor box
diverges for M2>=1 (codim{det=0}=1), so the NAIVE per-minor cover overcounts; the sector atlas over
ALL of F is required. Confirm the density-order A formula agrees (A=0 iff M2<=b+1).
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
def A_order(M0,M1,M2):
    b=M1-M0; return max([0]+[j*(M2-b-j) for j in range(1,min(M0,M2)+1)])
def gen(ar,w):
    for L in ar:
        for M in product(range(1,w+1),repeat=L): yield M

cnt={'bounded (M2<=b)':0,'log (M2=b+1)':0,'power-atlas (M2>=b+2)':0}
wit={'bounded (M2<=b)':None,'log (M2=b+1)':None,'power-atlas (M2>=b+2)':None}
mism=0
for M in gen([4],6):
    M0,M1,M2=M[0],M[1],M[2]
    if M0<M1:  # wide a=0
        b=M1-M0; A=A_order(M0,M1,M2)
        if M2<=b:
            k='bounded (M2<=b)'; assert A==0
        elif M2==b+1:
            k='log (M2=b+1)';
            if A!=0: mism+=1
        else:
            k='power-atlas (M2>=b+2)';
            if A<=0: mism+=1
        cnt[k]+=1
        if wit[k] is None: wit[k]=(M,f"b={b},A={A}")
print("wide a=0 sub-case census (arity-4, w<=6):")
for k in cnt: print(f"  {k:24s} count={cnt[k]:4d}  witness {wit[k]}")
print("A-formula vs boundary mismatches:", mism, "(0 = A=0 iff M2<=b+1 confirmed)")
print()
print("per-minor CoV: |det F_sigma|^{-M2} over free M0xM0 minor box -> INT finite iff M2 < 1 (codim{det=0}=1).")
print("  => for M2>=1 the NAIVE per-dominant-minor cover DIVERGES; must use the (r,s) source atlas over ALL of F.")
print("  (the milder order-A density comes from F's OTHER minors; a single-minor CoV overcounts.)")
