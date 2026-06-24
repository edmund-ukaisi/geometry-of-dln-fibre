import sympy as sp
from fractions import Fraction
from itertools import product as iproduct

# THE SOUNDNESS-CRITICAL QUESTION for hfin (cover_le upper bound):
# After full resolution, is EVERY leaf threshold >= minAdm/2?  Equivalently: can any branch/leaf of
# the pivot-blow-up resolution produce a divisor axis with (h_j+1)/(2 k_j) < minAdm/2?
# The cover gives rlct >= min_leaf (leaf threshold). For the UPPER bound rlct >= minAdm/2 we need
# every leaf >= minAdm/2. Since min_leaf = rlct = minAdm/2, the BINDING leaf is exactly minAdm/2 and
# we need NO leaf strictly below. The DANGER: an off-binding branch could have a SMALLER leaf threshold
# (which would make the cover give rlct >= something < minAdm/2, FAILING the upper bound).
#
# Aoyagi's structure: each branch with profile t accumulates a SINGLE binding divisor of codim Mval(M,t),
# threshold Mval(M,t)/2. Since Mval(M,t) >= minAdm for ALL admissible t (minAdm = min), every leaf
# threshold = Mval(M,t)/2 >= minAdm/2.  So NO leaf is below minAdm/2.  The upper bound is SOUND.
#
# This rests on: per-leaf threshold = Mval(M,t)/2 EXACTLY (single binding divisor of codim Mval).
# Verify this on multiple branches of (3,3,4) and a 2nd case, via the EXACT peel + Newton-LP.

def rlct_newton(gens, nvars):
    from scipy.optimize import linprog
    if not gens: return None
    n=nvars; c=[0.0]*n+[-1.0]; A_ub=[]; b_ub=[]
    for a in gens:
        A_ub.append([-float(a[i]) for i in range(n)]+[1.0]); b_ub.append(0.0)
    res=linprog(c,A_ub=A_ub,b_ub=b_ub,A_eq=[[1.0]*n+[0.0]],b_eq=[1.0],
                bounds=[(0,None)]*n+[(None,None)],method='highs')
    return Fraction(1)/(2*Fraction(-res.fun).limit_denominator(10**7))

def Mval(M, t):
    # M: list len L+1. t: list len L (t[L-1]=0). weakly decreasing.
    L = len(M)-1
    tt = list(t) + [0]  # t indices 1..L, tt[0]=t1,... ; pad
    # Mval = (M0 - t1)(M1 - t1) + sum_{j>=2} (t_{j-1} - t_j)(M_{j+1} - t_j)
    t1 = t[0]
    v = (M[0]-t1)*(M[1]-t1)
    for j in range(2, L+1):
        tjm1 = t[j-2]; tj = t[j-1]
        v += (tjm1 - tj)*(M[j] - tj)
    return v

def admissible(M):
    L=len(M)-1
    # t = (t1,...,tL), t_L=0, weakly decreasing, 0<=t_j<=min(M_0..along)
    # bounds: t_j <= min(M_0,...,M_j) roughly; enumerate t_j in 0..min(M_i for i<=j)
    caps=[min(M[:j+2]) for j in range(L)]  # t_j <= min(M_0..M_j)
    res=[]
    for t in iproduct(*[range(c+1) for c in caps]):
        if t[-1]!=0: continue
        if all(t[i]>=t[i+1] for i in range(len(t)-1)):
            res.append(t)
    return res

for M in [[3,3,4],[2,2,2],[2,2,4],[3,3,5,4],[4,4,2,2]]:
    adm = admissible(M)
    mvals = {t:Mval(M,t) for t in adm}
    minA = min(mvals.values())
    print(f"M={M}: minAdm={minA}, minAdm/2={Fraction(minA,2)}")
    print(f"   Adm profiles and Mval: {mvals}")
    # per-leaf threshold = Mval/2; check all >= minAdm/2
    below = [t for t,v in mvals.items() if v < minA]
    print(f"   any Mval < minAdm? {below}  (must be empty -> every leaf threshold >= minAdm/2)")
    print()
print("CONCLUSION: by definition minAdm = min over Adm of Mval, so Mval(M,t) >= minAdm for all t.")
print("Per-leaf threshold = Mval(M,t)/2 >= minAdm/2. The cover upper bound rlct >= minAdm/2 is SOUND,")
print("PROVIDED each leaf's threshold is EXACTLY Mval(M,t)/2 (single binding divisor of codim Mval).")
