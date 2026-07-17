"""
Exact-integer backbone checks for the d<=1 native dispatch of innerCorankDescent_lt_top.
minAdmRec transcribed EXACTLY from RouteMLayerSplit.lean:
  n<=1 -> 0 ; n==2 -> M0*M1 ; n>=3 -> min_{t in 0..min(M0,M1)} (M0-t)(M1-t) + minAdmRec(redChain t M).
redChain t M = [t] + M[2:].
"""
from functools import lru_cache
from itertools import product

@lru_cache(maxsize=None)
def minAdmRec(M):  # M a tuple
    n = len(M)
    if n <= 1: return 0
    if n == 2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t) + minAdmRec((t,)+M[2:])
               for t in range(0, min(M[0],M[1])+1))

def redChain(t, M): return (t,)+M[2:]
def peelCharge(M, t): return (M[0]-t)*(M[1]-t)

def dens_order_A(M0, M1, M2):
    # a=0 wide waist density order A = max_{j>=1} j*(M2 - b - j), b = M1 - M0. (satred table)
    b = M1 - M0
    best = 0
    for j in range(1, min(M0, M2)+1):
        best = max(best, j*(M2 - b - j))
    return best

def gen_chains(arities, wmax):
    for L in arities:  # number of widths
        for M in product(range(1, wmax+1), repeat=L):
            yield M

# ---------- 1. cut-soundness (should be 0 fails; it is a proved Lean lemma) ----------
fails_cutsound = 0
total_cuts = 0
# ---------- 2. min-over-strata = minAdm for the FRONT rank-sector (a=0 waist and general) ----------
# For a cut t, the corank rank-drop strata reduce to redChain u' M with u' the deepened cut, charge peelCharge(u').
# The claim: min_{u' in [t, min(M0,M1)]} [ peelCharge(M,u') + minAdmRec(redChain u' M) ] reaches minAdm-consistent value.
strata_fail = 0
strata_total = 0
# ---------- 3. d<=1 dispatch census + a>=u qbox-dim census ----------
census = {'d0_a0':0,'d0_b0':0,'d0_both':0,'d1_aLTu':0,'d1_aGEu':0}
a0_Agt2D = 0; a0_total = 0
aGEu_qbox_oneshot = {'q=Mlast':0,'q=M2':0}; aGEu_total = 0

for M in gen_chains([4,5], 6):
    n = len(M); M0,M1 = M[0],M[1]
    mA = minAdmRec(M)
    for t in range(1, min(M0,M1)+1):
        a = M0-t; b = M1-t; d = min(a,b); u = t
        # cut-soundness
        total_cuts += 1
        if mA > peelCharge(M,t) + minAdmRec(redChain(t,M)):
            fails_cutsound += 1
        if d > 1:
            continue
        # dispatch census
        if d == 0:
            if a==0 and b==0: census['d0_both']+=1
            elif a==0: census['d0_a0']+=1
            else: census['d0_b0']+=1
        else:  # d==1
            if a < u: census['d1_aLTu']+=1
            else: census['d1_aGEu']+=1

        # a=0 waist: A vs 2Delta
        if a==0 and n>=3:
            M2 = M[2]
            A = dens_order_A(M0,M1,M2)
            Delta2 = minAdmRec(redChain(M0,M)) - mA   # = 2*Delta
            a0_total += 1
            if A > Delta2: a0_Agt2D += 1
            # front rank-sector min over strata s=u-r (cuts s in 0..u=M0)
            vals = [ (M0-s)*(M1-s) + minAdmRec(redChain(s,M)) for s in range(0, M0+1) ]
            strata_total += 1
            if min(vals) != mA: strata_fail += 1

        # d=1 a>=u: qbox one-shot dim census (pivot Gram det(Qtil Qtil^T)^{-a/2}, Qtil is u x q)
        if d==1 and a>=u and n>=3:
            aGEu_total += 1
            q_last = M[-1]; q_M2 = M[2]
            # one-shot qbox on pivot Gram: b_box=u rows, q_box=q, conv iff u<=q and a < q-u+1
            if u <= q_last and a < q_last - u + 1: aGEu_qbox_oneshot['q=Mlast'] += 1
            if u <= q_M2 and a < q_M2 - u + 1: aGEu_qbox_oneshot['q=M2'] += 1

print("cut-soundness fails:", fails_cutsound, "/", total_cuts)
print("front rank-sector min==minAdm fails (a=0):", strata_fail, "/", strata_total)
print("d<=1 dispatch census:", census)
print("a=0 waist: A>2Delta count:", a0_Agt2D, "/", a0_total)
print("d=1 a>=u count:", aGEu_total, " qbox one-shot closes:", aGEu_qbox_oneshot)
