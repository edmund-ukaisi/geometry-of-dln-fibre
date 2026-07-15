"""
General-L exponent-gate arithmetic for the incidence-route capstone (brick B).
Matches the Lean recursion RouteMLayerSplit.minAdmRec exactly:
  minAdm(Fin1)=0; minAdm(Fin2)=M0*M1;
  minAdm(>=3 widths)= min_{t<=min(M0,M1)} [(M0-t)(M1-t) + minAdm(redChain t M)],
  redChain t M = (t, M2, ..., M_last).
"""
import itertools
from functools import lru_cache

def minAdm(M):
    M = tuple(M)
    L1 = len(M)                # number of widths = L+1
    if L1 == 1: return 0
    if L1 == 2: return M[0]*M[1]
    best = None
    for t in range(0, min(M[0],M[1])+1):
        red = (t,) + M[2:]     # redChain t M
        v = (M[0]-t)*(M[1]-t) + minAdm(red)
        if best is None or v < best: best = v
    return best

minAdm = lru_cache(maxsize=None)(minAdm)

def minAdm3(M0,M1,M2):
    return min((M0-s)*(M1-s)+s*M2 for s in range(0,min(M0,M1)+1))

# ---- Verify recursion anchors vs Lean ----
assert minAdm((2,2,2))==3, minAdm((2,2,2))
assert minAdm((3,3,4))==8
assert minAdm((4,4,2,2))==4
assert minAdm((3,3,2,2))==4
print("anchors OK: minAdm(2,2,2)=3, (3,3,4)=8, (4,4,2,2)=4, (3,3,2,2)=4")

# widths to sweep, arities 3..5
W = range(1,7)
def chains(arity):
    return itertools.product(W, repeat=arity)

# ---- FACT F2: minAdm(redChain t M) <= t*M2  (the p=0 peel bound) ----
# ---- FACT F1 (NAIVE gate): minAdm(M) <= (M0-s)(M1-s) + s*M2  for all s<=min(M0,M1) ----
# ---- FACT F1L (NAIVE, last): minAdm(M) <= (M0-s)(M1-s) + s*M_last ----
# ---- FACT F3 (TIGHT gate / parent inf'_le): minAdm(M) <= (M0-s)(M1-s)+minAdm(redChain s M), s<=min(M0,M1) ----
# ---- FACT REC: minAdm(M) == min_{t<=min(M0,M1)} [(M0-t)(M1-t)+minAdm(redChain t M)] ----
f2_fail=f1_fail=f1L_fail=f3_fail=rec_fail=0
minAdm_le_minAdm3_fail=0
tight_eq_examples=[]
naive_vs_tight_gap=[]   # cases where min_s naive (s*M2) > minAdm (i.e. front strata don't bind at T1)
n_checked=0
for arity in (3,4,5):
    for M in chains(arity):
        M=tuple(M)
        mm=minAdm(M); M0,M1,M2=M[0],M[1],M[2]; Mlast=M[-1]
        n_checked+=1
        mb=min(M0,M1)
        # F2
        for t in range(0, mb+1):
            red=(t,)+M[2:]
            if minAdm(red) > t*M2: f2_fail+=1
        # F1 naive (M2), F1L naive (last), F3 tight, over s<=min(M0,M1)
        for s in range(0, mb+1):
            red=(s,)+M[2:]
            if mm > (M0-s)*(M1-s)+s*M2: f1_fail+=1
            if mm > (M0-s)*(M1-s)+s*Mlast: f1L_fail+=1
            if mm > (M0-s)*(M1-s)+minAdm(red): f3_fail+=1
        # REC exact
        rec = min((M0-t)*(M1-t)+minAdm((t,)+M[2:]) for t in range(0,mb+1))
        if rec != mm: rec_fail+=1
        # minAdm <= minAdm3
        if mm > minAdm3(M0,M1,M2): minAdm_le_minAdm3_fail+=1
        # naive-vs-tight gap: does min_s (naive s*M2) exceed minAdm?
        naive_min = min((M0-s)*(M1-s)+s*M2 for s in range(0,mb+1))  # = minAdm3
        if naive_min > mm:
            naive_vs_tight_gap.append((M, naive_min, mm))

print(f"\nchecked {n_checked} chains (arity 3,4,5, widths 1..6)")
print(f"F2  minAdm(redChain t M) <= t*M2         fails: {f2_fail}")
print(f"F1  NAIVE minAdm(M) <= (M0-s)(M1-s)+s*M2 fails: {f1_fail}")
print(f"F1L NAIVE minAdm(M) <= ...+s*M_last      fails: {f1L_fail}")
print(f"F3  TIGHT minAdm(M) <= ...+minAdm(red s) fails: {f3_fail}   (=parent inf'_le, must be 0)")
print(f"REC minAdm==min_t[...]                    fails: {rec_fail}   (must be 0)")
print(f"minAdm(M) <= minAdm3(M0,M1,M2)           fails: {minAdm_le_minAdm3_fail}")
print(f"\nNAIVE-vs-TIGHT: #chains where min_s(s*M2)=minAdm3 STRICTLY > minAdm(M): {len(naive_vs_tight_gap)}")
for ex in naive_vs_tight_gap[:12]:
    print(f"   M={ex[0]}: minAdm3(front-naive)={ex[1]}  >  minAdm(full)={ex[2]}")
