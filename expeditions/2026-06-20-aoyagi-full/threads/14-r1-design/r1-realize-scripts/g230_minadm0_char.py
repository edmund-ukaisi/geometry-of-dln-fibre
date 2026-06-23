from itertools import product
def Mval(M,t):
    L=len(M)-1; tt=[M[0]]+list(t); return sum((tt[j-1]-tt[j])*(M[j]-tt[j]) for j in range(1,L+1))
def admissible(M,t):
    L=len(M)-1; tt=[M[0]]+list(t)
    if tt[-1]!=0: return False
    for j in range(1,L+1):
        if not(0<=tt[j]<=tt[j-1]): return False
        if tt[j]>M[j]: return False
    return True
def adm(M):
    L=len(M)-1; return [(t,Mval(M,t)) for t in product(*[range(M[0]+1)]*L) if admissible(M,t)]
def minAdm(M): return min(m for _,m in adm(M))

# EXACT characterization of minAdm=0. The summands (t_{j-1}-t_j)(M_j-t_j)=0 ⟺ t_{j-1}=t_j OR t_j=M_j.
# minAdm=0 ⟺ ∃ a weakly-decr admissible t (t_L=0) where at EACH j: no drop (t_{j-1}=t_j) OR width-saturated
# (t_j=M_j). Since t_L=0, the LAST summand needs t_{L-1}=0 (no drop, but then all prior also 0... ) or
# t_L=M_L=0. So M_L=0 forces the last summand=0 with any t_{L-1}. Let me characterize via a GREEDY/DP.
# CLAIM (test it): minAdm=0 ⟺ there's a "free descent path" 3=M_0... wait t_0=M_0. The condition:
# you can go from t_0=M_0 down to t_L=0 where each STEP either stays (t_{j-1}=t_j) or lands on M_j (saturate).
# A step DROPS only by saturating (t_j=M_j < t_{j-1}); a stay keeps t. To reach t_L=0 you need to drop to 0.
# Dropping to a value v at step j (v=M_j) requires M_j ≤ t_{j-1}. So: minAdm=0 ⟺ ∃ a sequence
# M_0 = s_0 ≥ s_1 ≥ ... ≥ s_L = 0 with each s_j ∈ {s_{j-1}} ∪ {M_j}  (stay or saturate-to-M_j), s_j ≤ s_{j-1}.
def minadm0_dp(M):
    # DP: reachable running ranks s_j (s_0=M_0), each step stay or drop-to-M_j (if M_j ≤ s_{j-1}), reach 0.
    L=len(M)-1; reach={M[0]}
    for j in range(1,L+1):
        nxt=set()
        for s in reach:
            # stay: only if the summand (s-s)(M_j-s)=0 — always (no drop). t_j=s, need s≤M_j (admissibility t_j≤M_j).
            if s <= M[j]: nxt.add(s)  # stay (t_j=t_{j-1}=s), needs s≤M_j
            # saturate: t_j = M_j, summand (s-M_j)(M_j-M_j)=0, needs M_j ≤ s (weakly-decr)
            if M[j] <= s: nxt.add(M[j])
        reach=nxt
    return 0 in reach
print("EXACT characterization (DP): minAdm M=0 ⟺ ∃ running-rank path M_0=s_0≥s_1≥…≥s_L=0,")
print("each step s_j ∈ {s_{j-1} (stay, needs s≤M_j)} ∪ {M_j (saturate, needs M_j≤s_{j-1})}.")
print("Verify DP matches brute-force minAdm=0:")
import random
random.seed(11); ok=True; n=0
for _ in range(300):
    L=random.randint(1,4); M=tuple(random.randint(0,3) for _ in range(L+1))
    bf = (minAdm(M)==0); dp = minadm0_dp(M)
    n+=1
    if bf!=dp: print(f"  MISMATCH M={M}: brute minAdm=0:{bf}, DP:{dp}"); ok=False
print(f"  {n} random M: DP matches brute-force minAdm=0: {ok}")
print()
# Now: is the DP-condition = a CLEAN geometric statement? Test the candidates against it.
print("The clean geometric reading of the DP condition:")
print("  minAdm=0 ⟺ you can descend M_0 → 0 by 'staying or saturating to M_j' at each layer — i.e. the")
print("  widths admit a zero-codim rank pattern. Equivalently: NO layer forces a positive-codim drop.")
print("  A layer j forces positive codim ⟺ you must drop t_{j-1}→t_j with t_{j-1}>t_j>M_j (a drop NOT to")
print("  the saturation M_j and NOT a stay) — but that's exactly when no free path exists.")
print()
# Geometric-leaf = the loss core is a unit at the generic point of the minimal stratum (IsUnit, candidate c).
# IsUnit residual core ⟺ the minimal-codim stratum is codim 0 ⟺ minAdm=0. So (a)=(c)=minAdm=0.
print("(a) achiever T* has Mval=0 = minAdm=0 (tautological, T*=argmin). ✓")
print("(c) IsUnit residual core ⟺ the minimal stratum is codim-0 ⟺ minAdm=0 (the core vanishes to a unit")
print("    on the codim-0 stratum — no positive-codim singular locus). ⟺ (a). ✓")
print("(b) schurState-bottomed (M_0=0 or M_1=0) ≠ minAdm=0 (counterexample (2,2,0): minAdm=0 but M_0=M_1=2).")
print("    So (b) is WRONG as the leaf RHS — it's too strong (misses leaves like (2,2,0) where schurState")
print("    still applies but minAdm is already 0). DON'T use (b).")
