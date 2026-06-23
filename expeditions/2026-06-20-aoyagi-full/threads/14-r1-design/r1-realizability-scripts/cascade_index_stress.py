from itertools import product
# CONSTRUCT a case where M_s < M_{s+1} (so admBound's M_{s+1} bound is WEAKER than the needed M_s),
# to confirm: (a) the direct admBound bound t_s ≤ M_{s+1} does NOT imply t_s ≤ M_s, but
#             (b) admissibility (weak-decrease + admBound) STILL gives t_s ≤ M_s.
# This pins whether the index-shift is a real gap or cosmetic.
def admBound(M,j):
    return min(M[0],M[1]) if j==0 else M[j+1]
def tPrev(M,T,j): return M[0] if j==0 else T[j-1]
def admPred(M,T):
    L=len(T)
    b1=all(T[j]<=admBound(M,j) for j in range(L))
    b2=all(not(i<=j) or T[j]<=T[i] for i in range(L) for j in range(L))
    b3=all(T[j]==0 for j in range(L) if j==L-1)
    return b1 and b2 and b3
def Adm(M):
    L=len(M)-1
    return [T for T in product(*[range(admBound(M,j)+1) for j in range(L)]) if admPred(M,list(T))]

# M with an INCREASING step (M_s < M_{s+1}) at an interior layer: M=(2,1,3,2), L=3.
# Here at s=1: M_1=1, M_2=3 → M_{s+1}=M_2=3 > M_1=1. The needed t_1 ≤ M_1=1; admBound gives t_1 ≤ M_2=3.
for M in [(2,1,3,2),(1,2,2,1),(3,1,1,2),(2,3,1,2)]:
    L=len(M)-1
    adm=Adm(M)
    # check EVERY admissible T: does t_s ≤ M_s hold (Core gate)? And would admBound-direct fail?
    all_gate_ok=True; admbound_would_fail=False
    for T in adm:
        for s in range(L):
            ts=T[s]; Ms=M[s]
            if ts > Ms: all_gate_ok=False
            # admBound-direct bound for this s:
            ab = admBound(M,s)  # = M_{s+1} for s≥1
            if s>=1 and ab > Ms:  # admBound weaker than needed at this s
                admbound_would_fail=True
    print(f"M={M}: |Adm|={len(adm)}; Core gate t_s≤M_s holds ∀ admissible T: {all_gate_ok}; "
          f"admBound-direct WEAKER than M_s at some s≥1: {admbound_would_fail}")
print()
print("⟹ At M with an increasing step (M_s < M_{s+1}), admBound's t_s ≤ M_{s+1} is STRICTLY WEAKER than")
print("  the needed t_s ≤ M_s — so a direct admBound discharge would NOT close ht there. But the Core gate")
print("  t_s ≤ M_s STILL holds for every admissible T (via weak-decrease ∘ admBound-at-(s-1)). So the")
print("  inequality is TRUE, but the PROOF must route through weak-decrease, NOT admBound at s.")
print()
# Confirm the weak-decrease route explicitly for one increasing-step case:
M=(2,1,3,2); adm=Adm(M)
print(f"Explicit weak-decrease route, M={M}:")
for T in adm[:6]:
    L=len(M)-1
    route=[]
    for s in range(L):
        if s==0:
            route.append(f"t_0={T[0]}≤min(M0,M1)={min(M[0],M[1])}≤M_0={M[0]}")
        else:
            # t_s ≤ t_{s-1} ≤ admBound(s-1)=M_s
            ab=admBound(M,s-1)
            route.append(f"t_{s}={T[s]}≤t_{s-1}={T[s-1]}≤admB({s-1})={ab}; M_{s}={M[s]}")
    print(f"  T={T}: " + " | ".join(route))
