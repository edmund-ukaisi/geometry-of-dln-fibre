from itertools import product
# Verify Mval M T >= 0 for all admissible T (so (Mval M T).toNat is faithful, fm3's codim type).
# Mval(M,t) = Σ_j (t_{j-1}-t_j)(M_j - t_j), t_0=M_0, admissible: weakly-decr, t_L=0, 0≤t_j≤M_j.
def Mval(M,t):
    L=len(M)-1; tt=[M[0]]+list(t); return sum((tt[j-1]-tt[j])*(M[j]-tt[j]) for j in range(1,L+1))
def admissible(M,t):
    L=len(M)-1; tt=[M[0]]+list(t)
    if tt[-1]!=0: return False
    for j in range(1,L+1):
        if not(0<=tt[j]<=tt[j-1]): return False
        if tt[j]>M[j]: return False
    return True
print("Verify Mval ≥ 0 on admissible T (so (Mval).toNat faithful) — each summand (t_{j-1}-t_j)(M_j-t_j):")
print("  t_{j-1}-t_j ≥ 0 (weakly decreasing, admissibility); M_j-t_j ≥ 0 (t_j ≤ M_j, admissibility).")
print("  ⟹ each summand ≥ 0 ⟹ Mval ≥ 0. So (Mval M T).toNat is faithful on Adm M.")
print()
allok = True
for M in [(2,2,2),(3,2,3),(2,2,2,2),(4,3,2),(2,3,2),(3,3,3),(2,1,2),(3,1,3),(4,4,4)]:
    L=len(M)-1
    for t in product(*[range(M[0]+1)]*L):
        if admissible(M,t):
            if Mval(M,t) < 0:
                print(f"  NEGATIVE: M={M} t={t} Mval={Mval(M,t)}"); allok=False
print(f"All admissible Mval ≥ 0 across test cases: {allok}  (each summand ≥0 by admissibility ✓)")
print()
print("So fm3's codim = (Mval M T).toNat is exact (no information loss) on admissible T.")
print("My §2 witness: {T // T ∈ Adm M ∧ codim c = (Mval M T).toNat} — the .toNat faithful since Mval≥0.")
