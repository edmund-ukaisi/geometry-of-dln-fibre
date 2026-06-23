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

# ADJUDICATE: minAdm M = 0 ⟺ geometric-leaf. First, CHARACTERIZE which M have minAdm=0.
# Mval(M,t) = Σ_{j=1..L} (t_{j-1}-t_j)(M^j - t_j), tt_0=M^0. minAdm=0 ⟺ ∃ admissible t with every summand 0.
# Each summand (t_{j-1}-t_j)(M_j - t_j) = 0 ⟺ t_{j-1}=t_j OR t_j=M_j. Since t is weakly-decr, t_L=0:
# the all-zero t (t_j=0 all j) gives Mval = Σ (t_{j-1}-0)(M_j-0)... no: t_0=M_0, t_1=...=0 ⟹ summand_1 =
# (M_0-0)(M_1-0)=M_0 M_1 (if t_1=0). So all-zero t is NOT Mval-0 in general.
# minAdm=0 ⟺ ∃ admissible t making EVERY summand 0. Let me find which M admit such t.
print("CHARACTERIZE minAdm M = 0 (the leaf condition). Mval summand_j = (t_{j-1}-t_j)(M_j - t_j) = 0")
print("  ⟺ t_{j-1}=t_j (no rank drop at j) OR t_j=M_j (the width saturated). minAdm=0 ⟺ ∃ admissible t")
print("  (weakly-decr, t_L=0, 0≤t_j≤M_j) with EVERY summand 0.")
print()
for M in [(2,2,2),(2,2,0),(0,0,2),(1,1,1),(0,0,0),(2,0,2),(0,2,0),(3,2,3),(1,0,1),(2,1,2),(0,1,0),(1,1,0),(2,0,0)]:
    L=len(M)-1; strata=adm(M); mA=minAdm(M)
    achievers=[t for t,m in strata if m==mA]
    leaf = (mA==0)
    # what does minAdm=0 require? characterize: the all-zero-after-some-point t. Find a Mval-0 t if exists.
    zero_t = [t for t,m in strata if m==0]
    print(f"  M={M}: minAdm={mA} {'LEAF' if leaf else 'BRANCH'}; Mval-0 strata: {zero_t if zero_t else 'NONE'}")
print()
# THE CHARACTERIZATION: when is there an admissible t with all summands 0?
print("PATTERN: minAdm=0 ⟺ ? Let me check the candidates.")
print("Candidate (a): no positive-codim resolvable defect = the achiever T* has Mval=0.")
print("  minAdm = Mval(T*) by def (T* = argmin). So minAdm=0 ⟺ Mval(T*)=0 ⟺ (a) TAUTOLOGICALLY. ✓ (a)=minAdm=0.")
print()
# Candidate: minAdm=0 ⟺ the chain is 'rank-saturated' — every layer either has no drop or saturates.
# Geometrically: minAdm=0 ⟺ the MINIMAL stratum is codim 0 ⟺ the loss core is ALREADY a unit at the
# generic point of that stratum ⟺ NO further blow-up reduces codim ⟺ LEAF. Let me verify the M_s structure.
print("GEOMETRIC LEAF candidates — are they the same as minAdm=0?")
print("  (b) red≡0 / schurState bottomed: schurState M = (M_0-1,M_1-1,M_{≥2}); 'bottomed' when M_0=0 or M_1=0")
print("     (can't drop further). Is minAdm=0 ⟺ M_0=0 or M_1=0? Check: (2,2,0) minAdm=0 but M_0=M_1=2≠0.")
print("     So (b) ≠ minAdm=0! (2,2,0) is a leaf (minAdm=0) yet schurState still applies (M_0,M_1≥1). fm3's note.")
