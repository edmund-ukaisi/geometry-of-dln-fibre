import itertools
from fractions import Fraction as F
def admBound(M,j,L): return min(M[0],M[1]) if j==0 else M[j+1]
def adm(M):
    L=len(M)-1; rngs=[range(admBound(M,j,L)+1) for j in range(L)]
    for T in itertools.product(*rngs):
        if all(T[i]>=T[j] for i in range(L) for j in range(L) if i<=j) and (L==0 or T[L-1]==0): yield tuple(T)
def Mval(M,T):
    L=len(M)-1; tot=0
    for j in range(L):
        tprev=M[0] if j==0 else T[j-1]; tot+=(tprev-T[j])*(M[j+1]-T[j])
    return tot
def minAdm(M): return min(Mval(M,T) for T in adm(M))

print("="*78)
print("CROSS-CHECK 3: the general-L path. Is it iterated rank-profile resolution? modulo-S2?")
print("="*78)
print("""
The cover's per-LAYER blow-up (one layer at a time, schurStateRed) is the WRONG resolution for L>=3:
it gives the per-node n=M_last increment, which overcounts (Erow not free).

The CORRECT resolution (Aoyagi/LR): blow up the rank-profile strata. minAdm = min_T Mval(M,T) where T
ranges over admissible rank PROFILES (t^(1)>=...>=t^(L)=0). The exceptional divisor for profile T has
the ratio Mval(M,T)/2; the RLCT = min over T = minAdm/2. This is NOT a per-layer recursion -- it is a
simultaneous resolution over the FULL profile lattice.

Two questions for the path:
 (Q-A) Is the general-L RLCT = min over rank-profile divisors (Mval(M,T)/2)?  -- the resolution form.
 (Q-B) Can the per-profile-divisor ratio Mval(M,T)/2 be proven MODULO-S2 (iterated monomial blow-ups
       + the S2 normal-crossing min rule), or does it need the Aoyagi rlct=½codim cite?
""")
# Q-A numeric: is minAdm achieved by SOME admissible profile, and is the structure a min over profiles?
# (definitional: minAdm = min_T Mval). The question is whether the rlct = this min (the resolution).
print("(Q-A) minAdm = min_T Mval is definitional. The geometric content (rlct = minAdm/2) is the")
print("      Aoyagi resolution theorem. Verify minAdm = min over profiles for the witnesses:")
for M in [[3,3,3,3],[2,2,2,3],[4,4,4,4]]:
    profs = sorted(adm(M), key=lambda T: Mval(M,T))
    print(f"  M={M}: minAdm={minAdm(M)} at T={profs[0]}; top few (T,Mval): {[(T,Mval(M,T)) for T in profs[:3]]}")
print()
print("(Q-B) THE KEY SCOPE QUESTION:")
print("""
  The rank-profile resolution = iterated blow-ups of the determinantal strata {rank(partial product)<=t}.
  Each such blow-up is a MONOMIAL/determinantal center. After full resolution, the loss is normal-crossing
  and the RLCT = min over exceptional divisors of (ord(Jac)+1)/(2 ord(loss)) = min_T Mval(M,T)/2.
  
  MODULO-S2 reachability: S2 = the normal-crossing 'rlct of a monomial = min axis ratio' + the additive/
  product rules. IF the rank-profile resolution can be EXHIBITED as an explicit iterated blow-up whose
  exceptional divisors carry Mval(M,T) as monomial data, THEN the value follows from S2 (the min rule)
  WITHOUT the Aoyagi rlct<=½codim cite -- the cite is replaced by an EXPLICIT resolution.
  
  BUT: exhibiting that resolution for ARBITRARY (L, widths) is exactly Aoyagi's hard theorem. The (2,2,2)
  precedent did it by hand (explicit charts). For general M, no explicit uniform resolution is in the repo
  -- so modulo-S2 general-M needs CONSTRUCTING the general iterated determinantal resolution (big, but
  in principle S2-only), OR importing the Aoyagi cite (rlct=½codim, beyond S2).
""")
print("VERDICT (Q-B): general-M-modulo-S2 is REACHABLE IN PRINCIPLE (explicit iterated determinantal")
print("  resolution => S2 min rule), but it is the FULL Aoyagi resolution construction -- NOT a small")
print("  per-layer recursion. The per-layer cover was the shortcut that FAILS for L>=3. So: either")
print("  (i) construct the general determinantal resolution (big, S2-only, the honest modulo-S2 path), or")
print("  (ii) cite Aoyagi rlct=½codim (beyond S2, the smaller-surface path).")
