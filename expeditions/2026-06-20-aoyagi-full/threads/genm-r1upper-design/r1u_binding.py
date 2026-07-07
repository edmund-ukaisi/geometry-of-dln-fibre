from functools import lru_cache
import numpy as np
@lru_cache(None)
def minAdmRec(M):
    L=len(M)-1
    if L==0:return 0
    if L==1:return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def binding_cuts(M):
    v=minAdmRec(M); return [t for t in range(min(M[0],M[1])+1) if (M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:])==v]

print("Per-step identity:  J ≍ P_tail^{-(c'-a/2)} · P_full^{-a/2}")
print("  P_tail=(t,M2..ML) reduced chain ;  P_full=(M1..ML) FULL remaining product (coupling)")
print("At the BINDING cut(s): is the coupling P_full subordinate (a/2 < RLCT(P_full)) or does it bind?\n")
allsub=True
for M in [(2,2,2,2),(3,3,3,3),(4,4,4,4),(2,2,2,3),(4,4,2,2),(2,3,4),(1,2,3,4),(3,4,2,3),(2,2,2,2,2),(3,3,3,3,3)]:
    v=minAdmRec(M); cstar=v/2
    for t in binding_cuts(M):
        a=(M[0]-t)*(M[1]-t); tail=(t,)+M[2:]; full=M[1:]
        s1=cstar-a/2; rl1=minAdmRec(tail)/2
        s2=a/2;       rl2=minAdmRec(full)/2
        b1 = "BIND" if abs(s1-rl1)<1e-9 else ("OVER" if s1>rl1 else "slack")
        b2 = "BIND" if abs(s2-rl2)<1e-9 else ("OVER" if s2>rl2 else "sub")
        if s2>rl2+1e-9: allsub=False
        print(f"  M={M} t={t}: a={a}  P_tail{tail} s1={s1} vs RLCT {rl1} [{b1}] ; P_full{full} s2={s2} vs RLCT {rl2} [{b2}]")
print(f"\n  coupling P_full ever OVER its RLCT at a binding cut? {'YES' if not allsub else 'NO (always sub or exactly critical)'}")

print("\n"+"="*70)
print("L=2 vs L>=3: does the coupling factor P_full DECOUPLE from P_tail?")
print("="*70)
print("""
L=2, M=(M0,M1,M2), peel t:  P_tail=(t,M2)=top t rows of FREE A1·(nothing)... 
  actually tail chain = top-t-rows of A1 (free t×M2 matrix); P_full = all M1 rows of the
  SAME free A1. => P_tail, P_full are disjoint ROW BLOCKS of one FREE matrix A1 -> INDEPENDENT.
  On {P_tail=0} (top rows ->0), P_full = bottom rows = bounded below. COUPLING DECOUPLES.
  => single-chain (SchurCore corank) recursion suffices. (BUILT ∀(r,r,p).)

L>=3: P_tail = ||R_top·A2···A_{L-1}||,  P_full = ||A1·A2···A_{L-1}||  SHARE the deeper
  factors A2,...,A_{L-1}. P_full = P_tail + ||r_bot·A2···||, and BOTH degenerate when a
  shared deeper factor drops rank. COUPLING DOES NOT DECOUPLE. Moreover each further peel
  adds ANOTHER P_full^{(k)-a_k/2} (Aoyagi's diag(b) monomial): the coupling factors ACCUMULATE
  on shared variables -> must be resolved jointly = the (S,J) simultaneous blow-up.
""")
# numeric: confirm at L=2 the two row-blocks are independent (P_full - P_tail uses only bottom rows)
rng=np.random.default_rng(2)
A1=rng.uniform(-1,1,(4,2,2))  # (2,2,2), t=1: top row vs full
def f2(M):return (M**2).sum(axis=(-1,-2))
Ptail=f2(A1[:,:1,:]); Pfull=f2(A1)   # L=2: tail chain = A1 itself (M2 absorbed as identity-like); rows of free A1
print("L=2 sanity: P_full - P_tail depends only on bottom row (independent block):",
      np.allclose(Pfull-Ptail, f2(A1[:,1:,:])))
