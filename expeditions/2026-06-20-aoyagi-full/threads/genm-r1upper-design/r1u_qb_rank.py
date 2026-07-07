from functools import lru_cache
import itertools
@lru_cache(None)
def minAdmRec(M):
    L=len(M)-1
    if L==0:return 0
    if L==1:return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def binding_cuts(M):
    v=minAdmRec(M); return [t for t in range(min(M[0],M[1])+1) if (M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:])==v]
# Codex's risk: the Gram atom (in pieces 4/5/7) needs rank(Q_b)=M1-t achievable, i.e. Q_b (M1-t rows of
# the M1×M_L tail product) can be full row rank => need M1-t <= min(M2,...,M_L) (deeper widths).
# When a DEEPER width bottlenecks (M1-t > min(M2..ML)), Q_b is FORCED rank-deficient -> atom unavailable
# -> that chart needs the joint recursion (= the (S,J) coupling). Check at binding cuts.
print("At binding cut t: is M1-t <= min(M2,...,ML)? (Y => Q_b CAN be full rank, Gram atom applies directly;")
print(" N => deeper bottleneck forces Q_b rank-deficient -> that chart recurses (the (S,J) coupling)).\n")
tot=0; bottleneck=0; ex=[]
for L in range(2,6):
  for M in itertools.product(range(1,5),repeat=L+1):
    if minAdmRec(M)==0 or L<2: continue
    tot+=1
    for t in binding_cuts(M):
        deeper=M[2:]   # M2..ML
        mindeep=min(deeper) if deeper else 10**9
        if (M[1]-t) > mindeep:
            bottleneck+=1; ex.append((M,t,M[1]-t,mindeep)); break
print(f"chains×(a binding cut) checked: {tot}")
print(f"  with a deeper bottleneck (Q_b forced rank-deficient => chart recurses): {bottleneck}")
for e in ex[:10]: print(f"   M={e[0]} t={e[1]}: M1-t={e[2]} > min(deeper)={e[3]}")
print("""
=> When bottlenecked, the Gram atom does not apply on that chart directly; Q_b's rank drop is a DEEPER
   boundary's drop -> resolved by the (S,J) recursion (consistent with ADDENDUM 2). Piece 3 (split A,
   Γ-explicit) is UNAFFECTED (no atom); the risk lives entirely in pieces 4/5/7, as designed.
""")
