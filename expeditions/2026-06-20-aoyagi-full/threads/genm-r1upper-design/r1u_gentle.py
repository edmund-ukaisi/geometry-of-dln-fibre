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

# Q1: is a GENTLE binding cut (a=(M0-t)(M1-t) <= M1-t, i.e. M0-t<=1) always available at EVERY
#     recursion level along SOME binding path?  If yes, the multiplier reduces at all rank(B)>=1
#     (power loss only at B=0). Follow the recursion choosing gentle cuts when possible.
def gentle_path_exists(M):
    M=tuple(M)
    if len(M)-1<2: return True
    for t in binding_cuts(M):
        a=(M[0]-t)*(M[1]-t)
        if M[0]-t<=1:                      # gentle at this level (a<=M1-t)
            if gentle_path_exists((t,)+M[2:]): return True
    return False

tot=0; nogentle=0; ex=[]
for L in range(2,6):
  for M in itertools.product(range(1,5),repeat=L+1):
    if minAdmRec(M)==0: continue
    tot+=1
    if not gentle_path_exists(M): nogentle+=1; ex.append(M)
print(f"L>=2, widths1..4: chains with minAdm>0 = {tot}")
print(f"  chains with NO all-gentle binding path (some level forces a>M1-t): {nogentle}")
for e in ex[:15]: print("   forced non-gentle:",e, "binding cuts top-level:",binding_cuts(e))
