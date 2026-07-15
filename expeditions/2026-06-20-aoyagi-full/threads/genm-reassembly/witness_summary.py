from functools import lru_cache
def redchain(t,M): return (t,)+M[2:]
@lru_cache(None)
def minAdm(M):
    M=tuple(M); n=len(M)
    if n==1: return 0
    if n==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm(redchain(t,M)) for t in range(min(M[0],M[1])+1))
def argmin_ts(M):
    m=minAdm(M); return m,[t for t in range(min(M[0],M[1])+1) if (M[0]-t)*(M[1]-t)+minAdm(redchain(t,M))==m]

# Witness for the residual GAP: good-branch binding cut with b + deepTailMin > max(M2,M3) (residual non-integrable).
# L=1 chains. residual det+(Z Z^T)^{-b/2}, Z=A2 (M2 x M3), integrable over A2 iff b <= |M2-M3|.
print("L=1 good-branch binding strict-shell cuts with residual NON-integrable (b > |M2-M3|):")
print(f"{'M':>16} {'t*':>3} {'u':>3} {'a':>3} {'b':>3} {'M2':>3} {'M3':>3} {'|M2-M3|':>7} {'b<=|M2-M3|?':>11} {'minAdm':>7} {'aplusb<=M2':>10}")
witnesses=[]
for M0 in range(2,6):
 for M1 in range(2,6):
  for M2 in range(1,7):
   for M3 in range(1,7):
    M=(M0,M1,M2,M3); dtm=min(M2,M3)
    if dtm>M1: continue
    m,ts=argmin_ts(M)
    for tstar in ts:
     r=min(M0-tstar,M1-tstar)
     for j in range(1,r):
      u=tstar+j; a=M0-u; b=M1-u
      if a>=1 and b>=1:
       resid_ok = b <= abs(M2-M3)      # integrable
       aplusb = (a+b)<=M2
       if not resid_ok:
        witnesses.append((M,tstar,u,a,b))
        print(f"{str(M):>16} {tstar:>3} {u:>3} {a:>3} {b:>3} {M2:>3} {M3:>3} {abs(M2-M3):>7} {str(resid_ok):>11} {m:>7} {str(aplusb):>10}")
print(f"\nTotal good-branch cuts with NON-integrable deep-Gram residual: {len(witnesses)}")
print("Note: ALL still satisfy a+b<=M2 (the L=0 incidence scope) -> the L=0 scope does NOT catch this.")
