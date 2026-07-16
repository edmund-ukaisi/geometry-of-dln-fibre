"""
satred: the A-vs-2Delta split governing whether the NAIVE pointwise density domination reaches the
saturated-shell threshold 1/2 minAdm(M), or UNDERSHOOTS (needing the joint rank-sector resolution).

  2Delta := minAdm(redChain u M) - minAdm(M)          (joint RLCT headroom, free from arity-IH)
  A      := max_{1<=j<=min(u,M2)} j*(M2 - b - j)       (pointwise density order at the rank-drop origin)
Naive pointwise fold consumes A/2:  reaches threshold  <=>  A <= 2Delta.
Finiteness ITSELF always holds to 1/2 minAdm(M) (Codex determinantal m_I=minAdm(M) at k=u+b=M1; and
(I)=RMBTF(M)|_{P invertible}, Aoyagi) -- only the ROUTE via the IH RMBTF(redChain u M) splits.
"""
def minAdmRec(M):
    M=list(M); L1=len(M)
    if L1==1: return 0
    if L1==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec([t]+M[2:]) for t in range(min(M[0],M[1])+1))

def A_order(u,M2,b):
    return max([0]+[j*(M2-b-j) for j in range(1,min(u,M2)+1)])

print(f"{'M':>14} {'u':>2} {'b':>2} {'M2':>3} {'minAdm(M)':>9} {'minAdm(red)':>11} {'2Delta':>6} {'A':>3} {'route':>12}")
undershoot=[]
for M0 in range(1,5):
  for M1 in range(M0,6):          # a=0 saturated: M0<=M1
    for M2 in range(1,6):
      for M3 in range(1,6):
        M=(M0,M1,M2,M3); u=M0; b=M1-M0
        mM=minAdmRec(list(M)); mR=minAdmRec([u,M2,M3]); twoD=mR-mM; A=A_order(u,M2,b)
        if A>twoD: undershoot.append((M,u,b,M2,mM,mR,twoD,A))
shown=[(1,2,2,2),(1,3,3,3),(1,2,3,3),(2,3,2,2),(2,2,2,2),(2,2,3,3),(3,3,3,3),(2,3,4,4),(1,1,2,2),(1,2,4,4)]
for M in shown:
    M0,M1,M2,M3=M; u=M0;b=M1-M0
    mM=minAdmRec(list(M));mR=minAdmRec([u,M2,M3]);twoD=mR-mM;A=A_order(u,M2,b)
    print(f"{str(M):>14} {u:>2} {b:>2} {M2:>3} {mM:>9} {mR:>11} {twoD:>6} {A:>3} {'REACHES' if A<=twoD else 'UNDERSHOOTS':>12}")
print(f"\nTotal a=0 shells scanned (M0<=M1<=5, M2,M3<=5): undershoot (A>2Delta) count = {len(undershoot)}")
print("u=1 undershoot count =", sum(1 for x in undershoot if x[1]==1), "(should be 0: u=1 always reaches)")
print("min u among undershoot =", min((x[1] for x in undershoot), default=None))
