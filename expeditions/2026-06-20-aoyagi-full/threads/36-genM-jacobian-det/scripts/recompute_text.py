# CORRECT: tach M = Fin.cons(M0, tStar). Text(0)=M0, Text(k+1)=tach(k). 
#   Text(1)=tach(0)=M0; Text(2)=tach(1)=tStar(0); Text(k+1)=tach(k)=tStar(k-1) for k>=1.
# So Text = [M0, M0, tStar0, tStar1, ..., tStar_{L-1}]. The identity boundary Text0=Text1=M0.
# For (1,2,2): tStar=(0,0), L=2. tach=Fin.cons(1, (0,0)) = (1,0,0). 
#   Text(0)=1, Text(1)=tach(0)=1, Text(2)=tach(1)=0. So Text=[1,1,0]. NOT [1,0,0]!
# leaf Text(L)=Text(2)=0 -> still row-empty. But Text(1)=1 now (identity boundary intact).
# q = deepest k<=L with Text(k)>0: Text0=1,Text1=1,Text2=0. q=1.
# Boundary q=1 E-block: r_1=Text(1)-Text(2)=1-0=1, c_1=Wext(1)-Text(2)=2-0=2. E-block 1x2 (NONEMPTY!). 
# So with the CORRECT tach (Text1=M0), the q=0 problem DISAPPEARS — q>=1 always (Text1=M0>=1).
# The deepest active E is at boundary q>=1, and Rmat_q is NOT the forced-0 Rmat_0. 
print("CORRECTED: tach = Fin.cons(M0, tStar) => Text(1) = M0 ALWAYS (identity boundary).")
print("So Text = [M0, M0, tStar0, tStar1, ...]. q = deepest Text>0 >= 1 (since Text1=M0>=1).")
print("The q=0 problem was a MISCOMPUTATION of tach (I used tStar directly; tach prepends M0).")
print()
# Recompute all the cases with correct tach:
import itertools, functools
@functools.lru_cache(None)
def minAdmRec(M):
    M=tuple(M); n=len(M)
    if n==1: return 0
    if n==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:]) for t in range(0,min(M[0],M[1])+1))
def tstar(M):
    M=tuple(M); L=len(M)-1
    bounds=[min(M[0],M[1])]+[M[j+1] for j in range(1,L)]
    best=None;arg=None
    def Mval(T):
        s=0
        for j in range(L):
            tp=M[0] if j==0 else T[j-1]; s+=(tp-T[j])*(M[j+1]-T[j])
        return s
    for T in itertools.product(*[range(b+1) for b in bounds]):
        if not all(T[j]<=T[i] for i in range(L) for j in range(L) if i<=j): continue
        if T[L-1]!=0: continue
        v=Mval(T)
        if best is None or v<best: best=v;arg=T
    return arg
for M in [(1,2,2),(2,2,4),(1,1,2),(2,2,2),(3,3,1,3),(3,3,3,3)]:
    M=tuple(M); L=len(M)-1; T=tstar(M)
    tach=(M[0],)+T  # Fin.cons(M0, tStar)
    Text=[M[0]]+[tach[k] for k in range(L)]  # Text(0)=M0, Text(k+1)=tach(k)
    q=max(k for k in range(L+1) if Text[k]>0)
    print(f"M={M}: tStar={T}, tach={tach}, Text={Text}, q={q} (>=1? {q>=1})")
