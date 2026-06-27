import functools, itertools
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
    return arg,best
# Text(k) = M0 (k=0), tStar(k-1) (k>=1). q = deepest k<=L with Text(k)>0.
# q=0 would mean Text(1)=tStar(0)=0, i.e. ALL tStar=0 (since weakly decreasing). Then the achiever path is
# the all-zero rank: Text=[M0,0,0,...,0]. Then minAdm = Mval(all-zero) = sum_j (tprev-0)(M_{j+1}-0):
#   j=0: M0*M1; j>=1: 0*M_{j+1}=0. So minAdm would = M0*M1 (the all-zero path). Is that ever the MINIMIZER?
# Only if M0*M1 <= all other paths. For deep nets the layer-collapse usually beats it. Let me scan:
qzero=[]
for M in itertools.product(range(1,5),repeat=3):
    T,v=tstar(M)
    if all(t==0 for t in T):  # q would be 0 (Text(1)=0)
        qzero.append((M,T,v))
for M in itertools.product(range(1,4),repeat=4):
    T,v=tstar(M)
    if all(t==0 for t in T):
        qzero.append((M,T,v))
print(f"Achiever paths with ALL tStar=0 (would give q=0, Text=[M0,0,...]): {len(qzero)} cases")
for M,T,v in qzero[:8]:
    print(f"  M={M}: tStar={T}, minAdm={v}")
