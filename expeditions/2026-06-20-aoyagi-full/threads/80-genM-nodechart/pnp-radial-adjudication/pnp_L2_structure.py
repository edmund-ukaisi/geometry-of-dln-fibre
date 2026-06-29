import sympy as sp
# L=2: M=(M0,M1,M2). One genuine boundary s=1, identity boundary s=0, leaf s=2.
# Text=[M0, M0, t1] where t1 = the achiever drop at boundary 1 (=Text_2=Text_L, the leaf rank).
# Wext=[M0,M1,M2]. flatDim = M0*M1 + M1*M2.
# minAdm(M0,M1,M2): identity boundary fixes Text1=M0, then peel boundary1: codim depends on t1.
#   minAdm = min over t [ (M0-t)? no -- the chain peels (front=Text1=M0, next=M2) at rank t1=Text2:
#   actually minAdm = min_{t1} [ (Text1 - t1)*(Wext1? ) ...]. Let me just compute via the recursion.
def redChain(t,M): return (t,)+tuple(M[2:])
def minAdmRec(M):
    L=len(M)-1
    if L==0: return 0
    if L==1: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec(redChain(t,M)) for t in range(min(M[0],M[1])+1))
def achiever_path(M):
    L=len(M)-1
    if L<=1: return ()
    best=None;bt=None
    for t in range(min(M[0],M[1])+1):
        v=(M[0]-t)*(M[1]-t)+minAdmRec(redChain(t,M))
        if best is None or v<best:best=v;bt=t
    return (bt,)+achiever_path(redChain(bt,M))
for M in [(2,2,2),(2,3,2),(3,3,3),(2,3,3),(3,2,3),(2,4,2)]:
    M=tuple(M)
    ap=achiever_path(M); tach=[M[0]]+list(ap)+[0]
    def Text(k): return M[0] if k==0 else (tach[k-1] if k-1<len(tach) else 0)
    t1=Text(2)  # = leaf rank = Text_L
    # boundary s=1: K-core t1 x t1; r1 = Text1 - t1 = M0 - t1; c1 = Wext1 - t1 = M1 - t1; 
    # E-block r1 x c1; leaf Rfin2 : Text2 x Wext2 = t1 x M2.
    r1=M[0]-t1; c1=M[1]-t1
    Efree=r1*c1; leaf_slots=t1*M[2]
    budget=Efree+leaf_slots  # = minAdm (incl 1 anchor)
    print(f"M={M}: minAdm={minAdmRec(M)} t1(leaf rank)={t1} r1={r1} c1={c1} | E-free={Efree} leaf-slots={leaf_slots} budget={budget} | flatDim={M[0]*M[1]+M[1]*M[2]}")
