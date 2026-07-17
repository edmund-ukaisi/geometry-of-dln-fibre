import numpy as np
np.random.seed(1)

print("="*78)
print("A. GRAM IDENTITY check  det(Q~p Q~pᵀ)·det((Q_bΠ)(Q_bΠ)ᵀ) = det(Q Qᵀ)")
print("   (Q full-rank generic; confirms the ALGEBRAIC identity l2engine derived)")
print("="*78)
def gram_id_check(t,b,q):
    # Q is (t+b) x q full tail, split rows into pivot (t) and corank (b)
    Q=np.random.randn(t+b,q)
    Qp=Q[:t,:]; Qb=Q[t:,:]
    # Q~p = Q_p + P^{-1} B12 Q_b  (pivotTail); pick random P invertible, B12
    P=np.random.randn(t,t); B12=np.random.randn(t,b)
    Qtp=Qp+np.linalg.inv(P)@B12@Qb
    # Pi = I - Q~pᵀ(Q~p Q~pᵀ)^{-1} Q~p  (proj off row space of Q~p)
    Pi=np.eye(q)-Qtp.T@np.linalg.inv(Qtp@Qtp.T)@Qtp
    S=Qb@Pi
    lhs=np.linalg.det(Qtp@Qtp.T)*np.linalg.det(S@S.T)
    rhs=np.linalg.det(Q@Q.T)
    return lhs,rhs
oks=[]
for _ in range(200):
    l,r=gram_id_check(1,2,4); oks.append(np.isclose(l,r,rtol=1e-6))
print(f"  identity holds (t=1,b=2,q=4, 200 samples): {all(oks)}   -> the ALGEBRAIC identity is TRUE")
print()

print("="*78)
print("B. STRUCTURAL BOTTLENECK  M=(3,3,2,q): tail product Q=3xq THROUGH width 2")
print("   Q generically rank 2 < t+b=3  =>  det(Q Qᵀ) ≡ 0  =>  ∫ det(QQᵀ)^{-a/2} = +∞")
print("="*78)
for q in [4,5,6]:
    dets=[]
    for _ in range(50):
        A1=np.random.randn(3,2)   # M1=3 -> M2=2
        A2=np.random.randn(2,q)   # M2=2 -> M3=q
        Q=A1@A2                   # 3 x q, rank <= 2
        dets.append(abs(np.linalg.det(Q@Q.T)))
    print(f"  q={q}: max|det(QQᵀ)| over 50 random A' = {max(dets):.3e}   (≡0 up to fp; rank={np.linalg.matrix_rank(Q)})")
print("  => collapsed obligation-2 integrand ≡ +∞ on a POSITIVE-MEASURE (all) of A'-box. FALSE.")
print()

print("="*78)
print("C. NON-SUBMERSIVE THRESHOLD LOWERING  (no bottleneck; Q = L·R, L square)")
print("   free Q (n x q): ∫det(QQᵀ)^{-a/2} finite iff a < q-n+1.  Pick n=2,q=4,a=2: free CONVERGES (a=2<3).")
print("   product Q=L·R, L 2x2 square, R 2x4:  det(QQᵀ)=det(L)²·det(RRᵀ) => extra |det L|^{-a} divisor.")
print("="*78)
n,q,a=2,4,2
# MC estimate of ∫ over unit box with cutoff {integrand < K}; track growth of E[integrand·1{>cut skipped}]
# cleaner: estimate ∫_{|det L|>δ} |det L|^{-a} dL over box[-1,1]^4 and show it GROWS as δ->0 (diverges),
# vs free: ∫ det(QQᵀ)^{-a/2} over free Q in box, with det-cutoff, stays BOUNDED.
def mc_free(N,delta):
    tot=0.0; cnt=0
    for _ in range(N):
        Q=np.random.uniform(-1,1,(n,q))
        d=np.linalg.det(Q@Q.T)
        if d>delta: tot+=d**(-a/2); cnt+=1
    return tot/N*(2**(n*q))   # box volume
def mc_prod(N,delta):
    tot=0.0
    for _ in range(N):
        L=np.random.uniform(-1,1,(n,n)); R=np.random.uniform(-1,1,(n,q))
        Q=L@R
        d=np.linalg.det(Q@Q.T)
        if d>delta: tot+=d**(-a/2)
    return tot/N*(2**(n*n+n*q))
N=200000
print(f"{'delta':>10} {'FREE ∫(cut)':>16} {'PRODUCT ∫(cut)':>18}")
for delta in [1e-2,1e-4,1e-6,1e-8]:
    print(f"{delta:>10.0e} {mc_free(N,delta):>16.2f} {mc_prod(N,delta):>18.2f}")
print("  => FREE estimate converges (bounded as δ→0); PRODUCT estimate GROWS without bound. WALL.")
