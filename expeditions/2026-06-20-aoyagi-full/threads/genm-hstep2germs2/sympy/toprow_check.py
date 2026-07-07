import sympy as sp, random
def b22(A,Y,Z,T): return A.row_join(Y).col_join(Z.row_join(T))
def run(L,r,m,seed):
    random.seed(seed)
    def M(a,b): return sp.Matrix(a,b,lambda i,j: sp.Rational(random.randint(-4,4),6))
    X={s:M(r,r) for s in range(L)}; Y={s:M(r,m) for s in range(L)}
    Z={s:M(m,r) for s in range(L)}; T={s:M(m,m) for s in range(L)}
    Ir=sp.eye(r); Im=sp.eye(m); n=r+m
    A={s:Ir+X[s] for s in range(L)}
    C={s:b22(A[s],Y[s],Z[s],T[s]) for s in range(L)}
    Q={0:sp.eye(n)}
    for s in range(1,L+1): Q[s]=Q[s-1]*C[s-1]
    B={s:Q[s][:r,:r] for s in range(L+1)}; R={s:Q[s][:r,r:] for s in range(L+1)}
    u={s:B[s].inv()*R[s] for s in range(L)}
    V={s:Z[s]*A[s].inv() for s in range(L)}
    S={s:T[s]-Z[s]*A[s].inv()*Y[s] for s in range(L)}
    Nn={s:Ir+u[s]*V[s] for s in range(L)}
    K={0:sp.zeros(m,m)}
    for s in range(1,L): K[s]=Z[s]*(Q[s+1][:r,:r]).inv()*(Q[s][:r,r:])
    Stil={s:(Im-K[s])*S[s] for s in range(L)}
    # up edit exactly Y'_s = Y_s + N^-1 u (S - Stil):
    Yt={s:Y[s]+Nn[s].inv()*u[s]*(S[s]-Stil[s]) for s in range(L)}
    # moved chain: Z'_s = Z_s (s>=1), Z'_0 arbitrary (test invariance of TOP row => use random)
    Z0e=M(m,r)
    Zt={s:(Z0e if s==0 else Z[s]) for s in range(L)}
    Tt={s:Stil[s]+Zt[s]*A[s].inv()*Yt[s] for s in range(L)}
    Ct={s:b22(A[s],Yt[s],Zt[s],Tt[s]) for s in range(L)}
    Qh={0:sp.eye(n)}
    for s in range(1,L+1): Qh[s]=Qh[s-1]*Ct[s-1]
    # TOP-ROW lemma: (Qh_s)_11 == (Q_s)_11 and (Qh_s)_12 == (Q_s)_12 for ALL s
    ok=all(sp.simplify(Qh[s][:r,:r]-Q[s][:r,:r])==sp.zeros(r,r) and
           sp.simplify(Qh[s][:r,r:]-Q[s][:r,r:])==sp.zeros(r,m) for s in range(L+1))
    # Invariant B: blockSchur(Ct_s) == Stil_s (per layer)
    okB=all(sp.simplify((Tt[s]-Zt[s]*A[s].inv()*Yt[s])-Stil[s])==sp.zeros(m,m) for s in range(L))
    return ok, okB
for (L,r,m) in [(3,1,1),(4,1,1),(3,1,2),(3,2,2),(5,1,2)]:
    for seed in (5,11):
        ok,okB=run(L,r,m,seed)
        print(f"L={L} r={r} m={m} seed={seed}: TOP-ROW(all s, ARBITRARY Z0)={ok}  perlayerB={okB}")
