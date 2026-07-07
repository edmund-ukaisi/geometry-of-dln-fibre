import sympy as sp, random

def b22(A,Y,Z,T): return A.row_join(Y).col_join(Z.row_join(T))
def prod(Cs):
    P=Cs[0]
    for s in range(1,len(Cs)): P=P*Cs[s]
    return P

def gen(L,r,m,seed,scale=sp.Rational(1,6)):
    random.seed(seed)
    def M(a,b): return sp.Matrix(a,b,lambda i,j: scale*sp.Rational(random.randint(-4,4),5))
    return ({s:M(r,r) for s in range(L)},{s:M(r,m) for s in range(L)},
            {s:M(m,r) for s in range(L)},{s:M(m,m) for s in range(L)})

def check(L,r,m,seed):
    Ir=sp.eye(r); n=r+m
    X,Y,Z,T=gen(L,r,m,seed)
    A={s:Ir+X[s] for s in range(L)}
    C={s:b22(A[s],Y[s],Z[s],T[s]) for s in range(L)}
    Q={0:sp.eye(n)}
    for s in range(1,L+1): Q[s]=Q[s-1]*C[s-1]
    B={s:Q[s][:r,:r] for s in range(L+1)}
    R={s:Q[s][:r,r:] for s in range(L+1)}
    D={s:Q[s][r:,:r] for s in range(L+1)}
    Hh={s:Q[s][r:,r:] for s in range(L+1)}
    u={s:B[s].inv()*R[s] for s in range(L)}
    V={s:Z[s]*A[s].inv() for s in range(L)}
    W={s:Hh[s]-D[s]*B[s].inv()*R[s] for s in range(L)}   # = blockSchur(Q_s)
    S={s:T[s]-Z[s]*A[s].inv()*Y[s] for s in range(L)}
    N={s:Ir+u[s]*V[s] for s in range(L)}
    K={0:sp.zeros(m,m)}
    for s in range(1,L): K[s]=Z[s]*(Q[s+1][:r,:r]).inv()*(Q[s][:r,r:])
    Msh={s:(Ir if False else sp.eye(m))-K[s] for s in range(L)}  # 1-K_s
    Stil={s:Msh[s]*S[s] for s in range(L)}
    z=lambda a,b: sp.zeros(a,b)
    ok=True
    # L1: B_{s+1} = B_s N_s A_s
    for s in range(L):
        ok &= sp.simplify(B[s+1]-B[s]*N[s]*A[s])==z(r,r)
    # RECUR-D: D_{s+1} = D_s N_s A_s + W_s Z_s
    for s in range(L):
        ok &= sp.simplify(D[s+1]-(D[s]*N[s]*A[s]+W[s]*Z[s]))==z(m,r)
    # leftAccum: a_{s+1}=a_s + W_s V_s N_s^-1 B_s^-1 ; claim D_s = a_s B_s
    a=z(m,r); okLA=True
    for s in range(L+1):
        okLA &= sp.simplify(D[s]-a*B[s])==z(m,r)
        if s<L: a=a+W[s]*V[s]*N[s].inv()*B[s].inv()
    ok &= okLA
    return ok, okLA

def check_moved(L,r,m,seed):
    """Verify Kcoup(moved)=Kcoup, blockSchur(partProd moved s)=wHatAccum, and D_hat_L=D_L."""
    Ir=sp.eye(r); Im=sp.eye(m); n=r+m
    X,Y,Z,T=gen(L,r,m,seed)
    A={s:Ir+X[s] for s in range(L)}
    C={s:b22(A[s],Y[s],Z[s],T[s]) for s in range(L)}
    Q={0:sp.eye(n)}
    for s in range(1,L+1): Q[s]=Q[s-1]*C[s-1]
    B={s:Q[s][:r,:r] for s in range(L+1)}
    R={s:Q[s][:r,r:] for s in range(L+1)}
    D={s:Q[s][r:,:r] for s in range(L+1)}
    Hh={s:Q[s][r:,r:] for s in range(L+1)}
    u={s:B[s].inv()*R[s] for s in range(L)}
    V={s:Z[s]*A[s].inv() for s in range(L)}
    W={s:Hh[s]-D[s]*B[s].inv()*R[s] for s in range(L)}
    S={s:T[s]-Z[s]*A[s].inv()*Y[s] for s in range(L)}
    N={s:Ir+u[s]*V[s] for s in range(L)}
    K={0:sp.zeros(m,m)}
    for s in range(1,L): K[s]=Z[s]*(Q[s+1][:r,:r]).inv()*(Q[s][:r,r:])
    Msh={s:sp.eye(m)-K[s] for s in range(L)}
    Stil={s:Msh[s]*S[s] for s in range(L)}
    # wHatAccum: wH[0]=I; wH[s+1]=wH[s]*(1-K_s)*Stil_s
    wH={0:sp.eye(m)}
    for s in range(L): wH[s+1]=wH[s]*Msh[s]*Stil[s]
    # deltaV0 = sum_{s<L}(W_s - wH_s) V_s N_s^-1 B_s^-1
    dV0=sp.zeros(m,r)
    for s in range(L): dV0=dV0+(W[s]-wH[s])*V[s]*N[s].inv()*B[s].inv()
    Z0edit=Z[0]+dV0*A[0]
    # build moved chain
    Yt={s:Y[s]+N[s].inv()*u[s]*(S[s]-Stil[s]) for s in range(L)}
    Zt={s:(Z0edit if s==0 else Z[s]) for s in range(L)}
    Tt={s:Stil[s]+Zt[s]*A[s].inv()*Yt[s] for s in range(L)}
    Ct={s:b22(A[s],Yt[s],Zt[s],Tt[s]) for s in range(L)}
    Qh={0:sp.eye(n)}
    for s in range(1,L+1): Qh[s]=Qh[s-1]*Ct[s-1]
    Bh={s:Qh[s][:r,:r] for s in range(L+1)}
    Rh={s:Qh[s][:r,r:] for s in range(L+1)}
    Dh={s:Qh[s][r:,:r] for s in range(L+1)}
    Hh_h={s:Qh[s][r:,r:] for s in range(L+1)}
    Wh={s:Hh_h[s]-Dh[s]*Bh[s].inv()*Rh[s] for s in range(L+1)}  # blockSchur(partProd moved s)
    z=lambda a,b: sp.zeros(a,b)
    ok=True
    # Kcoup(moved) = Kcoup(C)
    Kh={0:sp.zeros(m,m)}
    for s in range(1,L): Kh[s]=Zt[s]*(Qh[s+1][:r,:r]).inv()*(Qh[s][:r,r:])
    for s in range(1,L): ok &= sp.simplify(Kh[s]-K[s])==z(m,m)
    # blockSchur(partProd moved s) = wHatAccum s
    for s in range(L+1): ok &= sp.simplify(Wh[s]-wH[s])==z(m,m)
    # top row preserved
    for s in range(L+1):
        ok &= sp.simplify(Bh[s]-B[s])==z(r,r)
        ok &= sp.simplify(Rh[s]-R[s])==z(r,m)
    # FINAL: D_hat_L = D_L
    okD = sp.simplify(Dh[L]-D[L])==z(m,r)
    ok &= okD
    return ok, okD

if __name__=="__main__":
    for (L,r,m) in [(3,1,1),(3,1,2),(4,1,1),(4,1,2),(3,2,2),(5,1,2)]:
        for seed in (5,11):
            ok,okLA=check(L,r,m,seed)
            okm,okD=check_moved(L,r,m,seed)
            print(f"L={L} r={r} m={m} seed={seed}: L1&RECUR-D&leftAccum={ok} | moved(Kcoup,Wh,toprow)&Dhat=L={okm} (Dhat==D:{okD})")
