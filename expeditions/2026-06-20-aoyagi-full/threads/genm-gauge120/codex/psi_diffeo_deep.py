import sympy as sp

def dpsi_at_zero(L, r, M):
    """Build the absorbing diffeo Psi on the Schur-core coords for an L-layer chain,
       r x r regular block, M x M core block; return whether dPsi(0)=I on core & 0 on reg."""
    # symbols per layer
    X={}; Y={}; Z={}; S={}
    for s in range(L):
        X[s]=sp.Matrix(r,r,lambda i,j: sp.symbols(f'X{s}_{i}{j}'))
        Y[s]=sp.Matrix(r,M,lambda i,j: sp.symbols(f'Y{s}_{i}{j}'))
        Z[s]=sp.Matrix(M,r,lambda i,j: sp.symbols(f'Z{s}_{i}{j}'))
        S[s]=sp.Matrix(M,M,lambda i,j: sp.symbols(f'S{s}_{i}{j}'))   # Schur-core CHART coord
    Ir=sp.eye(r)
    # raw core T_s from Schur core S_s:  T_s = S_s + Z_s (I+X_s)^{-1} Y_s
    T={s: S[s] + Z[s]*(Ir+X[s]).inv()*Y[s] for s in range(L)}
    def layer(s):
        C=sp.zeros(r+M,r+M)
        C[:r,:r]=Ir+X[s]; C[:r,r:]=Y[s]; C[r:,:r]=Z[s]; C[r:,r:]=T[s]
        return C
    Cs=[layer(s) for s in range(L)]
    # partial products & couplings K_k = (C_k)_21 (P_k)_11^{-1} (P_{k-1})_12
    P=Cs[0]; Psi=[S[0]]
    for k in range(1,L):
        Pk=P*Cs[k]
        P11=Pk[:r,:r]; A12=P[:r,r:]; B21=Cs[k][r:,:r]
        Kk=B21*P11.inv()*A12                    # M x M
        Psi.append((sp.eye(M)-Kk)*S[k])
        P=Pk
    # flatten Psi outputs and core inputs; also reg inputs
    core_vars=[]; 
    for s in range(L):
        for i in range(M):
            for j in range(M): core_vars.append(S[s][i,j])
    reg_vars=[]
    for s in range(L):
        for blk in (X[s],Y[s],Z[s]):
            for i in range(blk.rows):
                for j in range(blk.cols): reg_vars.append(blk[i,j])
    psi_out=[]
    for s in range(L):
        for i in range(M):
            for j in range(M): psi_out.append(Psi[s][i,j])
    origin={v:0 for v in core_vars+reg_vars}
    # core Jacobian
    n=len(core_vars)
    coreJ=sp.zeros(n,n)
    for a,f in enumerate(psi_out):
        for b,v in enumerate(core_vars):
            coreJ[a,b]=sp.diff(f,v).subs(origin)
    core_ok = (coreJ == sp.eye(n))
    # reg derivative (should be all zero)
    reg_ok=True
    for f in psi_out:
        for v in reg_vars:
            if sp.diff(f,v).subs(origin)!=0: reg_ok=False
    return core_ok, reg_ok, n

for (L,r,M,label) in [(3,1,2,"L=3, r=1, 2x2 core (NON-SCALAR)"),
                      (4,1,1,"L=4, r=1, scalar core")]:
    core_ok,reg_ok,n=dpsi_at_zero(L,r,M)
    print(f"{label}: dPsi(0)=I on {n} core coords: {core_ok} ; zero on all reg dirs: {reg_ok}")
