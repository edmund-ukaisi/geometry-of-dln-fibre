import sympy as sp
# Check the (1,1) family rate F=z^2 U for a MULTI-LAYER case (1,2,2,1) [L=3, P=A0*A1]
# vs the single-layer (1,2,1) [L=2, P=A0]. Confirm the scalar shear cancellation is uniform.
def family_rate(M):
    L=len(M)-1; r=1; c=M[L]; m1=M[L-1]; s=m1-r; m0=M[0]
    facs=[sp.Matrix(M[k],M[k+1],lambda i,j,k=k: sp.Symbol(f'a{k}_{i}_{j}')) for k in range(L-1)]
    P=facs[0]
    for k in range(1,L-1): P=P*facs[k]
    P1=P[:,:r]; P2=P[:,r:]
    Lam0=(P1.T*P1).inv()*P1.T*P2   # 1 x s
    z=sp.Symbol('z')
    Hb=sp.Matrix(r,c,lambda i,j:(sp.Integer(1) if (i,j)==(0,0) else sp.Symbol(f'h{i}_{j}')))
    Sb=sp.Matrix(s,c,lambda i,j:sp.Symbol(f'sb{i}_{j}'))
    Dt=z*Hb-Lam0*Sb; D=sp.Matrix.vstack(Dt,Sb)
    full=P*D
    F=sum(sp.cancel(full[i,j])**2 for i in range(m0) for j in range(c))
    U=sp.cancel(F/z**2)
    return sp.simplify(sp.diff(U,z))==0, sp.denom(sp.together(U))==1, sp.simplify(U)
for M in [[1,2,1],[1,2,2,1],[1,3,1],[1,2,2,2,1]]:
    try:
        zfree,poly,U = family_rate(M)
        print(f"M={M}: U z-free={zfree}, U polynomial={poly}")
    except Exception as e:
        print(f"M={M}: ERROR {e}")
