import sympy as sp

def layer(X,Y,Z,T):
    # r=1, M=1 blocks -> 2x2 scalar layer [[1+X, Y],[Z, T]]
    return sp.Matrix([[1+X, Y],[Z, T]])

def schur22(P):
    # Schur complement of the (1,1) block (r=1): P22 - P21 * P11^{-1} * P12
    return P[1,1] - P[1,0]*P[0,0]**(-1)*P[0,1]

def per_layer_schur(X,Y,Z,T):
    return T - Z*(1+X)**(-1)*Y

print("=== L=2 (two layers), r=1,M=1 scalars ===")
Xs=sp.symbols('X0 X1 X2 X3'); Ys=sp.symbols('Y0 Y1 Y2 Y3'); Zs=sp.symbols('Z0 Z1 Z2 Z3'); Ts=sp.symbols('T0 T1 T2 T3')

for L in [2,3,4]:
    print(f"\n=== L={L} layers ===")
    Cs=[layer(Xs[s],Ys[s],Zs[s],Ts[s]) for s in range(L)]
    P=Cs[0]
    for s in range(1,L): P=P*Cs[s]
    Sch=sp.simplify(schur22(P))
    Ss=[per_layer_schur(Xs[s],Ys[s],Zs[s],Ts[s]) for s in range(L)]
    prodS=sp.prod(Ss)
    # ratio Sch / prod(S_s): should be an analytic unit -> 1 at origin
    ratio=sp.simplify(Sch/prodS)
    print("Sch / (prod S_s) =", ratio)
    subs0={**{Xs[s]:0 for s in range(L)},**{Ys[s]:0 for s in range(L)},
           **{Zs[s]:0 for s in range(L)},**{Ts[s]:0 for s in range(L)}}
    print("  ratio at origin =", sp.simplify(ratio.subs(subs0)))
