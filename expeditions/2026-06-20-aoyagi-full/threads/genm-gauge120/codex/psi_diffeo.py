import sympy as sp
# (2,2,2,2), r=1, M=1 (scalar) L=3: verify dPsi(0)=I explicitly with symbolic derivatives.
# Chart core coords: S0,S1,S2 (the Schur cores). reg coords: X0..X2,Y0..Y2,Z0..Z2.
# K_i depends on raw blocks. To express K_i as function of chart coords we need the map
# (X,Y,Z,S) -> raw T via T_i = S_i + Z_i Y_i/(1+X_i).  Then K_i(reg, S) and Psi_i=(1-K_i)S_i.
Xs=sp.symbols('X0 X1 X2'); Ys=sp.symbols('Y0 Y1 Y2'); Zs=sp.symbols('Z0 Z1 Z2')
Ss=sp.symbols('S0 S1 S2')
# raw T_i from Schur core S_i: S_i = T_i - Z_i Y_i/(1+X_i) => T_i = S_i + Z_i Y_i/(1+X_i)
Ts=[Ss[i] + Zs[i]*Ys[i]/(1+Xs[i]) for i in range(3)]
def layer(i): return sp.Matrix([[1+Xs[i], Ys[i]],[Zs[i], Ts[i]]])
Cs=[layer(i) for i in range(3)]
# partial products
P0=Cs[0]; P1=Cs[0]*Cs[1]; P2=Cs[0]*Cs[1]*Cs[2]
# K_k = (C_k)_21 * (P_k)_11^{-1} * (P_{k-1})_12
K1=Zs[1]*(P1[0,0])**(-1)*P0[0,1]
K2=Zs[2]*(P2[0,0])**(-1)*P1[0,1]
# Psi core map: S0->S0, S1->(1-K1)S1, S2->(1-K2)S2
Psi=[Ss[0], (1-K1)*Ss[1], (1-K2)*Ss[2]]
origin={Xs[0]:0,Xs[1]:0,Xs[2]:0,Ys[0]:0,Ys[1]:0,Ys[2]:0,Zs[0]:0,Zs[1]:0,Zs[2]:0,Ss[0]:0,Ss[1]:0,Ss[2]:0}
print("K1(0) =", sp.simplify(K1.subs(origin)), "  K2(0) =", sp.simplify(K2.subs(origin)))
# Jacobian of Psi w.r.t. ALL chart coords (reg + core), at origin
allvars=list(Xs)+list(Ys)+list(Zs)+list(Ss)
J=sp.Matrix([[sp.diff(Psi[i],v) for v in allvars] for i in range(3)])
J0=sp.simplify(J.subs(origin))
print("\ndPsi(0) rows (wrt X0..X2,Y0..Y2,Z0..Z2,S0,S1,S2):")
sp.pprint(J0)
# The core-block sub-Jacobian (dPsi_i/dS_j)
coreJ=sp.Matrix([[sp.diff(Psi[i],Ss[j]) for j in range(3)] for i in range(3)]).subs(origin)
print("\ncore-block dPsi_i/dS_j at 0 =")
sp.pprint(sp.simplify(coreJ))
print("\n=> dPsi(0) = identity on core, zero on reg-directions:",
      sp.simplify(coreJ-sp.eye(3))==sp.zeros(3,3) and all(sp.simplify(J0[i,k])==0 for i in range(3) for k in range(9)))
