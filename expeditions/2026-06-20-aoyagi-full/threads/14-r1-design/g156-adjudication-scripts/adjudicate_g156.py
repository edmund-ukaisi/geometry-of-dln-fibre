import sympy as sp

print("="*78)
print("ADJUDICATION: R1 single-step Schur core (real child) vs L2 full-product Pi S_s")
print("="*78)

# ---------------------------------------------------------------------------
# PART A. Reproduce the g156 counterexample EXACTLY (L=2, r=1, reduced-dim=2)
# and confirm: full-product Schur R != Pi S_s, but the L2 squeeze needs R ~ Pi S_s.
# ---------------------------------------------------------------------------
print("\n--- PART A: the g156 counterexample (full-product R vs Pi S_s) ---")
eps = sp.Rational(1,7)
# layer blocks C_s = [[A_s, Y_s],[Z_s, T_s]], A_s = I + X_s, here A=1 (r=1), reduced-dim 2
# K_1 = eps e_2 (2x1), Y_2 = eps e_1^T (1x2), S_1 = eps E_11 (2x2), S_2 = eps E_12 (2x2)
e1 = sp.Matrix([[1],[0]]); e2 = sp.Matrix([[0],[1]])
K1 = eps*e2                       # Z_1 A_1^{-1}, shape 2x1
Y2 = eps*e1.T                     # 1x2
S1 = eps*sp.Matrix([[1,0],[0,0]]) # E_11
S2 = eps*sp.Matrix([[0,1],[0,0]]) # E_12
# Reconstruct C_1, C_2 with A=1. C_s = [[I, 0],[K_s, I]] [[A_s, Y_s],[0, S_s]]
# r=1 so A_s=1 (1x1), reduced dim 2.
# choose Y_1 = -Y_2 S_1, K_2 = -S_2 K_1 (the cancellation choice)
Y1 = -Y2*S1     # 1x2
K2 = -S2*K1     # 2x1
A1 = sp.Matrix([[1]]); A2 = sp.Matrix([[1]])
# C_1 = [[I,0],[K1,I]]·[[A1,Y1],[0,S1]]
C1 = sp.Matrix(sp.BlockMatrix([[A1, Y1],[K1*A1, K1*Y1+S1]]))
C2 = sp.Matrix(sp.BlockMatrix([[A2, Y2],[K2*A2, K2*Y2+S2]]))
P = C2*C1     # full product C_2 C_1 (3x3:  1+2 = 3)
# Block P into [[P00 (1x1), P01 (1x2)],[P10 (2x1), P11 (2x2)]]
P00 = P[0:1,0:1]; P01 = P[0:1,1:3]; P10 = P[1:3,0:1]; P11 = P[1:3,1:3]
E = (P00 - sp.eye(1), P01, P10)
print("P00 - I =", sp.simplify(P00 - sp.eye(1)).T.tolist(), " P01 =", sp.simplify(P01).tolist(), " P10 =", sp.simplify(P10).T.tolist())
R = sp.simplify(P11 - P10*(P00.inv())*P01)   # full-product Schur core
prodS = sp.simplify(S2*S1)
print("E = 0 ?", all(sp.simplify(x)==sp.zeros(*x.shape) for x in E))
print("R (full-product Schur)      =", R.tolist())
print("Pi S_s = S2*S1              =", prodS.tolist())
print("R == Pi S_s ?", sp.simplify(R-prodS)==sp.zeros(2,2))
print("  => L2 comparability ||R||^2 <~ ||Pi S||^2 FAILS (RHS=0, LHS!=0):",
      sp.simplify(prodS)==sp.zeros(2,2) and sp.simplify(R)!=sp.zeros(2,2))
