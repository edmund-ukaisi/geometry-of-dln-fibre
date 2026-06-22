import sympy as sp
# g157 claim: R (full-product Schur) = S1·(inter-layer unit)·S2, NOT S1·S2 (per-layer Schur product),
# off {E=0}. They coincide only on {E=0}. Verify exactly (2-layer scalar, r=1).
A,Y,Z,T = sp.symbols('A Y Z T'); B,U,V,S = sp.symbols('B U V S')
C1 = sp.Matrix([[A, Y],[Z, T]]); C2 = sp.Matrix([[B, U],[V, S]])
P = sp.expand(C1*C2)
P00,P01,P10,P11 = P[0,0],P[0,1],P[1,0],P[1,1]
E00 = P00 - 1  # regular residuals (full product)
# FULL-product Schur R = P11 - P10 (P00)^{-1} P01  (NB: against P00, NOT 1+E00 — but P00=1+E00)
R = sp.simplify(P11 - P10*P00**(-1)*P01)
print("R (full-product Schur) = P11 - P10 P00^{-1} P01 =")
sp.pprint(sp.simplify(R))
print()
# per-layer Schur complements: S_s = T_s - Z_s (I+X_s)^{-1} Y_s
# layer1: X=A-1 so I+X=A; S1 = T - Z*A^{-1}*Y
# layer2: X=B-1 so I+X=B; S2 = S - V*B^{-1}*U
S1 = T - Z*A**(-1)*Y
S2 = S - V*B**(-1)*U
prod_S = sp.simplify(S1*S2)
print("∏S_s = S1*S2 =", prod_S)
print()
print("R - ∏S_s =", sp.simplify(R - prod_S), "  (nonzero off {E=0} ⟹ g157 RIGHT: R ≠ ∏S_s in general)")
print()
# On {E=0}: P00=1 (A B + Y V = 1 ... ), the regular residuals vanish. Check R = ∏S_s there.
# {E=0}: P00=1, P01=0, P10=0. Then R = P11 (leak=0). And we showed P11|{E=0} = S1 S2? 
# Use the g151 solve: B=(1-YV)/A, U=-YS/A, Z=-TV/B on E=0.
B_sol=(1-Y*V)/A; U_sol=-Y*S/A; Z_sol=-T*V/B_sol
R_E0 = sp.simplify(R.subs({B:B_sol,U:U_sol,Z:Z_sol}))
prodS_E0 = sp.simplify(prod_S.subs({B:B_sol,U:U_sol,Z:Z_sol}))
print("On {E=0}: R =", R_E0, " ; ∏S_s =", prodS_E0, " ; R-∏S_s =", sp.simplify(R_E0-prodS_E0))
