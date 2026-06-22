import sympy as sp
eps = sp.symbols('epsilon', positive=True)
print("="*70)
print("THE g153/g156 COUNTEREXAMPLE (trusted, ground truth) — L=3, r=1, H=(2,2,2,2)")
print("C1=[[1,0],[-eps^2,eps]], C2=[[1,eps],[eps,0]], C3=[[1,-eps^2],[0,eps]]")
print("="*70)
C1 = sp.Matrix([[1,0],[-eps**2,eps]])
C2 = sp.Matrix([[1,eps],[eps,0]])
C3 = sp.Matrix([[1,-eps**2],[0,eps]])
P = sp.expand(C1*C2*C3)
print("\nC1C2C3 =")
sp.pprint(P)
B0 = sp.Matrix([[1,0],[0,0]])  # blockdiag[I_r,0], r=1
loss = sp.expand(sum((P-B0)[i,j]**2 for i in range(2) for j in range(2)))
print("\nloss = ‖C1C2C3 - blockdiag[1,0]‖² =", sp.simplify(loss))

# per-layer blocks: X_s = (0,0)-1, Y_s=(0,1), Z_s=(1,0), T_s=(1,1)
def blocks(C): return (C[0,0]-1, C[0,1], C[1,0], C[1,1])  # X,Y,Z,T
X1,Y1,Z1,T1 = blocks(C1); X2,Y2,Z2,T2 = blocks(C2); X3,Y3,Z3,T3 = blocks(C3)
print("\nraw T_s (the (1,1) entries):", T1, T2, T3, " -> product =", sp.simplify(T1*T2*T3))

# (A) per-layer UNIT: T̃_s = T_s (I - V_s Y_s)^{-1} — but what is V_s? In my g151 V was the (1,0) of the NEXT
# layer. Ambiguous. Take the literal raw product first (units=... ): T1 T2 T3:
print("\n(A) per-layer raw/unit product ∏T_s = ε·0·ε·(unit) =", sp.simplify(T1*T2*T3), " (=0 since T2=0)")

# (B) per-layer SCHUR: S_s = T_s - Z_s (I+X_s)^{-1} Y_s = T_s - Z_s/(1+X_s) * Y_s
S1 = T1 - Z1*Y1/(1+X1)
S2 = T2 - Z2*Y2/(1+X2)
S3 = T3 - Z3*Y3/(1+X3)
print("\n(B) per-layer SCHUR S_s = T_s - Z_s Y_s/(1+X_s):")
print("    S1 =", sp.simplify(S1), "  S2 =", sp.simplify(S2), "  S3 =", sp.simplify(S3))
print("    ∏S_s =", sp.simplify(S1*S2*S3))
print("    ‖∏S_s‖² =", sp.simplify((S1*S2*S3)**2), "  vs loss =", sp.simplify(loss),
      " match:", sp.simplify((S1*S2*S3)**2 - loss)==0)

# (C) full product Schur R = P11 - P10 P00^{-1} P01
P00,P01,P10,P11 = P[0,0],P[0,1],P[1,0],P[1,1]
R = sp.simplify(P11 - P10*P00**(-1)*P01)
print("\n(C) full product Schur R = P11 - P10 P00^{-1} P01 =", R, "  ‖R‖²=",sp.simplify(R**2),
      " match loss:", sp.simplify(R**2 - loss)==0)
