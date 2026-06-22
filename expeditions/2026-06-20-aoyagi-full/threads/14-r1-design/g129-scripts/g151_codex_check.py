import sympy as sp
# VERIFY Codex's refutation: on {E=0}, is the reduced block P_11 = T(I-VY)^{-1}S, NOT TS?
# Use r=1, but m,n BIGGER so the (n-r),(m-r) blocks are nontrivial and VY is a genuine product.
# Take H=(2,2,2)... no, need n-r ≥1 and the internal V,Y to multiply. Use the 2-layer general blocks
# symbolically (small dims) and CHECK on the product-regular zero locus (E=0), solving B,U,Z.
r = 1
M0, M1, M2 = 1, 1, 1   # reduced widths M_s = H_s - r; so H = (2,2,2), r=1 ⟹ M=(1,1,1).
# C1 : H0×H1 = 2×2,  C2 : H1×H2 = 2×2. blocks (r=1): A,B scalar(1×1); Y,U: 1×1; Z,V:1×1; T,S:1×1.
A,Y,Z,T = sp.symbols('A Y Z T'); B,U,V,S = sp.symbols('B U V S')
C1 = sp.Matrix([[A, Y],[Z, T]]); C2 = sp.Matrix([[B, U],[V, S]])
P = sp.expand(C1*C2)
E00 = sp.expand(P[0,0]-1); E01 = sp.expand(P[0,1]); E10 = sp.expand(P[1,0]); P11 = sp.expand(P[1,1])
print("E00 =",E00," E01 =",E01," E10 =",E10," P11 =",P11)
# Codex: coords (E00,E01,E10,T,S,A,Y,V); solve B,U,Z. On {E00=E01=E10=0}:
#   B = A^{-1}(1+E00-Y V) = A^{-1}(1 - Y V)   [E00=0]
#   U = A^{-1}(E01 - Y S) = A^{-1}(- Y S)      [E01=0]
#   Z = (E10 - T V) B^{-1} = (- T V) B^{-1}     [E10=0]
Binv_val = (1 - Y*V)/A
B_sol = (1 - Y*V)/A
U_sol = (-Y*S)/A
Z_sol = (-T*V)/B_sol
P11_onE0 = sp.simplify(P11.subs({B:B_sol, U:U_sol, Z:Z_sol}))
print("\nP11 on {E=0} (B,U,Z solved) =", P11_onE0)
TS = T*S
T_internal_S = sp.simplify(T*(1-V*Y)**(-1)*S)  # Codex's claim T(I-VY)^{-1}S
print("T·S =", TS)
print("T(1-VY)^{-1}·S =", sp.simplify(T_internal_S))
print("P11|{E=0} - T·S =", sp.simplify(P11_onE0 - TS), "  (nonzero ⟹ Codex right: raw split FAILS)")
print("P11|{E=0} - T(1-VY)^{-1}S =", sp.simplify(P11_onE0 - T_internal_S), "  (0 ⟹ Codex's T(I-VY)^{-1}S is right)")
print()
# Schur-complement form: R = P11 - E10 (1+E00)^{-1} E01. Is R = T̃·S̃ with gauge-normalized blocks?
R = sp.simplify(P11 - E10*(1+E00)**(-1)*E01)
print("Schur complement R = P11 - E10(1+E00)^{-1}E01 =", sp.expand(R))
# does R = T·S exactly (no internal factor)? (the Schur complement removes the endpoint-regular leak)
print("R - T·S =", sp.simplify(R - T*S), "  (0 ⟹ R = T·S, the Schur complement IS the clean reduced core)")
