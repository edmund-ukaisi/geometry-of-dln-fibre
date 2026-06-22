import sympy as sp
print("="*70)
print("g151's EXACT L=2 case: C1=[[A,Y],[Z,T]], C2=[[B,U],[V,S]], solve B,U,Z on {E=0}")
print("Compare P11|{E=0} to: (i) T(1-VY)^{-1}S  (ii) per-layer Schur S1*S2")
print("="*70)
A,Y,Z,T = sp.symbols('A Y Z T'); B,U,V,S = sp.symbols('B U V S')
C1 = sp.Matrix([[A, Y],[Z, T]]); C2 = sp.Matrix([[B, U],[V, S]])
P = sp.expand(C1*C2)
E00 = sp.expand(P[0,0]-1); E01 = sp.expand(P[0,1]); E10 = sp.expand(P[1,0]); P11 = sp.expand(P[1,1])
# g151 solved: B=(1-YV)/A, U=-YS/A, Z=-TV/B  (on E=0)
B_sol = (1 - Y*V)/A; U_sol = (-Y*S)/A; Z_sol = (-T*V)/B_sol
P11_E0 = sp.simplify(P11.subs({B:B_sol, U:U_sol, Z:Z_sol}))
print("\nP11|{E=0} =", P11_E0)
print("T(1-VY)^{-1}S =", sp.simplify(T*(1-V*Y)**(-1)*S), "  diff:", sp.simplify(P11_E0 - T*(1-V*Y)**(-1)*S))

# per-layer Schur with THESE blocks: S_s = T_s - Z_s (I+X_s)^{-1} Y_s
# layer1: X=A-1, T_1=T, Z_1=Z, Y_1=Y ⟹ S_1 = T - Z*(A)^{-1}*Y   (I+X = A)
# layer2: X=B-1, T_2=S, Z_2=V, Y_2=U ⟹ S_2 = S - V*(B)^{-1}*U   (I+X = B)
S1 = T - Z*(A)**(-1)*Y
S2 = S - V*(B)**(-1)*U
# evaluate per-layer Schur ON THE SOLVED locus (B,U,Z from E=0):
S1_e = sp.simplify(S1.subs({Z:Z_sol, B:B_sol}))   # S1 uses Z (solved), A (free)
S2_e = sp.simplify(S2.subs({U:U_sol, B:B_sol}))   # S2 uses U,B (solved)
print("\nper-layer Schur on {E=0}: S1 =", S1_e, "  S2 =", S2_e)
prod_schur = sp.simplify(S1_e * S2_e)
print("S1*S2 on {E=0} =", prod_schur)
print("P11|{E=0} - S1*S2 =", sp.simplify(P11_E0 - prod_schur), "  <- 0 ⟹ per-layer Schur IS the L=2 reduced core")
print()
# CRUCIAL: is g151's 'T(1-VY)^{-1}S' actually EQUAL to S1*S2? (i.e. was my unit-naming just notation drift?)
print("T(1-VY)^{-1}S  vs  S1*S2 :", sp.simplify(T*(1-V*Y)**(-1)*S - prod_schur), " <- if 0, my g151 unit form = Schur (notation drift); if not, they differ")
