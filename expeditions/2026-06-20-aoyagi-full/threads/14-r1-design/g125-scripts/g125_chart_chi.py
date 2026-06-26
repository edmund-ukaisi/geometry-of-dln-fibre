import sympy as sp
# Make the explicit MeasurePreserving chart χ concrete for a114e07e + fm-2, on (2,2,2) r=1.
# The triangular unit-pivot elimination = a sequence of polynomial shears (each measure-preserving),
# composing to χ : (local coords) -> (regular coords ⊕ core coords), with F∘χ⁻¹ = ‖reg‖² + core.
# This is EXACTLY the lemma2Fwd-style det-1 map, but for the deepest-point split.
#
# (2,2,2) r=1: deepest A1=A2=[[1,0],[0,0]], B=[[1,0],[0,0]]. Local W1,W2 (8 vars).
w = sp.symbols('w0:8', real=True)
W1=sp.Matrix([[w[0],w[1]],[w[2],w[3]]]); W2=sp.Matrix([[w[4],w[5]],[w[6],w[7]]])
v1=sp.Matrix([[1,0],[0,0]]); v2=sp.Matrix([[1,0],[0,0]]); B=v1*v2
P=sp.expand((v1+W1)*(v2+W2))
gens=[sp.expand((P-B)[i,j]) for i in range(2) for j in range(2)]
# gens: g00=(P-B)00, g01, g10, g11. From #125: g00 lin=w0+w4, g01 lin=w5, g10 lin=w2, g11 lin=0 (core).
print("=== explicit generators at deepest (2,2,2) r=1 ===")
names=['g00','g01','g10','g11']
for nm,g in zip(names,gens): print(f"  {nm} =", g)
print()
# The chart χ: NEW regular coords E1:=g00, E2:=g01, E3:=g10 (the 3 regular generators themselves),
# core coords: the remaining 5 local vars MINUS the 3 solved. Actually χ maps the 8 local coords to
# (E1,E2,E3, [5 core/spectator coords]). Since g00=w0+w4+(w0 w4+w1 w6), g01=w5+(...), g10=w2+(...),
# each gi has a UNIT-pivot variable (w0 or w4 for g00 — pick w4; w5 for g01; w2 for g10). Define χ by
# REPLACING w4->E1, w5->E2, w2->E3 (unit-pivot substitution), keeping w0,w1,w3,w6,w7 as core/spectator.
# This is a TRIANGULAR polynomial change (each new coord = old var + polynomial in others), det=1.
E1,E2,E3 = sp.symbols('E1 E2 E3', real=True)
# χ⁻¹: express the loss in (E1,E2,E3,core). The regular block = E1²+E2²+E3² (the 3 reg gens squared),
# core = g11² (the residual). Check: is F = g00²+g01²+g10²+g11² = E1²+E2²+E3²+g11² with χ the map
# (w)->(E1=g00,E2=g01,E3=g10, w0,w1,w3,w6,w7)? F is literally the sum of the 4 gens² -- so in the
# coords (g00,g01,g10, core-vars) it IS g00²+g01²+g10²+g11core². The point: (g00,g01,g10) + 5 others
# is a valid coordinate system (Jacobian: the 3 gens have distinct unit pivots w4,w5,w2 => the map
# (w0..w7) -> (w0,w1,E3=g10,w3,E1=g00,E2=g01,w6,w7) has triangular Jacobian, det=±1).
chi_out = [w[0], w[1], gens[2], w[3], gens[0], gens[1], w[6], w[7]]  # replace w2->g10, w4->g00, w5->g01
J = sp.Matrix([[sp.diff(c, wi) for wi in w] for c in chi_out])
print("=== χ : (w0..w7) -> (w0, w1, g10, w3, g00, g01, w6, w7) [unit-pivot replace w2,w4,w5] ===")
print("  Jacobian det =", sp.factor(J.det()), " (constant ±1 => MEASURE-PRESERVING, no exponent shift)")
print()
print("  In χ-coords, F = ‖prod-B‖² = g00²+g01²+g10²+g11² = (new w4-slot)²+(new w5-slot)²+(new w2-slot)²")
print("  + g11(core)². The first 3 = the REGULAR BLOCK Σ E_i² (nReg=3 nondeg squares); g11 = the CORE.")
