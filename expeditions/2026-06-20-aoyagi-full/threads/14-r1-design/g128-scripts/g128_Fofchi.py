import sympy as sp
# CONFIRM the EXACT form of F∘χ for the L2 deepest unit-Jac χ. (2,2,2) r=1.
# deepest A1=A2=[[1,0],[0,0]], B=[[1,0],[0,0]]. F = ‖prod-B‖² = g00²+g01²+g10²+g11².
# χ (the #125 chart): replace the 3 regular generators' unit-pivot vars by the generators themselves.
# So in χ-coords, the 3 regular generators BECOME coordinates E1=g00, E2=g01, E3=g10, and the 4th
# generator g11 is the core. So F = E1²+E2²+E3²+g11². The QUESTION: when we express g11 in the NEW
# coords (after the substitution), is it literally a clean core G², or G²·unit, and is there an overall
# unit factor on the whole F?
w = sp.symbols('w0:8', real=True)
W1=sp.Matrix([[w[0],w[1]],[w[2],w[3]]]); W2=sp.Matrix([[w[4],w[5]],[w[6],w[7]]])
v1=sp.Matrix([[1,0],[0,0]]); v2=sp.Matrix([[1,0],[0,0]]); B=v1*v2
P=sp.expand((v1+W1)*(v2+W2))
g=[sp.expand((P-B)[i,j]) for i in range(2) for j in range(2)]  # g00,g01,g10,g11
print("generators: g00=%s | g01=%s | g10=%s | g11=%s" % tuple(str(x) for x in g))
print()
# F = sum of squares of the 4 generators — this is ALREADY literally g00²+g01²+g10²+g11², NO unit factor!
# F = g00²+g01²+g10²+g11². The χ-coords just RENAME g00,g01,g10 -> E1,E2,E3 (they're coordinates).
# So in χ-coords F = E1²+E2²+E3² + g11(in χ-coords)². The only question: what is g11 in χ-coords?
# g11 = w2 w5 + w3 w7 (no linear part). After χ (w4=E1-..., w5=E2-..., w2=E3-...), express g11:
# Actually χ uses w2,w4,w5 as the pivots (g10 has pivot w2, g00 has w4, g01 has w5). So the core coords
# are w0,w1,w3,w6,w7 (the 5 non-pivot vars). g11 = w2 w5 + w3 w7 — but w2,w5 are PIVOT vars (=functions
# of E's and core). Substitute the inverse to write g11 in (E1,E2,E3, w0,w1,w3,w6,w7):
E1,E2,E3 = sp.symbols('E1 E2 E3', real=True)
# χ: E1=g00, E2=g01, E3=g10. Invert for w4 (from g00), w5 (from g01), w2 (from g10):
# g00 = w4(1+w0)+w0+w1 w6 = E1 => w4 = (E1 - w0 - w1 w6)/(1+w0)
# g01 = w5(1+w0)+w1 w7 = E2 => w5 = (E2 - w1 w7)/(1+w0)
# g10 = w2(1+w4)+... wait g10 = w2 w4 + w2 + w3 w6 = w2(1+w4)+w3 w6 = E3 => w2 = (E3 - w3 w6)/(1+w4)
sol = sp.solve([g[0]-E1, g[1]-E2, g[2]-E3], [w[4],w[5],w[2]], dict=True)[0]
g11_chi = sp.simplify(g[3].subs(sol))
print("g11 in χ-coords (E1,E2,E3,w0,w1,w3,w6,w7):")
print("  g11∘χ⁻¹ =", g11_chi)
print()
# F∘χ⁻¹ = E1²+E2²+E3²+g11_chi². Is g11_chi = G·unit (G the clean core, unit bounded), or clean?
# Look at g11_chi's structure: does it factor as (clean core)·(unit) or have E-dependence?
print("F in χ-coords = E1²+E2²+E3²+(g11∘χ⁻¹)²")
print("Is g11∘χ⁻¹ free of E1,E2,E3 (a pure core in w0,w1,w3,w6,w7)? Check E-dependence:")
for Evar in [E1,E2,E3]:
    print(f"  ∂(g11∘χ⁻¹)/∂{Evar} = {sp.simplify(sp.diff(g11_chi, Evar))}")
