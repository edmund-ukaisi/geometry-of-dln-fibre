import sympy as sp
# The naive "rename generators" χ gives g11∘χ⁻¹ with E-dependence — NOT the clean S1.5 form.
# The PROPER split: the core is g11 RESTRICTED to the regular-zero locus {E1=E2=E3=0} (= the Schur
# complement). On {g00=g01=g10=0}, g11 becomes the Schur-complement core G. Compute G and check whether
# F = (regular quadratic in E) + G²·(unit) near 0, the form S1.5 needs.
w = sp.symbols('w0:8', real=True)
W1=sp.Matrix([[w[0],w[1]],[w[2],w[3]]]); W2=sp.Matrix([[w[4],w[5]],[w[6],w[7]]])
v1=sp.Matrix([[1,0],[0,0]]); v2=sp.Matrix([[1,0],[0,0]]); B=v1*v2
P=sp.expand((v1+W1)*(v2+W2))
g=[sp.expand((P-B)[i,j]) for i in range(2) for j in range(2)]
# Solve g00=g01=g10=0 for w4,w5,w2 (the regular-zero locus), substitute into g11 => the Schur core G:
sol=sp.solve([g[0],g[1],g[2]],[w[4],w[5],w[2]],dict=True)[0]
G = sp.simplify(g[3].subs(sol))
print("=== Schur-complement core G = g11 on {g00=g01=g10=0} ===")
print("  G =", G)
print("  (the reduced core in w0,w1,w3,w6,w7 — E-FREE)")
print()
# Now: F = g00²+g01²+g10²+g11². On the regular-zero locus, g11=G. Off it, the question is whether
# F = Q(E) + G² up to a UNIT, where Q(E) is a nondeg quadratic in the 3 regular dirs and G is the core.
# The HONEST structure: F is literally g00²+g01²+g10²+g11². This is ALREADY a sum of 4 squares — NO
# unit factor on F itself. The issue is ONLY whether the 4th square g11² separates from the first 3.
# g11 = w2 w5 + w3 w7. The first 3 generators define the regular block. The clean Morse-style split
# would need new coords (E1,E2,E3, core) with F = E1²+E2²+E3²+G². But g11 MIXES with the regular vars
# (w2,w5 appear in both g10/g01 AND g11). So a SOURCE-only coordinate change does NOT cleanly separate.
print("=== THE EXACT FORM of F∘χ — the honest answer ===")
print("F = g00²+g01²+g10²+g11² is LITERALLY a sum of 4 squares (NO overall unit factor on F).")
print("BUT g11 shares variables (w2,w5) with the regular generators g10,g01 — so a SOURCE-only c-o-v")
print("(renaming generators to coords) leaves g11 with E-dependence (computed: ∂(g11∘χ⁻¹)/∂E ≠ 0).")
print("=> F∘χ is NOT literally E1²+E2²+E3²+G²; it is E1²+E2²+E3²+(g11∘χ⁻¹)² with g11∘χ⁻¹ = G + E·(stuff).")
print()
print("So the bridge a114e07e needs is NOT a simple unit-strip. The clean S1.5 form needs the GENERATOR")
print("equivalence: rlctAt of the IDEAL (g00,g01,g10,g11) = rlctAt of (E1,E2,E3,G) where G is the Schur")
print("core — via Lemma1(2)-style ideal-generator invariance (Aoyagi Lemma 1(2): same ideal => same rlct),")
print("NOT a source-coordinate Morse split. Let me verify the IDEALS match.")
