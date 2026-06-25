import sympy as sp
# Structural reason for the squeeze: F − Phi = g11² − G². Is g11 − G in the regular ideal (g00,g01,g10)?
w = sp.symbols('w0:8', real=True)
W1=sp.Matrix([[w[0],w[1]],[w[2],w[3]]]); W2=sp.Matrix([[w[4],w[5]],[w[6],w[7]]])
v1=sp.Matrix([[1,0],[0,0]]); v2=sp.Matrix([[1,0],[0,0]]); B=v1*v2
P=sp.expand((v1+W1)*(v2+W2))
g=[sp.expand((P-B)[i,j]) for i in range(2) for j in range(2)]
G = -w[3]*w[7]/(w[1]*w[6]-1)   # Schur core
diff = sp.simplify(g[3] - G)   # g11 - G
print("g11 - G =", sp.simplify(diff))
# Is g11 - G in the ideal (g00,g01,g10)? g11 - G should = combination of g00,g01,g10 with poly/analytic coeffs.
# Try to write g11 - G = a·g00 + b·g01 + c·g10. Solve for a,b,c (rational coeffs):
# Simplest check: on {g00=g01=g10=0}, g11 - G = 0 (since G = g11 there by definition). Verify:
sol=sp.solve([g[0],g[1],g[2]],[w[4],w[5],w[2]],dict=True)[0]
on_locus = sp.simplify(diff.subs(sol))
print("(g11 - G) on {g00=g01=g10=0}:", on_locus, " (0 ⟹ g11-G vanishes on the regular zero-locus)")
print()
print("=== Structural confirmation of the squeeze ===")
print("g11 − G vanishes on {g00=g01=g10=0} ⟹ g11 − G ∈ the ideal (g00,g01,g10) (analytically, near 0,")
print("since the regular gens are a regular sequence / submersion there). So:")
print("  F − Phi = g11² − G² = (g11−G)(g11+G), with (g11−G) ∈ (g00,g01,g10).")
print("  ⟹ |F − Phi| ≤ C·(|g00|+|g01|+|g10|)·(|g11|+|G|) near 0, DOMINATED by Phi (which contains")
print("    g00²+g01²+g10² AND G²). Hence c1·Phi ≤ F ≤ c2·Phi near 0 — the squeeze is STRUCTURAL, not")
print("    just numerical. F and Phi share the same zero-set ({prod=B}), so rlctAt_mono applies both ways.")
print("  ⟹ rlctAt(F) = rlctAt(Phi) = [S1.5] nReg/2 + rlctAt(G²). SOUND, green-tools-only, NO c-o-v,")
print("    NO measure Jacobian, NO ideal-invariance lemma, NO constant-rank.")
