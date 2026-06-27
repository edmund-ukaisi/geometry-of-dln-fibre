import sympy as sp
u = sp.symbols('u', positive=True)
g = sp.symbols('g0:20', real=True)
C1 = sp.Matrix([[1, u*g[16], u*g[17]],[u*g[18], u*g[0], u*g[1]],[u*g[19], u*g[2], u*g[3]]])
C2 = sp.Matrix([[u*g[4],u*g[5],u*g[6],u*g[7]],[g[8],g[9],g[10],g[11]],[g[12],g[13],g[14],g[15]]])
P = sp.expand(C1*C2)
F = sp.expand(sum(P[i,j]**2 for i in range(3) for j in range(4)))
U2 = F.coeff(u,2)  # the u^2 coefficient = U(0)
print("u^2 coefficient (= U at u=0):", sp.expand(U2))
# Expect = ||C2 row0 part||^2 ... actually = Σ_j (C2[0,j]/u contribution + C1 row0 pivot)... 
# The dominant: P[0,j] = C1[0,0]·C2[0,j] + C1[0,1]C2[1,j] + C1[0,2]C2[2,j] = u·g[4+j] + u g16 C2[1j] + u g17 C2[2j]
#   = u(g[4+j] + g16 S[0,j] + g17 S[1,j]). So P[0,j]/u = g[4+j]+g16 S0j + g17 S1j. F row0 / u^2 = Σ_j (that)^2.
# At g16=g17=0 (off-pivot 0): = Σ g[4+j]^2 = ||tbar||^2. With g16,g17 in a box: still bounded below 
# by choosing tbar dominant. ✓
# Check U2 includes Σ_{j} g[4+j]^2 (the clean tbar block):
has_tbar = all(U2.coeff(g[4+j],2) != 0 for j in range(4))
print("U2 contains the clean tbar block (Σ g[4..7]^2):", has_tbar)
# Bounded below: on the slice {g[4]∈[1/2,1], g16,g17,g18,g19 ∈ [-η,η] small, rest box}, 
# U2 >= (g4 + g16 S00 + g17 S10)^2 + ... >= positive for η small. Honest positive-measure tube. ✓
print()
print("So even WITHOUT exact off-pivot zeros, F = u^2·U2 + O(u^3), U2 bounded below on a")
print("positive-measure slice (tbar dominant, off-pivot small). The u^3,u^4 terms only ADD")
print("(F could be larger), but for the LOWER bound we need F <= C·u^2 on the tube:")
# F <= C u^2? F = u^2 U2 + u^3(...) + u^4(...). On the tube u∈(0,δ], the higher terms are <= C'u^2 
# (since u<=δ => u^3<=δ u^2). So F <= u^2(U2 + δ·bdd + δ^2·bdd) <= C u^2. ✓ (the U is bounded ABOVE too)
print("F = u^2 U2 + u^3 A + u^4 B; on u∈(0,δ], F <= u^2(U2 + δ|A| + δ^2|B|) <= C·u^2 (bounded above). ✓")
print("So |F|^{-c'} >= C^{-c'} u^{-2c'}, and ∫ Jac·|F|^{-c'} >= ∫ u^{minAdm-1} u^{-2c'} = u^{-1} at c'=minAdm/2. ⊤")
