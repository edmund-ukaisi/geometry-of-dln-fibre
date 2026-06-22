import sympy as sp
# No ideal-swap tool is green. So the bridge must be a SOURCE c-o-v giving F∘χ = u·(ΣEᵢ²+G²), G E-free.
# Build the PROPER χ: new coords (E1,E2,E3, y) where E1=g00,E2=g01,E3=g10 (regular) and y = the CORE
# coordinates (w0,w1,w3,w6,w7), and check F∘χ⁻¹ = E1²+E2²+E3² + (core in y)²·unit OR similar.
#
# The issue before: g11 expressed via the generator-rename had E-dependence. But if χ maps the SOURCE
# (w) to (E1,E2,E3, y) where y = (w0,w1,w3,w6,w7) UNCHANGED and (w4,w5,w2)→(E1,E2,E3) via solving the
# regular gens, then F∘χ⁻¹(E,y) = E1²+E2²+E3² + g11(χ⁻¹(E,y))². The core term g11∘χ⁻¹ DOES depend on E
# (computed). So F∘χ⁻¹ = E1²+E2²+E3² + (G(y) + E·h(E,y))². Expanding:
#   = E1²+E2²+E3² + G(y)² + 2G(y)·E·h + (E·h)²  -- the cross terms 2G·E·h are NOT a clean ΣE²+G².
# So this χ does NOT give the clean form, even with a unit factor. CONFIRMED: source-rename insufficient.
#
# THE RESOLUTION (the honest soundest bridge, green-tool-only): use rlctAt_mono (squeeze) NOT an equality.
# OR: the regular block + core, even with cross terms, has rlct = nReg/2 + rlct(core) IF the cross terms
# are dominated. Let me check: is F∘χ⁻¹ = E1²+E2²+E3²+(G+E·h)² actually = a NONDEGENERATE quadratic in E
# (shifted) + G²? Complete the square: the E-block is a quadratic form; (G+E·h)² adds E·h cross terms.
# Treating G as the "core" and E as regular: near 0, the Hessian in E is positive-definite (the E1²+E2²+E3²
# dominates the (E·h)² which is higher order in E... no, (E·h)² is degree 2 in E too). Hmm.
# Let me just COMPUTE rlctAtOn(F) directly for (2,2,2) r=1 and confirm = nReg/2 + core-rlct = 3/2 + core.
w = sp.symbols('w0:8', real=True)
W1=sp.Matrix([[w[0],w[1]],[w[2],w[3]]]); W2=sp.Matrix([[w[4],w[5]],[w[6],w[7]]])
v1=sp.Matrix([[1,0],[0,0]]); v2=sp.Matrix([[1,0],[0,0]]); B=v1*v2
P=sp.expand((v1+W1)*(v2+W2))
g=[sp.expand((P-B)[i,j]) for i in range(2) for j in range(2)]
print("=== The cross-term issue: F∘χ⁻¹ = E1²+E2²+E3²+(G+E·h)², NOT clean ΣE²+G² ===")
print("Source generator-rename χ leaves cross terms 2G·E·h. So NEITHER a clean literal form NOR u·(clean).")
print()
print("=== The SOUNDEST green-tool bridge (no ideal-swap needed): MULTIPLICATIVE via the Schur FACTORIZATION ===")
print("The KEY realization: the L2 split should NOT go through 'F∘χ = ΣE²+G²' at all. The CLEAN route:")
print("apply the #125 deepest split as a GENERATOR/MATRIX identity FIRST (the unimodular Q's of #109/#125),")
print("giving prod-B = Q⁻¹ blockdiag[E_reg, C'] Q'⁻¹ as MATRICES, so ‖prod-B‖² = ‖E_reg‖² + ‖C'‖² by the")
print("BLOCK-DIAGONAL structure (orthogonal blocks in the Frobenius norm) — IF the Q's are such that the")
print("off-diagonal is cleared. Let me check: does the #125/#109 unimodular Q give ‖prod-B‖² literally")
print("splitting as ‖reg block‖² + ‖core block‖² (Frobenius = sum over disjoint entry blocks)?")
