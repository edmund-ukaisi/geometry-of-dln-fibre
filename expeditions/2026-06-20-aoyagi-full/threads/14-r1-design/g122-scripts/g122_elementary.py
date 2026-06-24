import sympy as sp
# Is there an ELEMENTARY chain-structure route to the (a)-split at v, avoiding the general
# constant-rank/Morse theorem (which Mathlib lacks)?
#
# The (a)-split: F(v+W) = [regular q-square block] + [homogeneous residual core], q = Jac rank at v.
# The general route uses the constant-rank theorem (implicit function thm) to solve the q regular
# generators. The ELEMENTARY question: can the chain/GL structure give the split by EXPLICIT
# polynomial substitution (Gaussian elimination on the bilinear generators), no IFT?
#
# KEY STRUCTURAL FACT of the DLN family at v: the fibre {prod=B} is a GL-gauge orbit's stratification.
# At v, the gauge group GL(M^1) x ... x GL(M^{L+1}) acts; v can be moved to a BLOCK-NORMAL form by an
# EXPLICIT gauge element (block_elimination, #5, DONE -- it's a finite matrix factorization, no IFT).
# In block-normal coords, the regular block is the rank-r identity corner, and the residual is the
# reduced-chain zero-core -- an EXPLICIT algebraic split, no implicit function theorem.
print("=== The elementary route: GL-gauge to block-normal form (block_elimination, no IFT) ===")
print("At v, an EXPLICIT gauge element (block_elimination #5, a finite matrix factorization P B Q =")
print("corner-block, DONE in Lean, NO constant-rank theorem) moves v to block-normal form. In those")
print("coords the loss germ splits EXPLICITLY: the rank-r corner = regular block, the reduced-chain")
print("residual = homogeneous core. The split is a CHANGE OF VARIABLE by an explicit polynomial gauge,")
print("not an implicit-function solve.")
print()
# But wait: the gauge moves v, but the SPLIT of the GERM (regular quadratic + homog core) still needs
# to separate the q linear-leading generators from the core. Is THAT elementary?
# Test on (2,2,2) v=(A1=0, A2 invertible): the q=4 regular generators are (W1 v2)_ij, LINEAR in W1.
# Since v2 is invertible, the map W1 -> W1 v2 is a LINEAR ISOMORPHISM (explicit, det = det(v2)^2 != 0).
# So the 4 generators ARE 4 of the coordinates after the linear change W1' = W1 v2. EXPLICIT, no IFT.
a=sp.symbols('a0:4'); b2=sp.Matrix([[2,1],[1,3]])  # v2 invertible
W1=sp.Matrix(2,2,a)
gens_lin = W1*b2  # the linear-leading part of the generators
print("=== (2,2,2) v=(A1=0,A2 inv): regular generators (linear part) = W1·v2 ===")
print("  W1·v2 =", [sp.expand(gens_lin[i,j]) for i in range(2) for j in range(2)])
print("  v2 invertible => W1 -> W1·v2 is a LINEAR ISO (det v2^2 =", sp.det(b2)**2, "!= 0).")
print("  So the 4 regular generators ARE coordinates after an EXPLICIT linear change. NO IFT needed.")
print()
print("=== The general worry: at v where the regular block is NOT linear-iso-clean ===")
print("At a deeper v (L>=3 intermediate), the q regular generators have linear parts that are NOT a")
print("clean linear iso of a coordinate block -- they mix. Solving them = the constant-rank step.")
print("CAN this be done elementarily for the chain family? Test the L=3 intermediate v.")
