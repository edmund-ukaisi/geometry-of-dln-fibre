import sympy as sp

# ============================================================================
# Build the ACTUAL C5 node loss and test the hnode factorization.
# Chain at the active node: P = D · C  where
#   C = active factor (a-dim prefix → its image), columns = [survivor U | complement w]
#   D = downstream product (acts on C's image, kills everything at the deepest point)
# At the deepest point the FULL product is 0. Near it, in blow-up coords, we test the form.
#
# The C5 mechanism (g138): split C's image = survivor(rank b) ⊕ complement(rank a-b).
# - Complement: rank-1 defect, blow up NOW (C1 micro-step). Its column couples to the NEXT factor.
# - Survivor: rank-b, passes through downstream full-rank layers, killed at the LAST layer (C2 pass-through).
#
# CRITICAL QUESTION: the downstream product D acts on BOTH survivor and complement images.
# If D mixes them (shared rows), ‖D·C‖² has CROSS terms between survivor-block and complement-block
# ⟹ NOT the clean hnode form (G² would not equal the pure survivor reduced-core).
# ============================================================================

a = 3   # prefix rank
b = 2   # survivor rank; complement rank = a-b = 1

# Active factor C : (prefix coords, dim a) → image, dim a. In the split basis:
#   survivor columns span a b-dim subspace; complement column spans the remaining 1-dim.
# Post-blow-up of the complement defect, the complement column = ε · (e + bounded), ε exceptional.
# Use blow-up coordinate: the complement direction carries the exceptional scalar; downstream
# the complement couples to the next factor → the Schur bilinear b_i·E_j.

# Downstream product D : a-dim → output. At the deepest point D·(survivor image) and
# D·(complement image) are the two column-blocks. Frobenius: ‖[D·U | D·w]‖² = ‖D·U‖² + ‖D·w‖².
# COLUMN-block orthogonality in Frobenius norm is AUTOMATIC (different columns), REGARDLESS of
# whether D mixes the row-spaces. ‖[X|Y]‖²_F = ‖X‖²_F + ‖Y‖²_F always. So the split into
# survivor-cols-block and complement-col-block is ALWAYS Frobenius-orthogonal.

# Let's VERIFY this is the right reading and that the survivor-block IS the reduced core.
# Model: C's image columns. survivor: U (a×b). complement: ε·v (a×1), ε the blow-up coord.
# D: downstream (output_dim × a). 
out = 4
D = sp.Matrix(out, a, sp.symbols(f'd0:{out*a}', real=True))
U = sp.Matrix(a, b, sp.symbols(f'u0:{a*b}', real=True))
v = sp.Matrix(a, 1, sp.symbols(f'v0:{a}', real=True))
eps = sp.Symbol('epsilon', real=True)

# Full active factor (in split coords): C = [U | eps*v]  (a × (b+1)=(a))  -- here b+1 = 3 = a, good.
C = U.row_join(eps*v)
P = D*C   # the product = [D*U | eps*(D*v)]   (out × a)
loss = sum(P[i,j]**2 for i in range(P.shape[0]) for j in range(P.shape[1]))

# Frobenius splits by columns:
survivor_block = D*U                 # out × b  -- the survivor's product (→ reduced core after recursion)
complement_block = eps*(D*v)         # out × 1  -- the complement's product (→ Schur bilinear)
loss_survivor = sum(survivor_block[i,j]**2 for i in range(out) for j in range(b))
loss_complement = sum(complement_block[i,0]**2 for i in range(out))

diff = sp.expand(loss - (loss_survivor + loss_complement))
print("CHECK 1 — block-column Frobenius orthogonality (survivor ⟂ complement):")
print("  ‖P‖² - (‖D·U‖² + ‖ε·D·v‖²) =", diff, "  [expect 0 = no cross terms]")
print()

# So loss = ‖D·U‖²  +  ε²·‖D·v‖².
# The SURVIVOR block ‖D·U‖² is the reduced-chain core on the survivor = G² (= dlnLoss S.red 0, recursed).
# The COMPLEMENT block ε²·‖D·v‖² is the exceptional-weighted column. After the C1 Schur step on the
# complement, ‖D·v‖² near the deepest point = Σ_j (E_j)² (regular squares, the next-factor coupling).
# But we need the FULL hnode form: Σreg² + Σ(b_i E_j + SΓ_ij)². Where does the BILINEAR b_i·E_j come from?
print("CHECK 2 — where the hnode BILINEAR coupling arises (the C1 Schur step on the complement):")
print("""
  After block-column split: loss = ‖D·U‖²(survivor reduced core) + ε²‖D·v‖²(complement).
  The complement is rank-1, coupled to the NEXT factor. The C1 Schur step on the complement
  produces the standard hnode bilinear. BUT the survivor ‖D·U‖² is a SEPARATE Frobenius block.

  ⟹ The hnode form for the C5 node is NOT the single-block hnode. It is:
       flatCore = [complement C1 Schur: Σreg² + Σ(b·E + SΓ_comp)²]  +  ‖D·U‖²(survivor)
     The survivor ‖D·U‖² is an ADDITIONAL summand — itself a reduced core to be recursed SEPARATELY.
""")
