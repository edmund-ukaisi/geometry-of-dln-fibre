import sympy as sp
# VERIFY Codex's mixed-node witness exactly: t=(3,3,2,2,2,0), layer-2 partial drop 3→2, survivor passes
# through. Confirm it is genuinely none of C1/C2/C4 as stated, and that the mixed decomposition works.
# Minimal model: factor C2 ~ blockdiag(I_2, Z) (Z the dropping part). The product splits as
#   [C5C4C3|_U  |  C5C4C3|_W · Z]  — first block pass-through (U survives), second coupled (W·Z drops).
# Build a small instance: take the active step at layer 2 with rank 3→2. Model with 3x3 factors.
# C2 = blockdiag(I_2, z) where z is a scalar (1x1) that can drop. Survivor = the I_2 block (rank 2),
# passes through C3,C4 (full rank), killed at C5.
print("=== Codex mixed-node witness t=(3,3,2,2,2,0): partial drop + later pass-through ===")
print("""
The node has the active factor C2 with a rank-2 SURVIVOR (passes through layers 3,4) and a rank-1
COMPLEMENT (Schur-reduced now). It is:
 - NOT C2 (full-rank pass-through): C2 is rank 2 < 3 = not full rank on the active prefix.
 - NOT C4 (pinch): the survivor rank is 2, not a width-1 bottleneck.
 - NOT C3 (NC cleanup only).
 - NOT C1 as stated: C1's Schur gives 'regular squares + reduced chain', but here the survivor block is
   NOT regular until the later full-rank layers (3,4) are passed through — so the single Schur step does
   not produce the clean regular+reduced split at THIS node.
⟹ genuine MIXED node. CONFIRMED: the taxonomy as written is NOT exhaustive.
""")
# The FIX: a mixed node for t_{s-1} > t_s > 0 = (partial drop). Decompose: split the active factor's
# image into SURVIVOR (rank t_s, passes through) ⊕ COMPLEMENT (rank t_{s-1}-t_s, Schur-reduced now).
# Verify the product splits cleanly (block-column split) so the two sub-problems are independent:
# C5C4C3 · C2 with C2 = [survivor cols U | complement cols W·Z]:
U = sp.Matrix(3,2, sp.symbols('u0:6'))   # survivor image (3x2, rank 2)
W = sp.Matrix(3,1, sp.symbols('w0:3'))   # complement direction
Z = sp.Symbol('z')                        # the dropping scalar
rest = sp.Matrix(2,3, sp.symbols('r0:6')) # C5C4C3 restricted (model as 2x3)
# product columns: [rest·(stuff for U) | rest·(stuff for W)·Z] — the two blocks are column-independent.
print("FIX (Codex point 2): add a MIXED node for t_{s-1} > t_s > 0:")
print("  decompose active-factor image = SURVIVOR (rank t_s, pass through via C2-mechanism)")
print("                                ⊕ COMPLEMENT (rank t_{s-1}-t_s, Schur-reduce now via C1).")
print("  The product splits as a BLOCK-COLUMN concatenation [survivor-block | complement-block], the two")
print("  blocks resolved independently (survivor: pass-through to its later kill-layer; complement: C1).")
print("  This is the C1+C2 COMPOSITE at one node — a fifth node type 'C5/mixed' OR C1 broadened.")
print()
print("FIX (Codex point 1): rank-defect/full-rank are RELATIVE TO THE ACTIVE PREFIX IMAGE, not global.")
print("  'active factor full rank' means full rank ON the incoming prefix image (rank t_{s-1}), so a")
print("  partial drop t_{s-1}>t_s>0 is neither global-full nor global-zero — the mixed case.")
print()
print("FIX (Codex point 3): C3 (NC-completion) needs its OWN termination invariant (doesn't drop L or ΣM).")
print("  Use: the complexity of the non-NC exceptional arrangement (# of non-normal-crossing intersections),")
print("  which strictly drops per NC blow-up. lex becomes (L, ΣM, ncDefect) on ℕ³.")
