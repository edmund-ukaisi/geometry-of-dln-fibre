import sympy as sp
# C4 (Fubini pinch) + lex termination — verify and pin for the design.
print("=== C4: width-1 / rank-pinch / s=0 node SEPARATES (Fubini, not coupled blow-up) ===")
# (3,1,3): C1 is 3x1, C2 is 1x3. product C1·C2 is 3x3 rank-1. The inner width is 1 (a bottleneck).
# ‖C1·C2‖² = ‖C1‖²·‖C2‖² (rank-1 outer product Frobenius factorises!). Verify:
c = sp.Matrix(3,1, sp.symbols('c0:3')); d = sp.Matrix(1,3, sp.symbols('d0:3'))
P = sp.expand(c*d)
f = sp.expand(sum(P[i,j]**2 for i in range(3) for j in range(3)))
nc2 = sp.expand(sum(c[i,0]**2 for i in range(3)))
nd2 = sp.expand(sum(d[0,j]**2 for j in range(3)))
print(f"  (3,1,3): ‖C1·C2‖² − ‖C1‖²·‖C2‖² = {sp.expand(f - nc2*nd2)}  (0 ⟹ FACTORISES)")
print("  ⟹ a width-1 inner layer makes the core a PRODUCT ‖C1‖²·‖C2‖² of two SEPARATE smooth blocks.")
print("  The resolution here is FUBINI (rlct of a product = sum of rlcts via the product-min), NOT a")
print("  coupled Schur blow-up. Blowing up {C1=0} alone leaves an EMPTY Schur complement (s=0 stuck).")
print("  C4: BRANCH — coupled layers → Schur blow-up; width-1/pinch/s=0 layers → Fubini product-min.")
print()
print("=== Lex termination: ΣM-drop INSUFFICIENT at full-rank/no-drop layers; use lex(depth, ΣM) ===")
print("""
pp3's C2 (full-rank pass-through): descend on a FULL-RANK first factor (no rank drop) so a later-factor
drop is resolved. At such a step the first factor's width does NOT drop (it's full rank, pass it through),
so ΣM might not strictly decrease at that single step — the DEPTH L drops instead (one factor consumed/
absorbed). So the sound termination measure is LEX (L, ΣM): either the depth L strictly drops (a factor
fully resolved / passed through), or L same and ΣM strictly drops (a Schur rank-reduction). lex(L,ΣM) is
well-founded on ℕ×ℕ. This FIXES the hdrops-insufficiency #132 flagged implicitly (ChainDimSplit.measure_drops
needs Σdrop>0, which CAN be 0 at a full-rank pass-through where only depth drops).
""")
print("=== (4,3,2) thin-product: geometric codim = Mval, NOT generic-Jacobian rank (C1) ===")
print("  For thin products the gen-Jacobian/Hessian rank (8) ≠ the geometric codim (Mval=12). The (k,h)")
print("  read for the lower bound must use the GEOMETRIC codim (Mval), from the strict transform of {prod=0},")
print("  not the raw Jacobian rank. This is C1 (read (k,h) from the full pulled-back density).")
