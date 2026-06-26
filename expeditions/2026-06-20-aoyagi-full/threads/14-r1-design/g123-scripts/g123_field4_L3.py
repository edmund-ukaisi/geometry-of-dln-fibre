import sympy as sp
# Is field 4 (reduced-chain map) genuinely needed at general M, or does (2,2,2)'s direct-quadratic
# resolvedForm generalize? Test: at general M, does ONE lemma2-style straighten + ONE blow-up resolve,
# or does the resolved form ITSELF contain a smaller chain core needing recursion (field 4)?
#
# (2,2,2): step1Residual = ‖Â B‖², Â=[[1,t1],[t2,t3]] (2x2, pivot 1 unit), B 2x2. After lemma2
# straighten, resolvedForm = E²+F0²+(qE+δG)²+(qF0+δH)² -- a quadratic whose vertex blow-up (step2)
# THEN has a residual smooth block (the δ-branch needs step3). So even (2,2,2) recurses (step2->step3)!
# The δ-branch block G²+H²(+...) IS a smaller core. Let me check: is that block a ‖prod(C')‖²?
#
# Look at step2D's block (from the Lean resolvedForm_step2D):
#   block = E'²+F0'²+(q E'+G)²+(q F0'+H)²   (E'=z2, F0'=z3)
z2,z3,q,G,H=sp.symbols('z2 z3 q G H')
block = z2**2 + z3**2 + (q*z2+G)**2 + (q*z3+H)**2
print("=== (2,2,2) δ-branch block (step2D residual, the part needing step3) ===")
print("  block =", block)
# Is this block a ‖prod(C')‖² for a smaller chain? It's E'²+F0'²+(qE'+G)²+(qF0'+H)². Factor as
# ‖[[1,?],[q,?]] · [[E',F0'],[?,?]]‖²? Compare to ‖Â' B'‖² with Â'=[[1,0],[q,1]], B'=[[E',F0'],[G,H]]:
Ap=sp.Matrix([[1,0],[q,1]]); Bp=sp.Matrix([[z2,z3],[G,H]])
prodp=sp.expand(Ap*Bp)
normp=sum(prodp[i,j]**2 for i in range(2) for j in range(2))
print("  ‖[[1,0],[q,1]]·[[E',F0'],[G,H]]‖² =", sp.expand(normp))
print("  block - that =", sp.expand(block - normp))
print()
print("=> the (2,2,2) δ-branch block IS ‖Â' B'‖² for a SMALLER chain (Â'=[[1,0],[q,1]], B'=[[E',F0'],[G,H]])")
print("   = a reduced-chain core! So (2,2,2) DOES recurse into a smaller chain at the δ-branch -- but")
print("   the Lean anchor handles it as a literal SMOOTH BLOCK (G²+H²+...) via step3 blow-up, NOT via")
print("   a reduced-chain MAP. It WORKS for (2,2,2) because the block is small enough to monomialize")
print("   directly. For general M, the residual block is a LARGER ‖prod(C')‖² that needs the RECURSION")
print("   (field 4: the reduced-chain map exposing M' + core') to close -- you can't just monomialize a")
print("   big chain core directly; you re-straighten + re-blow-up it (the C2 recursion).")
