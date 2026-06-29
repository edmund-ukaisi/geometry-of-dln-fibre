import sympy as sp
print("="*78)
print("QUESTION (1): coreF(bareAbsorb(ψq)) = coreF(conjAbsorb(q)) near wstar?  EXACT.")
print("  ψ = psiSplitRawL2CoreConj (the conj joint move, core -> T1'c = Wc^-1 Brc).")
print("="*78)
print()
print("Banked decode identities (inner ball):")
print("  coreF(bareAbsorb(p)) = frobSq(prod(deepestM)(decode p.core + schurCorrection(p.reg,p.spec)))")
print("  coreF(conjAbsorb(p)) = frobSq(prod(deepestM)(decode p.core + schurCorrectionConj(p.reg,p.spec)))")
print()
print("LHS = coreF(bareAbsorb(ψq)):  p := ψq.")
print("  (ψq).core = decode-updated to T1'c at last layer; (ψq).reg/spec = ψ-edited reg.")
print("  = frobSq(prod( decode(ψq).core + schurCorrection((ψq).reg,(ψq).spec) ))")
print("RHS = coreF(conjAbsorb(q)):")
print("  = frobSq(prod( decode q.core + schurCorrectionConj(q.reg,q.spec) ))")
print()
# Model at (2,2,2) r=1, the deepestM core product is a 2-layer 1x1-core multiplication:
# deepestM core slots are scalars t0,t1 (the reduced cores M_s, here 1x1).  prod = t0*t1.
# (The reduced model: deepestM dims have reduced width; cores are the (H-r)-blocks.  At r=1,
#  H=2, reduced width 1, cores are scalars.)
t0,t1 = sp.symbols('t0 t1', real=True)        # decode q.core (original)
# reg/spec reads (drive the schur corrections):
X0,Y0,Z0,X1,Y1,Z1 = sp.symbols('X0 Y0 Z0 X1 Y1 Z1', real=True)
# bare schur correction s_s = -Z_s (1+X_s)^{-1} Y_s ; conj uses deepBlk-shifted reads but at the
# BOUNDARY (deepBlkY_0=0, deepBlkZ_1=0) the boundary corrections simplify.  Model generic:
def schur(Z,X,Y): return -Z*(1+X)**(-1)*Y
# CONJ correction of ORIGINAL q (RHS): corrConj_s(q.reg,q.spec).  At boundary it uses the conj reads.
corrConj0 = schur(Z0,X0,Y0); corrConj1 = schur(Z1,X1,Y1)   # schematic conj (boundary)
RHS_core0 = t0 + corrConj0
RHS_core1 = t1 + corrConj1
RHS = (RHS_core0*RHS_core1)**2   # frobSq(prod) = (t0+..)(t1+..) squared (1x1 product)
print("RHS = ( (t0+corrConj0)(t1+corrConj1) )^2")
print()
# LHS: ψ updates the core: (ψq).core_last = T1'c (a Schur-corrected joint value), layer0 core unchanged.
# T1'c = Wc^-1 Brc -- the joint-move value.  And the BARE correction is applied to ψq's reads.
# ψ also edits reg (Y1->Y1'c).  So LHS_core1 = T1'c + schurBare1((ψq).reg,(ψq).spec).
# The KEYSTONE structure: coreF(conjAbsorb(ψq)) = Score (TRUE).  Score = the Schur complement of the
# FULL framed product = the value the WHOLE bridge is driving to.  And coreF(bareAbsorb(ψq)) = Score
# ONLY IF W-a holds (FALSE).  So bareAbsorb(ψq) != conjAbsorb(ψq) in general.
# Question (1) compares bareAbsorb(ψq) vs conjAbsorb(q) [NOT conjAbsorb(ψq)].  Two differences:
#   (A) bare vs conj correction (the W-a gap), AND (B) moved ψq vs original q.
# For (1) to hold, these two differences would have to CANCEL.  Test if that's structurally possible.
print("LHS vs RHS differ in TWO ways simultaneously:")
print("  (A) bare-correction vs conj-correction (the W-a gap, found FALSE), AND")
print("  (B) evaluated at MOVED ψq vs ORIGINAL q.")
print("For (1) TRUE, (A) and (B) must exactly cancel.  Structural test:")
print()
# The ONLY banked bridge is coreF(conjAbsorb(ψq)) = Score = coreF(conjAbsorb(q))? NO -- conjAbsorb(q)
# is NOT Score in general (Score is the joint-moved Schur complement; conjAbsorb(q) is the un-moved
# conj correction).  And bareAbsorb(ψq) = Score would need W-a.  So:
#   coreF(bareAbsorb(ψq)) =?= coreF(conjAbsorb(q))
#   would chain as Score [if W-a] =?= coreF(conjAbsorb(q)).  But coreF(conjAbsorb(q)) is the
#   conj correction at the ORIGINAL point, which is NOT Score (Score needs the joint move ψ).
print("  coreF(conjAbsorb(q)) is the conj Schur correction at the ORIGINAL (un-moved) q.")
print("  Score is the joint-MOVED Schur complement (needs ψ).  coreF(conjAbsorb(q)) != Score.")
print("  And coreF(bareAbsorb(ψq)) = Score requires W-a (FALSE).")
print("  => (1) would need [bareAbsorb(ψq)=Score via FALSE W-a] AND [Score=conjAbsorb(q) FALSE].")
print("  TWO false links; no cancellation route.  => (1) is FALSE.")
