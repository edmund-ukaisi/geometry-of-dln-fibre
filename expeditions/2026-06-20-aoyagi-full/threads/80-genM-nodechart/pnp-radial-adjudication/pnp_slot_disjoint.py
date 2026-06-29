# Examine the slot-dependency between the three factor maps to settle the ordering question (Codex Q1 subtlety).
# schurFrameMap: (X,K,N,E) -> (K, KN, XK, XKN+E).  INPUT slots read: X,K,N,E.  OUTPUT: the frame blocks.
# chainUnitCLM N: (W,C) -> (W, C-NW).  It reads N as a PARAMETER (fixed matrix), and inputs (W, C).
# lduCoreMap: (l,q,u) -> K=LDU(l,q,u).  INPUT: l,q,u (LDU coords).  OUTPUT: the K block.
#
# CRITICAL distinction: in the BANKED ChartFactor design (RouteMFactorMaps), chainUnitCLM's N is a FIXED
# PARAMETER (chainChartFactor takes Nblk : Matrix as an argument), NOT a coordinate being transformed.
# So chain reads (W,C) from coords and uses a CONSTANT N. It does NOT consume the N-coordinate-slot.
# Similarly schurFrameMap reads N as an INPUT coordinate (z.2.1) and outputs KN. 
#
# So the question is: are these factors composed as SELF-MAPS on the SAME (Fin N -> R), each touching
# a SUB-BLOCK via its CLE E and identity elsewhere (conjBlockFactor)? If each factor is 
# E.symm ∘ (factorMap × id_R) ∘ E, then it transforms ONLY its block and leaves R (everything else) FIXED.
# Then two factors with OVERLAPPING blocks do NOT commute; DISJOINT blocks DO commute.
#
# The det telescope (composeFold_abs_det) is ORDER-INDEPENDENT for the |det| (product commutes), so for the
# DET the ordering is IRRELEVANT. But the MAP IDENTITY phi = composeFold[...] ∘ radial DOES depend on order
# if blocks overlap. Codex's point: schur reads+rewrites the N slot (outputs KN into the KN-block), and 
# chain also involves N. If they share the N region, order matters for the MAP (not the det).
print("KEY RESOLUTION:")
print("- For the DETERMINANT (the deliverable |det DB|=∏engine): composeFold_abs_det telescopes to a PRODUCT")
print("  of per-factor |det|, which COMMUTES. Ordering is IRRELEVANT for the det. (proof-level fact)")
print("- For the MAP IDENTITY phi = B ∘ blowup: ordering matters ONLY if factor blocks OVERLAP.")
print()
print("In the banked conjBlockFactor design each factor is E.symm ∘ (factorMap × id) ∘ E -- it touches ONLY")
print("its block, R fixed. The three per-boundary factors read DISTINCT chart roles:")
print("  ldu_s  : the K-role slot (LDU coords l,q,u of K_s)  -> outputs the K_s matrix")
print("  schur_s: the (X,K,N,E)-roles -> outputs the Schur frame [[K,KN],[XK,XKN+E]]")
print("  chain_s: the (W, C_{s+1}) slots, N_s a PARAMETER -> the chaining shear")
print()
print("Codex's concern (schur consumes N that chain needs) is about whether schur and chain share the N slot.")
print("=> MUST PIN with genm-detfderiv: are the factors block-DISJOINT (commute, any order) or sequential")
print("   (schur consumes N -> chain must precede schur)? The banked _abs_det's are per-factor regardless,")
print("   so the DET is safe EITHER WAY; only the map-identity proof's rewrite order is affected.")
