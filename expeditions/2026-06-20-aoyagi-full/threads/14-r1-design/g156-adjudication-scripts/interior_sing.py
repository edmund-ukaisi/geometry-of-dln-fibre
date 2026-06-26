import sympy as sp
print("="*78)
print("THE REAL CRUX: child box-integrability vs child point-RLCT")
print("On the FIXED ratio box Vz, is int |child|^{-c} < inf  <=>  c < rlct(child, deepest)?")
print("They differ IFF the child loss has interior singular strata in Vz with SMALLER local RLCT.")
print("="*78)
# child = ||S Bred||^2, a PRODUCT loss of an (m-1)x(k-1) matrix S and (k-1)xn matrix Bred.
# Singular locus of |child|^{-c}: where child = 0, i.e. S·Bred = 0.
# {S Bred = 0} as S, Bred range over the box.  This is the FULL zero-product variety of the
# (m-1,k-1,n) product map -- NOT just the origin (S=0 or Bred=0 or rank-deficient products).
# At a NON-origin point p of {S Bred = 0} (e.g. S != 0, Bred != 0, but S Bred = 0), the loss
# child = ||S Bred||^2 has a local RLCT rlct(child, p) which may DIFFER from rlct(child, 0).
print("\n{child=0} = {S·Bred=0}: the zero-product variety of the (m-1,k-1,n) map -- has MANY strata,")
print("not just the origin (e.g. S full row but Bred col in ker, etc).")
print()
# KEY FACT (the paper's whole point / Aoyagi): the MINIMUM RLCT over the deepest stratum is what
# governs.  The paper's rlct = (1/2)minAdm is the rlct AT THE DEEPEST POINT (all-zero), which is the
# MOST degenerate / SMALLEST-rlct point of the loss.  At any OTHER point p of {child=0}, the loss is
# LESS singular (rank drop is smaller), so rlct(child, p) >= rlct(child, 0).
# => int over the box converges at c < rlct(child,0) (the WORST point), since every other point is
#    EASIER.  So box-integrability for c < rlct(child,0) HOLDS, EQUAL to the point-RLCT.
print("PAPER FACT (Aoyagi/LR): the deepest point (all-zero) is the MOST degenerate point of dlnLoss;")
print("rlct(child, deepest) is the MINIMUM local rlct over the whole zero-locus {child=0}.")
print("At any other p in {child=0}, the rank drop is smaller => rlct(child,p) >= rlct(child,deepest).")
print()
print("=> By a compactness/partition-of-unity argument on the FIXED box Vz: |child|^{-c} is")
print("   integrable over Vz for every c < min_p rlct(child,p) = rlct(child,deepest).")
print("   So BOX-integrability over Vz  <=>  c < rlct(child,deepest)  -- EQUAL to the point-RLCT,")
print("   PROVIDED the deepest point is the global-min-rlct point (the paper's structural fact).")
print()
print("THE ARCHITECTURE VERDICT:")
print(" - The clean point-min rlct(node)=min{mk/2, n/2+rlct(child)} HOLDS AT THE VALUE LEVEL,")
print("   because the deepest point is the min-rlct point of the child (paper fact).")
print(" - BUT the PROOF of the GE leg over a fixed box needs, as an INPUT, that the child is")
print("   integrable over the WHOLE fixed box -- which requires controlling the child's rlct at")
print("   EVERY point of the box, i.e. that the deepest point is the global min.  This is exactly")
print("   the recursion threading: the child must be resolved/covered over its OWN fixed box too.")
print(" => the box-recursion is INTERNAL to the proof; the VALUE statement is the clean point-min,")
print("   but the proof-interface threads box-integrability (= the child's argmax-cover applied")
print("   recursively), NOT merely the child's point-RLCT as a black box.")
