import sympy as sp
# Refine: directionality + cheaper-route check for the UPPER bound.
#
# Upper bound: rlctAtOn(F) >= minAdm/2  <=>  ∫_U |F|^{-c'} < ⊤  for all c' < minAdm/2.
# This is FINITENESS of the threshold integral below minAdm/2.
#
# Watanabe: ∫_U |F|^{-c'} < ⊤  iff  c' < rlctAtOn(F) = global min RLCT. So the upper bound is 
# EXACTLY "rlctAtOn(F) = ½ minAdm" 's >= direction. It's the hard analytic direction.
#
# Q: does a cover by threshold-only charts give a VALID upper bound (maybe with wrong value)?
# A cover ∫_U |F|^{-c'} <= Σ_leaf ∫_leaf monomial^{-c'} (the cover_le inequality). The RHS is finite 
# iff c' < min_leaf threshold. If the cover uses threshold-only charts, min_leaf threshold = 
# ½·(threshold-only minAdm) = ½·3 = 3/2 for (3,3,4) -- which is SMALLER than the true ½·8=4.
# So a threshold-only cover would prove ∫_U|F|^{-c'} < ⊤ only for c' < 3/2 -- a WEAKER (smaller) 
# upper bound rlctAtOn >= 3/2. That's TRUE but gives rlctAtOn >= 3/2, NOT >= 4. 
# To prove rlctAtOn >= 4 you need the cover's min leaf threshold to be 4 = correct resolution.
print("THRESHOLD-ONLY cover gives upper bound rlctAtOn >= 3/2 for (3,3,4) -- TRUE but WEAK (need >=4).")
print("The cover_le RHS finiteness threshold = ½·(cover's minAdm). Wrong cover => wrong (weak) bound.")
print()
# CRUCIAL: the cover must ACTUALLY cover U up to null (the cover_le INEQUALITY ∫_U <= Σ_leaf must hold).
# A threshold-only cover that MIS-resolves corank strata may NOT validly cover -- if a corank stratum 
# is under-resolved, the change-of-variables identity ∫_U = Σ_leaf ∫_leaf FAILS (the charts don't 
# tile U up to null). So threshold-only doesn't even give a valid (weak) upper bound on the corank 
# strata -- it gives a wrong DECOMPOSITION.
print("Worse: a mis-resolving cover may not VALIDLY tile U (the ∫_U = Σ_leaf identity fails on corank).")
print("So the cover for the upper bound must CORRECTLY resolve corank strata to even be a valid cover.")
print()
# CHEAPER ROUTE via global F lower bound? Upper bound needs |F| NOT TOO SMALL, i.e. F >= (something 
# with controlled vanishing). A clean global bound: F = ||P||^2 >= 0, and near the fibre {P=0}, 
# F ~ dist^2... but the dist^2 to the determinantal variety {rank P <= r} has its OWN RLCT = the 
# codim. So a global F >= dist^2 bound just relocates the problem to the determinantal variety's RLCT
# -- which IS minAdm (the codim). No free lunch.
print("CHEAPER via global F lower bound: F >= dist(·, fibre)^2; but dist^2's RLCT = the codim = minAdm.")
print("Relocates, doesn't avoid. The corank strata's codim must be computed correctly either way.")
print()
print("VERDICT Q3: the UPPER bound IS corank-sensitive. It needs the corank strata resolved correctly")
print("(coupled diag(b) charts), OR the cited analytic bound rlct >= ½ codim_min. The wedge (lower bd)")
print("does NOT give it. Honest move: commit to Aoyagi's coupled-diag(b) recursion as the chart")
print("producer for the UPPER bound (the cover), OR cite the >= direction.")
