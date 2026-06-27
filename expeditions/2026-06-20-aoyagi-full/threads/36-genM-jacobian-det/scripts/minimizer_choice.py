# Both minimizers of (2,2,1) give minAdm=2, so the radial active.card=2 either way -> det |u_p|^{2-1}=|u_p|^1.
# The CHOICE of T* affects WHICH coords are active (the block distribution) and the SPECTATOR monomials, but
# NOT the pivot exponent (always minAdm-1) NOR the rate (always u^2). So any argmin works. The formaliser just
# needs a deterministic selection (e.g. lexicographically-first minimizer, or any explicit witness T* with
# Mval=minAdm). The det leafH_pivot = minAdm-1 is INVARIANT across minimizers.
print("Any minimizer T* of Mval works: radial active.card = minAdm (invariant), pivot exp = minAdm-1 (invariant),")
print("rate = u^2 (invariant). The CHOICE only affects the spectator-monomial distribution (k=0 axes, threshold-irrelevant).")
print("=> NOT a wall. The construction fixes ONE explicit witness T* with Mval(M,T*)=minAdm (an argmin),")
print("   which exists by definition of minAdm = min Mval. Formaliser supplies it per-M or via a choice.")
