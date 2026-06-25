import sympy as sp
print("="*78)
print("CRUX: is the chart box {y0,z} shrinkable when U (small A) shrinks?")
print("The pivot chart: a_00=y0, a_0j=y0*u_j, a_i0=y0*v_i, a_ij=y0*w_ij.")
print("So z=(u,v,w) are RATIOS = a_0j/y0 etc.  Shrinking A does NOT bound the ratios.")
print("="*78)
# Concretely: A small (||A||<delta) but on the chart {a_00 != 0}, the ratio u_j = a_0j/a_00 can be
# ARBITRARILY LARGE if a_00 is much smaller than a_0j. So phi_p^{-1}(U) is NOT contained in
# {|y0|<eps} x {bounded z}.  The chart DOMAIN V_p (where pivot |a_00| is the argmax) bounds the
# ratios: on the argmax cell |a_00| >= |a_ij| for all (i,j), so |u_j|=|a_0j/a_00|<=1, |v_i|<=1, |w_ij|<=1.
# THAT is why the cover uses the ARGMAX cells -- the ratio box IS bounded ([-1,1]) on the argmax cell,
# INDEPENDENT of how small A is.  The bound |ratio|<=1 is a SCALE-INVARIANT (homogeneous) constraint.
print("\nKEY: on the ARGMAX cell {|a_00| = max_ij |a_ij|}, the ratios satisfy |u|,|v|,|w| <= 1.")
print("  This bound is SCALE-INVARIANT: it holds for ALL ||A||, not just small A.")
print("  => the ratio box Vz = [-1,1]^(mk-1) is FIXED (scale-invariant), NOT shrinkable with U.")
print("  => the 'z' coords (ratios) range over a FIXED box [-1,1]^(mk-1) even as y0->0.")
print()
print("CONSEQUENCE for the recursion:")
print("  core = ||Ahat B||^2, Ahat = [[1,u],[v,W]] with (u,v,W) in the FIXED box [-1,1].")
print("  The child ||S Bred||^2, S = W - v u, also has (S, Bred) ranging where:")
print("   - S = W - v u: W,v,u in [-1,1] (fixed box) => S in a FIXED bounded box;")
print("   - Bred: the deeper-layer coords, ALSO need a box.")
print("  So the core's z-integral IS over a FIXED box in the ratio coords (u,v,W) -- the y0->0")
print("  limit does NOT shrink them.  The child integrability is needed over THIS fixed box.")
print()
print("BUT: is that 'fixed box' integrability STRICTLY STRONGER than the child's point-RLCT?")
print("  The child loss ||S Bred||^2 -- its NON-integrability can only come from its OWN zero-set")
print("  (where S Bred = 0), which is a germ at the child's deepest point.  On the FIXED ratio box,")
print("  the only singularity of |child|^{-c} is along {child=0}; |child|^{-c} is integrable over")
print("  the fixed box iff c < rlct(child) -- PROVIDED the child has no OTHER singular strata in the")
print("  box (away from the deepest point).  THAT is the real question: does the child loss have")
print("  singularities AWAY from its deepest point inside the fixed ratio box?")
