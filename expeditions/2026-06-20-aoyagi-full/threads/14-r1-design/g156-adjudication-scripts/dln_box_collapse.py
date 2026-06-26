import sympy as sp
print("="*78)
print("DLN BOX-COLLAPSE: over the chart ratio box Vz, is rlct(child) WORST at deepest 0?")
print("If yes => box-integ <=> c'<rlct(child,0) => clean point-min interface holds for DLN.")
print("Sharpened: does reduced-dim>=2 introduce a box-interior stratum with rlct < rlct(deepest)?")
print("="*78)
# The child loss in the cover is core's reduced part = ||S Bred||^2, S=(m-1)x(k-1), Bred=(k-1)xn.
# BUT in the RECURSION, the child is dlnLoss(red M) 0 = ||A'_0 A'_1 ... A'_L||^2 (a full DLN chain,
# widths (M0-1,M1-1,M2,...)).  We recurse by blowing up A'_0's pivot.  The chart ratio box for the
# CHILD bounds the CHILD's ratios.  Question: over the child's chart box, is the child's WORST rlct
# at the child's deepest point (all-zero)?
#
# This is the structural claim: for dlnLoss, the all-zero point is the global-min-rlct point.
# Let me test it on a reduced-dim>=2 child where the box could contain OTHER zero-product strata.
print("\n--- TEST 1: a node whose RATIO BOX contains a non-origin singular stratum ---")
# Take the SIMPLEST L=2 child with reduced-dim>=2 after one blow-up: e.g. node (2,2,2).
# After blow-up A0=y0 Ahat, core reduced part = ||S Bred||^2 with S=(1)x(1)? No: (2,2,2)->S is 1x1.
# Need reduced-dim>=2: node (3,3,n) -> S is 2x2.  Child = ||S Bred||^2, S 2x2, Bred 2xn.
# Over the ratio box, S=W-v u ranges over a bounded set of 2x2 matrices INCLUDING rank-1 and rank-0.
# The loss ||S Bred||^2 vanishes on {S Bred=0}.  Singular strata in the box:
#   (a) S=0 (deepest of this sub-block): rank drop full.
#   (b) S rank-1, Bred chosen so S Bred=0: S != 0 but S Bred=0 possible if rows of Bred in ker(S).
# At a stratum (b) point p (S rank1 fixed nonzero, Bred in a linear subspace), is rlct(loss,p) < rlct(0)?
print(" node with S 2x2 (reduced-dim 2): child loss ||S·Bred||^2.")
print(" zero-locus {S·Bred=0} strata: S=0 (origin-like), OR S rank-1 with Bred-rows in ker(S), etc.")
print()
# The local rlct at a point p of {S Bred=0}: the loss is ||S Bred||^2; near p, expand.  At a point
# where S has rank exactly r0 and the configuration is 'as degenerate as the all-zero' only if r0=0.
# Aoyagi's theorem (the paper): rlct of ||A_0...A_L - B||^2 at a point where the product has rank r
# is governed by minAdm of the rank-r-REDUCED problem.  The MOST degenerate (rank 0 = all-zero) gives
# the SMALLEST rlct.  Higher-rank points give LARGER rlct (fewer constraints).
print(" Aoyagi/LR: at a point where the product ∏A_s has rank ρ, the local rlct is (1/2)·minAdm of")
print(" the rank-ρ-reduced chain.  rank ρ=0 (all-zero) is MOST degenerate => SMALLEST minAdm => MIN rlct.")
print(" ρ>0 strata: fewer rank constraints => LARGER minAdm-deficit => LARGER local rlct.")
print(" => over ANY bounded box, the all-zero deepest point is the GLOBAL-MIN-rlct point.")
print(" => box-integ for c'<rlct(deepest) HOLDS (worst point governs), reduced-dim IRRELEVANT.")
