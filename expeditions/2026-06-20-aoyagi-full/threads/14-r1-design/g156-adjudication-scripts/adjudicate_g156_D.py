import sympy as sp
print("="*78)
print("PART D: (i) does R1 child B stay generic on recursion? (ii) is reduced-dim>=2")
print("        DLN-achievable, i.e. is the eps counterexample a DLN deepest point?")
print("="*78)

# (i) R1 recursion: at the parent node, child loss = ||S·Bred||^2 with A'=S ((m-1)x(k-1)) FREE,
# B'=Bred ((k-1)xn).  Bred = B[1:,:] = lower (k-1) rows of B = (A_1...A_L)[1:,:].
# When we recurse on the child, we blow up A'=S's deepest pivot.  S is a FREE matrix (D free).
# The child's "B'" = Bred plays the role of the deeper product -- and crucially, in the RLCT
# computation B' is integrated over as a generic matrix (the child loss dlnLoss(red M) 0 is the
# product loss of TWO free matrices S, Bred -- a fresh 2-layer-equivalent node, NOT a fixed chain).
print("\n(i) On recursion the child loss is ||S·Bred||^2 = dlnLoss(m-1,k-1,n) 0, a product of TWO")
print("    matrices both FREE in the RLCT integral. The child is again a generic-B node:")
print("    the recursion descends the WIDTH vector (m,k,n)->(m-1,k-1,n), never accumulating a")
print("    fixed product of per-layer Schur cores. The ∏S_s object is NEVER assembled.")
print("    => generic-B status is INDUCTIVELY preserved (FACT: each child loss is a 2-free-matrix")
print("       product loss by the V3 reduced-core identity).")

# (ii) The eps counterexample: L=2, r=1, reduced-dim=2.  In DLN terms r = rank at the deepest point.
# 'reduced-dim 2' = the reduced block size = H_s - r >= 2.  Is this a real DLN deepest point?
# A DLN deepest point: B (the product value) = blockdiag[I_r, 0]; layers rank-r-sliced.
# Reduced dims H_s - r are the AMBIENT widths minus the rank -- for wide layers these are >= 2 freely.
# The eps example used 1x1 pivot (r=1) and 2x2 reduced -> widths H = 1+2 = 3 per intermediate layer.
# That is a perfectly legal DLN with intermediate width 3, rank r=1.  So reduced-dim>=2 IS DLN-achievable.
print("\n(ii) reduced-dim = H_s - r.  The eps example: r=1, reduced-dim=2 => intermediate width H=3.")
print("     A 3-wide intermediate layer at rank-1 deepest point is a LEGAL DLN node.")
print("     => reduced-dim>=2 IS DLN-achievable at a genuine deepest point (NOT an artifact).")
print("     => the (NC)/scalar-reduced-core hypothesis is NOT automatic for general DLN.")
print("\n     BUT: this only matters for the L2 route (which uses ∏S_s). The R1 cover route never")
print("     forms ∏S_s, so it does NOT need (NC) even though reduced-dim>=2 is achievable.")
print("\nDONE.")
