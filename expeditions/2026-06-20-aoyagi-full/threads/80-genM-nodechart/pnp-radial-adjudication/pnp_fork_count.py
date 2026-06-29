# The coordinate BUDGET (flatDim) is FIXED = sum M_s M_{s+1}. The decoder READS coords from disjoint slots
# via chartIdxEquiv. The chart-role count: per boundary, K+X+N+E (=Text_s*Wext_s? no, =(t+r)(t+c)) + W lift.
# chartDim_eq_flatDim: (sum roleDim) + 1(radial) - 1(fixed residual) = flatDim.
# So there are EXACTLY flatDim coordinate SLOTS. The decoder assigns them. The "+1 radial -1 fixed" means:
#   ONE slot is the radial pivot u; ONE E-slot is FIXED (the -1, the pivotEIndicator anchor).
# 
# So BOTH decoders read flatDim slots. The difference:
#   genBlkFlatLive (Fix A): NO E-slot fixed. Then count = flatDim but there's NO radial gauge -> 
#     the "+1 radial -1 fixed" accounting BREAKS: you'd have flatDim+1 DOF (over-determined) OR the leaf
#     reader rfin must DROP one slot. Actually genBlkFlatLive's rfin is a free reader -> if it reads a
#     FRESH slot, count overshoots (as we saw: 9>8). The live decoder is NOT square unless rfin reroutes.
#   genBlkFlatLiveR1 (Fix B): the pivot E-slot (0,0) FIXED to 1; that slot's coordinate REROUTED to rfin.
#     => count = flatDim exactly (the -1 fixed E + the rerouted leaf slot). SQUARE BY CONSTRUCTION.
#
# CONCLUSION on the count: Fix B (fixed-pivot R1) is square by construction (this is WHY it was chosen).
# Fix A (live-pivot, all-E-free) OVERSHOOTS unless rfin is constrained -- the count is the open RISK,
# and our 222 build SHOWS the overshoot (9 vs 8). So Fix A does NOT trivially give count=minAdm-1.
print("(2,2,2): flatDim=8. Fix A (all-E-free + free leaf): 9 coords -> OVERSHOOTS (not square).")
print("         Fix B (R1, E(0,0) fixed=1, leaf rerouted): 8 coords -> SQUARE by construction.")
print()
print("=> The count was the REASON for the fixed pivot. Fix A's count does NOT hold without extra constraint.")
print("   So the FORK is really: Fix B (right count, but map-identity needs AFFINE radial, not pivotBlowupOn).")
