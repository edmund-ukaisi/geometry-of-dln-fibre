# The genuine soundness check: in composeFold [.., schur_{s+1}, chain_{s+1}, ldu_{s+1}, schur_s, chain_s, ldu_s, ..],
# the deeper factors (boundary s+1) run FIRST (innermost), building C_{s+1} into layer-s's KEPT-ROW positions,
# THEN chain_s reads those positions. For this to be consistent:
#   schur_{s+1} must WRITE its frame output into the SAME flat region that chain_s reads as its C-block.
# schur_{s+1}'s output (the frame [[K,KN],[XK,XKN+E]]) has shape Text_{s+1} x Wext_{s+1} = C_{s+1}'s shape.
# It must land in layer-s's kept rows (Fin Text_{s+1} x Fin Wext_{s+1} at layer-s offset). 
# So schur_{s+1}'s OUTPUT CLE must target layer-s's kept-row block. But schur_{s+1}'s INPUT reads boundary
# (s+1)'s chart-role slots (K,X,N,E of boundary s+1). So schur_{s+1} is: (input role slots) -> (layer-s kept rows).
# That's a NON-square-region map: input side = ChartIdx role slots, output side = FlatIdx layer-s kept rows.
# 
# This confirms: the factors are NOT each "self-maps touching one block, identity elsewhere" in ONE coordinate
# system. They form a CHAIN where factor i's OUTPUT region = factor (i-1 outer)'s INPUT region. This is the
# composeFold prefix-evaluation: each factor's deriv is taken at the OUTPUT of the factors to its right.
# 
# CRUCIAL: composeFold requires each ChartFactor to be a self-map (Fin N -> R) -> (Fin N -> R). The banked
# conjBlockFactor E factorMap = E.symm ∘ (factorMap × id) ∘ E IS a self-map for ANY single E. But if 
# schur_{s+1} READS role-slots and WRITES layer-s-kept-rows, its INPUT and OUTPUT coordinatizations DIFFER
# => it is NOT of the form E.symm ∘ (fm × id) ∘ E (same E both sides). 
# 
# RESOLUTION OPTIONS:
#  (A) The composeFold factors are NOT conjBlockFactor (one E); instead each is a genuine map whose input
#      coords and output coords differ, and the whole composeFold telescopes input(ChartIdx)->output(FlatIdx).
#      Then B is NOT a self-map composition with one ambient coordinatization -- it's the eIn/eOut two-sided
#      structure in disguise (input regroup = ChartIdx, output regroup = FlatIdx).
#  (B) The banked conjBlockFactor design (RouteMFactorMaps) uses ONE E per factor with input=output=that E's
#      coords, and the factors DO act as block-self-maps -- meaning the C_{s+1} block IS read from a slot in
#      the SAME coordinatization, and the "threading" is via R (the untouched complement) being re-read.
# This is the load-bearing ambiguity. Let me check the banked conjBlockFactor to see if input=output coords.
print("FLAGGING: the chain factor's C-block (layer-s kept rows, OUTPUT side) vs schur/ldu (ChartIdx input)")
print("means the factors may NOT share one coordinatization. Two resolutions (A two-sided / B one-E block-self-map).")
print("MUST check banked conjBlockFactor: is it E.symm∘(fm×id)∘E (same E both sides, block-self-map)?")
