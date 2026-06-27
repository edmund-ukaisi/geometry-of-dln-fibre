# What rank pattern does each banked chart actually resolve?
# (4,4,2,2): pb4422 blows up A2 (the deepest 2x2 factor) entirely -> A2 has rank dropping to 0. The center
#   is {A2=0} (codim 4). A0,A1 full rank. So the rank pattern: rank(A0)=4? no, A0 is 4x4, A1 4x2 (rank<=2),
#   A2 2x2. The product A0 A1 A2 : 4x2. Center {A2=0} => product=0. The "descent ranks" of the achiever:
#   the surviving rank after each matrix at the center: after A0: rank<=4, after A0A1: rank<=2, after A0A1A2: 0.
#   But the CODIM is purely from A2=0 (4 entries). The Aoyagi T*=(4,2,0): t^1=4 (rank after layer1 pair),
#   t^2=2, t^3=0. Hmm T has L=3 entries for L=3 (4 widths). t^1=4,t^2=2,t^3=0.
# The Aoyagi r_j x c_j = the codim CONTRIBUTION per layer, and sum=minAdm. The ACTIVE coords of the radial
# blow-up = these minAdm residual entries, located in the chart's matrix slots. For 4422 they're all in A2
# (the j=2 block, 2x2=4). For 334 they're split: j=0 block (2x2=4 in A0's normal) + j=1 block (1x4=4 in A1).
#
# So the radial active set = the union of the Aoyagi residual-block ENTRIES, placed in the chart's Params slots.
# The COUNT is minAdm. The chain Text/Eblock width gap is IRRELEVANT to the chart -- the hand-built charts
# place the actives directly in the Params matrix entries by the Aoyagi block structure, NOT via the chain
# Schur-frame E-blocks. The chain (genBlkFlatStruct) was a SEPARATE (rate-only, now-degenerate) construction.
#
# CONCLUSION: the |active|=minAdm rule is CORRECT and uniform (Aoyagi blocks, cols=M_{j+1}). The chain
# E-block count is a DIFFERENT quantity and must NOT be used to count the radial actives. The formaliser must
# place the minAdm actives by the Aoyagi r_j x c_j blocks in the Params matrix slots (as pb4422/pb334 do),
# NOT read them from the chain decoder's E-slots.
print("VERDICT: |active| = minAdm = sum_j (Aoyagi r_j*c_j), cols c_j = M_{j+1} - t^j (AFTER width).")
print("The radial active set = the Aoyagi residual-block entries placed in the Params matrix slots.")
print("The chain Schur-frame E-block count (cols M_s BEFORE) is a DIFFERENT number; do NOT use it for actives.")
print("Matches both banked hand-built charts (pb4422 card=4, pb334 card=8).")
