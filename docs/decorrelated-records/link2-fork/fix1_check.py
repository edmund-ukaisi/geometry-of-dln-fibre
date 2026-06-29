import sympy as sp
print("="*78)
print("FIX 1 TEST: is deepestEFull(0, c, s) = deepestEFull(0, 0, s) for ALL spec s?")
print("  i.e. is the reg residual core-independent on the FULL {reg=0} hyperplane?")
print("="*78)
print()
print("STRUCTURE: deepestEFull reads {11,12,21} of M = reindex(prod(framedParamsPivot q)).")
print("framedParamsPivot embeds the per-layer blocks (A_s = pivot+readX, Y_s = readY, Z_s = readZ,")
print("T_s = core) into the layer matrix.  The reads readX/Y/Z are functions of the (reg,spec) slot.")
print()
print("KEY: the gauge slot is partitioned by regGaugeIdxSplit into reg-half (BoundaryPivotIdx, the")
print("pivot/boundary entries) and spec-half (the complement).  X/Y/Z entries split across BOTH.")
print("So at reg=0, spec=s: SOME of X/Y/Z are 0 (reg-half) and SOME are nonzero (spec-half, =s).")
print()
print("The leak (verified): M12 gets core via y0*T1, M21 via z1*T0 — the core couples to the")
print("Y0 and Z1 READS.  FIX 1 holds IFF those specific reads (Y0, Z1) live in the REG half")
print("(=> they're 0 at reg=0, so the leak term y0*T1, z1*T0 vanishes at reg=0 regardless of spec).")
print()
print("Model the WORST CASE for FIX 1: suppose Y0, Z1 (the leak-carrying reads) live in the SPEC")
print("half.  Then at reg=0, spec=s: y0=s_a != 0, z1=s_b != 0, so M12 ⊃ s_a*T1, M21 ⊃ s_b*T0 —")
print("the core LEAKS into the read blocks even at reg=0.  => FIX 1 would FAIL.")
print()
# To decide, I must determine: in framedParamsPivot, do the OFF-DIAGONAL reads Y_s, Z_s that
# carry the core-leak come from reg or spec?  The block structure of deepestEFull's reads:
# deepestEFull reads {11,12,21} = the reg-RESIDUAL blocks (the deviation of the product from the
# rank-r corner).  The core T_s sits in the (2,2) block of each layer.  The leak M12 <- y0*T1:
# y0 is the (1,2)-block (Y) of LAYER 0; T1 is the (2,2) (core) of LAYER 1.  In the product
# P = A0*A1, P12 = A0_11*A1_12 + A0_12*A1_22 = (pivot)*Y1 + Y0*T1.  So the leak Y0*T1 uses Y0.
# Q: is the off-diagonal block Y_s a REG read or a SPEC read?
print("DECISIVE: In framedParamsPivot, is the off-diagonal Y_s/Z_s block a REG or a SPEC read?")
print("  The reg RESIDUAL that deepestEFull measures = (product − corner) in blocks {11,12,21}.")
print("  The reg slot (BoundaryPivotIdx) = the entries E reads for the residual = the {11,12,21}")
print("  product blocks' SOURCES.  The Y_s, Z_s per-layer blocks ARE the {12},{21} reg-deviation")
print("  inputs.  => Y_s, Z_s are REG reads (they're literally the off-diagonal residual the")
print("  reg-straightening targets).  The SPEC slot = the (2,2)-adjacent gauge d.o.f. NOT read")
print("  by the residual.")
