import sympy as sp
# RECONCILE: the joint multi-radial wedge vs the achiever rate. Test on (2,2,2).
# (2,2,2): minAdm=3. Achiever peel: t=1 -> block (2-1)(2-1)=1, leaf (1,2)->minAdm(1,2)=2. Total 1+2=3.
# So codims along the achiever path: [1, 2] (layer-1 block 1, leaf block 2). Sum=3=minAdm. ✓
# JOINT multi-radial wedge with blocks c=[1,2]: 
#   ∫ r1^{1-1} r2^{2-1} (r1^2+r2^2)^{-c'} dr1 dr2 = ∫ r1^0 r2^1 (r1^2+r2^2)^{-c'} dr1 dr2.
#   multi-polar R (2 radii -> but weights differ): total exponent = (c1-1)+(c2-1) + (#radii) - 2c'
#     Actually: ∫∫ r1^{0} r2^{1} (r1^2+r2^2)^{-c'}. Polar r1=R cosθ, r2=R sinθ:
#     = ∫ R^{0+1} (R^2)^{-c'} · R dR · (θ-integral) = ∫ R^{1 - 2c' + 1} dR = ∫ R^{2-2c'} dR.
#     diverges iff 2-2c' <= -1 iff c' >= 3/2 = minAdm/2. ✓✓ EXACT.
cp = sp.Rational(3,2)
print("(2,2,2) joint wedge blocks c=[1,2]: ∫ r1^0 r2^1 (r1^2+r2^2)^{-c'}")
print("  total: ∫ R^{(0)+(1)+1 -2c'} dR = R^{2-2c'}, at c'=3/2: R^{-1} = ⊤. ✓ (matches minAdm/2)")
print()
# GENERAL: blocks c_1..c_K (the achiever PATH block codims), Σ=minAdm. 
#   ∫ ∏ r_i^{c_i - 1} (Σ r_i^2)^{-c'} ∏ dr_i.  multi-polar R^{K-1} sphere × radius R:
#   ∏ r_i^{c_i-1} = R^{Σ(c_i-1)} · (angular) = R^{minAdm - K} · (ang). (Σr_i^2)^{-c'}=R^{-2c'}.
#   ∏dr_i = R^{K-1} dR dΩ. Total: R^{minAdm-K -2c' + K-1} = R^{minAdm-1-2c'}.
#   diverges iff minAdm-1-2c' <= -1 iff c' >= minAdm/2. ✓✓✓ EXACT for ALL block decompositions!
mA, K, cp2 = sp.symbols('minAdm K'), None, sp.symbols('cp')
print("GENERAL (K blocks, Σc_i=minAdm): multi-polar exponent = minAdm-1-2c'.")
print("  diverges iff c' >= minAdm/2. INDEPENDENT of K and the block split. EXACT.")
print()
print("=> The joint multi-radial wedge gives divergence at EXACTLY c'=minAdm/2 for ANY decomposition")
print("   of minAdm into the achiever path's block codims. This is the achiever rate, not an overcount.")
print()
# CRUCIAL CHECK: is it an OVERCOUNT (divergence at c' < minAdm/2, which would be WRONG -- would mean
# the wedge region has rlct < minAdm/2, contradicting the upper bound)? 
# At c' slightly below minAdm/2: exponent minAdm-1-2c' > -1, so ∫R^{>-1} CONVERGES. So the wedge 
# region's threshold is EXACTLY minAdm/2 -- it does NOT overcount. The boundary is sharp. ✓
print("NOT an overcount: at c'<minAdm/2, exponent>-1, integral CONVERGES. Boundary sharp at minAdm/2. ✓")
