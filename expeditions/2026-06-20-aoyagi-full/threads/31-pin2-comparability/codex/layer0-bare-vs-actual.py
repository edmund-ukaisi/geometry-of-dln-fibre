import sympy as sp
# Layer-0: deepBlkY0 = 0 (cols>=r killed). Does bare layer-0 Schur = actual layer-0 Schur?
# bare:   S0_bare = T0 - Z0*(1+X0)^-1*Y0          (pivot 1+X0, off-diag readZ=Z0, readY=Y0)
# actual: S0_act  = T0 - (u1+Z0)*(u0+X0)^-1*Y0    (pivot u0+X0, off-diag deepBlkZ+readZ=u1+Z0, deepBlkY+readY=0+Y0)
u0,u1 = sp.symbols("u0 u1")
X0,Y0,Z0,T0 = sp.symbols("X0 Y0 Z0 T0")
S0_bare = T0 - Z0*(1+X0)**(-1)*Y0
S0_act  = T0 - (u1+Z0)*(u0+X0)**(-1)*(0+Y0)
print("S0_bare - S0_act =", sp.simplify(S0_bare - S0_act))
print("  (nonzero in general => bare layer0 != actual layer0; layer0 also needs the actual pivot)")
print()
# So hc_eq cleaning ONLY the last layer is INSUFFICIENT unless layer0 is ALSO re-expressed.
# Check: is there a reading where the absorbed-core layer0 ALREADY = actual-pivot? Only if the
# coreAbsorb shift for layer0 used deepBlkA/deepBlkZ -- i.e. the CONJUGATED correction, not bare.
# => The sub-4 hLDUtie hypothesis can only hold if schurCorrection in the absorbed tuple is the
#    CONJUGATED one (deepBlk+read), NOT the bare one. The hyp as-stated (bare schurCorrection) is the
#    object; the discharge theorem prod_deepestM_eq_schur_ldu_readback is actual-pivot. MISMATCH unless
#    the in-Lean schurCorrection = conjugated, OR the cleaning re-expresses BOTH layers.
print("Sanity: at u0=1,u1=0 (the FALSE 'bare-correct' premise), S0_bare - S0_act =",
      sp.simplify((S0_bare - S0_act).subs({u0:1,u1:0})))
