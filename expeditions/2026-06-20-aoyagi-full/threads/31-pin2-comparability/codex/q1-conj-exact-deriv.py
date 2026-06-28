import sympy as sp
# (a) deepBlkZ_0 != 0 generically: the deepest layer-0 in the rThreshold split.
# Per the brief/branch: deepest layer-0 block = [[u0, 0],[u1, 0]] in r+(.-r) split (cols>=r killed),
# u0 = A11 (≠1 generically), u1 = Z0 (free under IsDeepLayers). So toBlocks21 = u1 = deepBlkZ_0.
# Confirm: for a rank-r deepest layer with free lower-left, deepBlkZ_0 is an independent free entry.
print("(a) deepBlkZ_0 = (reindex deepest_0).toBlocks21 = u1 (the free lower-left of a rank-r layer).")
print("    Under IsDeepLayers the layer is rank r with arbitrary column space basis => u1 free => != 0 generically. CONFIRMED structurally.\n")

# (b) D(schurCorrectionConj_0)(0): full-layer  -(dZ+zt)(dA+xt)^-1(dY+yt), layer-0 dY=0 (cols>=r killed), dZ!=0, dA!=0.
t = sp.Symbol("t"); x,y,z = sp.symbols("x y z"); dZ,dA,dY = sp.symbols("dZ dA dY")
corr = -(dZ + z*t)*(dA + x*t)**(-1)*(dY + y*t)
print("(b) GENERAL conj correction series in t:")
ser = sp.series(corr, t, 0, 2).removeO()
print("   ", sp.expand(ser))
print("    value(0) =", sp.simplify(corr.subs(t,0)), "  D(.)(0) =", sp.simplify(sp.diff(corr,t).subs(t,0)))
print("\n    LAYER-0 (dY=0, dZ!=0, dA!=0):")
c0 = corr.subs(dY,0)
print("    value(0) =", sp.simplify(c0.subs(t,0)), "   D(.)(0) =", sp.simplify(sp.diff(c0,t).subs(t,0)),
      "   <-- = -dZ*y/dA  != 0  (genm-l2thread RIGHT)")
print("\n    LAYER-(L-1) (dZ=0, dY!=0):  D(.)(0) =", sp.simplify(sp.diff(corr.subs(dZ,0),t).subs(t,0)),
      "   = -dA^-1*y*... (the readY/Y-leg)")

# (c) bare vs conj: does coreAbsorb(bare) absorbed-core equal the conj Schur core? Only if dA=1,dZ=dY=0.
print("\n(c) bare schurCorrection at the SAME point: -(zt)(1+xt)^-1(yt) -> value/deriv both 0;")
print("    conj Schur core uses dA(!=1), dZ(!=0): so deepestCoreF(coreAbsorb_bare q) != conjSchur unless dA=1,dZ=0.")
print("    => the readback (hsub4core: bare-absorbed core = Score) is the MISMATCH (the 659 'mis-dictionaried' sorry).")
