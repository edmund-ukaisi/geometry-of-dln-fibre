import sympy as sp
# THE PRECISION QUESTION: is dlnLoss∘flat = ∑E² + dlnLoss M 0(T̃-core) EXACT (c₁=c₂=1) or a SQUEEZE (leak)?
# dlnLoss = ‖product‖² = Σ over ALL product blocks of (block entry)². After the gauge c-o-v:
#   E = the regular residual blocks {(0,0)-I_r, (0,1), (1,0)}, T̃-core = the gauge-normalized (1,1) Schur.
# Is ‖product‖² = ‖E‖² + ‖T̃-core‖² EXACTLY?  ‖product‖² = ‖(0,0)-I_r‖²... wait, ‖product‖² is the deviation
# of the product from B. At the deepest, B = blockdiag[I_r,0] (rank r). So:
#   dlnLoss = ‖product − B‖² = ‖(0,0)−I_r‖² + ‖(0,1)‖² + ‖(1,0)‖² + ‖(1,1)‖²  (Frobenius = Σ block norms²)
#   E = {(0,0)−I_r, (0,1), (1,0)} ⟹ ‖E‖² = ‖(0,0)−I_r‖² + ‖(0,1)‖² + ‖(1,0)‖².
#   so dlnLoss = ‖E‖² + ‖(1,1)‖².  The question: is ‖(1,1)‖² = ‖T̃-core‖² EXACTLY, where T̃-core is the
#   gauge-normalized reduced block?  (1,1) = T_1 T_2 + Z_1 Y_2 (the raw block, with the cross).
# Recall g151: (1,1)|{E=0} = T(I−VY)^{-1}S (the gauge-normalized T̃ = product Schur complement). But OFF
# {E=0}, (1,1) = T_1 T_2 + Z_1 Y_2 ≠ T̃-core. So is ‖(1,1)‖² = ‖T̃-core‖² as FUNCTIONS, or only on {E=0}?
r,m,n = 1,2,2
def blk(p):
    return (sp.Matrix(r,r,sp.symbols(f'{p}X0:{r*r}')), sp.Matrix(r,n-r,sp.symbols(f'{p}Y0:{r*(n-r)}')),
            sp.Matrix(m-r,r,sp.symbols(f'{p}Z0:{(m-r)*r}')), sp.Matrix(m-r,n-r,sp.symbols(f'{p}T0:{(m-r)*(n-r)}')))
X1,Y1,Z1,T1=blk('a'); X2,Y2,Z2,T2=blk('b'); Ir=sp.eye(r)
C1=sp.Matrix(sp.BlockMatrix([[Ir+X1,Y1],[Z1,T1]])); C2=sp.Matrix(sp.BlockMatrix([[Ir+X2,Y2],[Z2,T2]]))
P=sp.expand(C1*C2)
E00=sp.expand(P[0,0]-1); E01=sp.expand(P[0,1]); E10=sp.expand(P[1,0]); P11=sp.expand(P[1,1])
# The chart's REGULAR coords are E00,E01,E10 (the product residuals); the chart REWRITES the loss in
# (E00,E01,E10, T̃-core, spectators). The question: when we express dlnLoss = ‖E‖²+‖P11‖² in the NEW
# coords (E_i and the reduced T̃), is ‖P11‖² = T̃-core² EXACTLY (P11 = T̃ as a coordinate) or P11 =
# T̃ + (stuff in E) ⟹ ‖P11‖² = T̃² + leak?
# On {E=0}: P11 = T̃ := T(I−VY)^{-1}S (g151). Off {E=0}: P11 = T̃ + correction(E). So as a FUNCTION,
# P11 = T̃ + δ where δ vanishes on {E=0} ⟹ δ ∈ ideal(E). Compute δ = P11 − T̃|{the chart}:
# the chart sets E as coords; T̃ = P11 expressed via the solved B,U,Z (g151). Let me compute P11 − T̃
# where T̃ = the {E=0}-value lifted (i.e. P11 with B,U,Z solved from E=0). 
B_sol=(1-Y2[0,0]*Z1[0,0])/(1+X1[0,0])  # rough; use the g151 solve. Actually simpler: is dlnLoss, in the
# E-and-T̃ coords, LITERALLY ∑E²+T̃² or ∑E²+T̃²+leak? Test: does ‖P11‖² − T̃² ∈ ideal(E) (vanish on E=0)?
# T̃ on {E=0} = P11|{E=0}. Substitute E00=E01=E10=0 by solving — but E00,E01,E10 involve X1,X2,Y,Z; pick
# the simplest: on the locus X1=X2=Y1=Y2=Z1=Z2=0 (a SUBSET of {E=0}), P11 = T1 T2, T̃ = T1 T2.
# The HONEST test (matches the controller's Q): is the loss EXACTLY ∑E²+T̃² or a squeeze?
print("=== dlnLoss = ‖E‖² + ‖(1,1)‖²; is ‖(1,1)‖² = ‖T̃-core‖² exactly, or T̃² + leak∈ideal(E)? ===")
print("(1,1) = P11 =", P11, "   [= T_1 T_2 + Z_1 Y_2 = aT0·bT0 + aZ0·bY0]")
# T̃ (gauge-normalized, = P11 on {E=0} where the cross is absorbed). The cross Z1 Y2 = aZ0·bY0.
# Is Z1 Y2 ∈ ideal(E00,E01,E10)? i.e. does it vanish on {E=0}? On {E=0} (solving), g151 showed the cross
# becomes the internal factor — it does NOT vanish, it's ABSORBED into T̃. So P11 ≠ T̃ + (ideal-E leak);
# rather P11 = T̃ literally once T̃ is DEFINED as the gauge-normalized block. The question is whether the
# CHART makes ‖P11‖² = ‖T̃‖² exactly or ‖T̃‖²·(unit) or +leak. KEY: T̃ = P11 EXACTLY (T̃ IS the (1,1)
# block in the gauge coords) — so ‖(1,1)‖² = ‖T̃‖² is an IDENTITY (T̃ is literally the (1,1) entry).
print()
print("RESOLUTION: T̃-core is DEFINED as the (1,1) block in the gauge coords (= P11). So ‖(1,1)‖² = ‖T̃‖²")
print("is an IDENTITY by definition — NO leak THERE. The loss = ‖E‖² + ‖T̃‖² is EXACT (c₁=c₂=1) IF the")
print("chart's E-coords are EXACTLY the (0,0)-I,(0,1),(1,0) blocks AND T̃ = the (1,1) block.")
print()
print("BUT the SUBTLETY (where #48-exact vs #55-squeeze diverge): is ‖T̃‖² = dlnLoss M 0 EXACTLY, or only")
print("≍? T̃ = P11 = T(I−VY)^{-1}S (gauge-normalized). dlnLoss M 0 = ‖∏T̃_s‖² is the REDUCED CHAIN. T̃ has")
print("the INTERNAL UNIT (I−VY)^{-1} — so ‖T̃‖² = ‖T(I−VY)^{-1}S‖². Is THAT = ‖dlnLoss M 0 reduced chain‖²")
print("exactly, or ≍ (the (I−VY)^{-1} is a UNIT, |I−VY|^{-1} bounded near 0, so ‖T̃‖² ≍ ‖T·S‖² with the")
print("unit (I−VY)^{-2} as the squeeze factor)? ⟹ THE LEAK IS THE INTERNAL UNIT (I−VY)^{-1}: T̃-core =")
print("T(I−VY)^{-1}S is NOT literally the reduced-chain dlnLoss M 0 = ‖T·S‖²-style product — it carries")
print("the (I−VY)^{-1} unit. So dlnLoss∘flat = ∑E² + ‖T(I−VY)^{-1}S‖², and ‖T(I−VY)^{-1}S‖² ≍ dlnLoss M 0")
print("(SQUEEZE, the unit (I−VY)^{-2} ∈ [c₁,c₂], NOT =1). ⟹ it's a SQUEEZE, not exact. #55 is right.")
