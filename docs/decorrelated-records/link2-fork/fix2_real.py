import sympy as sp
print("="*78)
print("FIX 2 (real): does delta_s = schurCorrectionConj_s - schurCorrection_s carry a reg factor?")
print("="*78)
# schurCorrection_s (bare)   = -(readZ_s)(1 + readX_s)^{-1}(readY_s)         [pivot base 1]
# schurCorrectionConj_s      = -(Zbar_s+readZ_s)(Abar_s+readX_s)^{-1}(Ybar_s+readY_s) [base deepBlk]
# At L=2 boundary: layer0 has Ybar_0 = deepBlkY_0 = 0; layer-last has Zbar_last = deepBlkZ_last = 0.
# Abar_s = deepBlkA_s (unit, hDA).  At the FRONT-PIVOT deepest point Abar_s = I (leading block = I_r),
# so Abar_s = 1 (scalar, r=1).  Then:
#   conj_0 = -(Zbar0 + Z0)(1 + X0)^{-1}(0 + Y0) = -(Zbar0+Z0)(1+X0)^{-1} Y0
#   bare_0 = -(Z0)(1+X0)^{-1} Y0
#   delta_0 = conj_0 - bare_0 = -(Zbar0)(1+X0)^{-1} Y0    [the Zbar0 part]
# Role-assign reads: Y0 = Y_first = SPEC(p); Z0 = Z_first = REG(w); X0 = X_first = REG(u).
# Zbar0 = deepBlkZ_0 (a CONSTANT of the deepest point, generally != 0 at layer 0 — only deepBlkY_0=0).
u,v,w,p,q,x,T0,T1 = sp.symbols('u v w p q x T0 T1', real=True)
Zbar0, Ybar_last, Zbar_last, Ybar0 = sp.symbols('Zbar0 Ybar_last Zbar_last Ybar0', real=True)
# boundary: Ybar0 = 0, Zbar_last = 0.
Ybar0_v=0; Zbar_last_v=0
# layer0 reads: X0=u(reg), Y0=p(spec), Z0=w(reg).  layer-last reads: X1=x(spec), Y1=v(reg), Z1=q(spec).
delta0 = (-(Zbar0 + w)*(1+u)**(-1)*(Ybar0_v + p)) - (-(w)*(1+u)**(-1)*(p))
delta0 = sp.simplify(delta0)
delta1 = (-(Zbar_last_v + q)*(1+x)**(-1)*(Ybar_last + v)) - (-(q)*(1+x)**(-1)*(v))
delta1 = sp.simplify(delta1)
print("delta_0 =", delta0, "   (Zbar0 = deepBlkZ_0, a deepest-point constant)")
print("delta_1 =", delta1, "   (Ybar_last = deepBlkY_last, a deepest-point constant)")
print()
print("FIX 2 test: does delta carry a ‖reg‖ factor?  reg=(u,v,w), spec=(p,q,x).")
# delta_0 = -Zbar0*p/(1+u): at reg=0 (u=v=w=0): delta_0 = -Zbar0*p.  p is SPEC.  Zbar0 const != 0.
#   => delta_0(reg=0,spec=s) = -Zbar0*p != 0.  NO reg factor.  FIX 2 FAILS for delta_0.
print("  delta_0|reg=0 = -Zbar0 * p   (p=spec, Zbar0=deepBlkZ_0 const).  NONZERO if Zbar0,p != 0.")
print("  => delta does NOT carry a pure reg factor.  **FIX 2 FAILS** (unless deepBlkZ_0 = 0).")
print()
print("  Is deepBlkZ_0 = 0?  deepBlkZ_0 = (reindex deepestPoint_0).toBlocks21 = the (rows>=r,cols<r)")
print("  block of layer 0.  At L=2, layer 0 is BOUNDARY with deepBlkY_0=0 (cols>=r vanish) -- but")
print("  that's the (1,2) block (Y), NOT the (2,1) block (Z).  deepBlkZ_0 (rows>=r) need NOT vanish.")
print("  So generically deepBlkZ_0 != 0  => FIX 2 FAILS.")
