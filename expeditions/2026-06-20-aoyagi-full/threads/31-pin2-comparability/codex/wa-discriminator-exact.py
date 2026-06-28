import sympy as sp
# W-a discriminator: r=1, H=[2,2,2], A11=3. Confirm bare LDU != Score, and Score = ACTUAL-layer-pivot LDU.
# Decode layers (reindexed r+(.-r) split), L=2. Deepest layer0=[[u0,0],[u1,0]], layer1=[[v0,v1...]]
# A11 = u0 = 3.  Off-diagonals: layer0 deepBlkZ=u1, layer1 deepBlkY=v1 (the other free deepest blocks).
# Take a concrete rational test point per the in-file discriminator.
sp.init_printing()
# decode layer0 = deepest0 + dev0 ; reindexed blocks: A0=u0+X0, Y0=0+Y0read, Z0=u1+Z0read, T0=0+T0
# decode layer1 = deepest1 + dev1 ; A1=w0+X1, Y1=v1+Y1read, Z1=0+Z1read, T1=0+T1   (layer1: deepBlkZ=0)
u0,u1,w0,v1 = sp.Rational(3), sp.Rational(1,2), sp.Rational(2), sp.Rational(1,3)   # deepest constants
X0,Y0r,Z0r,T0 = sp.Rational(1,5),sp.Rational(1,7),sp.Rational(1,11),sp.Rational(1,13)
X1,Y1r,Z1r,T1 = sp.Rational(1,17),sp.Rational(1,19),sp.Rational(1,23),sp.Rational(1,29)
def blk2(A,B,C,D): return sp.Matrix([[A,B],[C,D]])
# ACTUAL decode layers (full blocks):
L0 = blk2(u0+X0, 0+Y0r, u1+Z0r, 0+T0)
L1 = blk2(w0+X1, v1+Y1r, 0+Z1r, 0+T1)
M  = L0*L1                                   # prod(decode x), reindexed
# Score = (2,2)-Schur of M over its OWN (1,1) block (unframed, actual-pivot):
Sc_actual = M[1,1] - M[1,0]*(M[0,0])**(-1)*M[0,1]
# BARE per-layer LDU: S0=(T0)-(Z0r)(1+X0)^-1(Y0r); ... pivot 1+X (WRONG per W-a)
S0_bare = T0 - Z0r*(1+X0)**(-1)*Y0r
# bare layer1: T1 - Z1r*(1+X1)^-1*Y1r
S1_bare = T1 - Z1r*(1+X1)**(-1)*(v1+Y1r)   # note Y1 carries deepBlkY=v1
bare_LDU = S0_bare*S1_bare    # rough bare product (scalar r=1)
print("Score (unframed ACTUAL-layer-pivot Schur of M):", float(Sc_actual), " exact:", Sc_actual)
print("bare per-layer LDU (pivot 1+X):               ", float(bare_LDU))
print("=> bare != Score  (W-a: bare is FALSE). Difference:", float(bare_LDU - Sc_actual))
print()
# Now the ACTUAL-layer-pivot per-layer cores (pivot A=u0+X, the conjugated dict):
S0_act = (0+T0) - (u1+Z0r)*(u0+X0)**(-1)*(0+Y0r)
S1_act = (0+T1) - (0+Z1r)*(w0+X1)**(-1)*(v1+Y1r)
# two-layer LDU with the cross term K (reindex_mul_schur_factor):
K = (0+Z1r)*((M[0,0]))**(-1)*(0+Y0r)    # the (1-K) cross uses prod(1,1)=M00
ldu_act = S0_act*(1-K)*S1_act
print("ACTUAL-layer-pivot two-factor LDU S0c*(1-K)*S1c:", float(ldu_act), " exact:", ldu_act)
print("Score - actual-LDU =", sp.simplify(Sc_actual - ldu_act), "  <== should be 0 (the W-a identity)")
