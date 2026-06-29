import sympy as sp
# Does the CLEANED bare-corrected product reconcile to the actual-pivot Score?
# sub-4 hc_eq: c''_0 = decode.core_0 + schurCorrection_0 (BARE, layer0 unchanged under psi);
#              c''_1 = (1 - l2K) * l2S1   (the W-cleaned last layer, via hWdet).
# Then hLDUtie claims prod(c'') = Score integrand. Check vs actual-pivot LDU.
#
# Use scalars (r=1) with deepest constants u0=A11(!=1), u1=deepBlkZ0, w0=A11_layer1, v1=deepBlkY1.
u0,u1,w0,v1 = sp.Rational(3), sp.Rational(1,2), sp.Rational(2), sp.Rational(1,3)
X0,Y0,Z0,T0 = sp.Rational(1,5),sp.Rational(1,7),sp.Rational(1,11),sp.Rational(1,13)  # layer0 deviation reads
X1,Y1,Z1,T1 = sp.Rational(1,17),sp.Rational(1,19),sp.Rational(1,23),sp.Rational(1,29) # layer1 deviation reads

def blk2(A,B,C,D): return sp.Matrix([[A,B],[C,D]])
# Full decode layers (deepest + deviation), reindexed:
L0 = blk2(u0+X0, 0+Y0, u1+Z0, 0+T0)     # layer0: deepBlkY=0
L1 = blk2(w0+X1, v1+Y1, 0+Z1, 0+T1)     # layer1: deepBlkZ=0
M  = L0*L1
# Score = unframed actual-pivot Schur of M  (DP=DQ=1, frames stripped):
Score = M[1,1] - M[1,0]*(M[0,0])**(-1)*M[0,1]

# --- the BARE absorbed-core tuple (what coreAbsorb actually produces) ---
# c_s = decode.core_s + schurCorrection_s = T_s + (-(readZ)(1+readX)^-1(readY))
# layer0: core read = T0 (the deepest core 0 + deviation T0); schurCorr uses readZ=Z0,readX=X0,readY=Y0
c0_bare = T0 + ( -(Z0)*(1+X0)**(-1)*(Y0) )
# layer1: core read = T1; schurCorr uses readZ=Z1,readX=X1,readY=Y1 (NOTE: bare uses the READS, not deepBlk)
c1_bare = T1 + ( -(Z1)*(1+X1)**(-1)*(Y1) )
prod_bare = c0_bare * c1_bare
print("BARE absorbed prod (c0_bare*c1_bare):", float(prod_bare), " vs Score:", float(Score),
      " EQUAL?", sp.simplify(prod_bare-Score)==0)

# --- the CLEANED tuple (sub-4 hc_eq): c''_0 = c0_bare ; c''_1 = (1-K)*S1 (actual-pivot last layer) ---
# l2S1 / l2K are the ACTUAL-pivot last-layer Schur + cross term (the W-clean). Reconstruct them:
# S1 actual = (T1) - (Z1)*(w0+X1)^-1*(v1+Y1)   [pivot w0+X1 = actual layer1 (1,1)]
S1_act = (0+T1) - (0+Z1)*(w0+X1)**(-1)*(v1+Y1)
# S0 actual = (T0) - (u1+Z0)*(u0+X0)^-1*(0+Y0)  [pivot u0+X0 = actual layer0 (1,1)]
S0_act = (0+T0) - (u1+Z0)*(u0+X0)**(-1)*(0+Y0)
K = (0+Z1)*((M[0,0]))**(-1)*(0+Y0)
# cleaned product per the LDU: S0c*(1-K)*S1c
prod_cleaned = S0_act*(1-K)*S1_act
print("CLEANED actual-pivot LDU (S0c*(1-K)*S1c):", float(prod_cleaned), " vs Score:", float(Score),
      " EQUAL?", sp.simplify(prod_cleaned-Score)==0)
print()
print("CONCLUSION:")
print("  bare absorbed prod = Score?  ", sp.simplify(prod_bare-Score)==0, "  (bare coreAbsorb's RAW output != Score)")
print("  cleaned actual-LDU = Score?  ", sp.simplify(prod_cleaned-Score)==0, "  (the W-clean RECONCILES it)")
print("  => the bare coreAbsorb's output must be RE-EXPRESSED (the (1-K)S1 cleaning, hWdet) into the")
print("     actual-pivot LDU to match Score. The cleaning IS the bare->actual bridge = hLDUtie content.")
