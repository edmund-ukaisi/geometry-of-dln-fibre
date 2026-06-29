import sympy as sp
# Does the BARE per-layer Schur (pivot 1+X) match the CONJUGATED (2,2)-Schur of the decode layer,
# AFTER the endpoint-frame transform?  This is the separability crux: bare coreAbsorb -> Score WITHOUT
# the shift ever being conjugated.
#
# A decode layer (reindexed, r+(.-r) split) is  L = [[dA+X, dY+Y],[dZ+Z, dT+T]]  (full block).
# Its (1,1)-Schur core (the conjCore the readback uses) = (dT+T) - (dZ+Z)(dA+X)^-1(dY+Y).
# The BARE absorbed core (coreAbsorb shift) is  (dT+T)_raw-coreslot... actually = core + schurCorrection
#   = (decode core T_s) + (-(Z)(1+X)^-1(Y)).
# These can only be EQUAL as the Schur core if the frame absorbs (dA,dZ,dY) -> the endpoint conjugation.
#
# KEY: at the deepest point the decode layer L = the deepest layer = [[u0,0],[u1,0]] (cols>=r killed for layer0).
# So dA=u0, dY=0, dZ=u1, dT=0.  The (1,1)-Schur of L at the deepest point:
u0,u1 = sp.symbols("u0 u1")  # dA=u0(=A11), dZ=u1(=Z0); dY=0,dT=0 (layer0)
T,X,Y,Z = sp.symbols("T X Y Z")  # the deviation core+gauge reads
L11 = u0 + X; L12 = 0 + Y; L21 = u1 + Z; L22 = 0 + T
conjSchur = L22 - L21*(L11)**(-1)*L12
print("CONJ (1,1)-Schur of decode layer (dA=u0,dZ=u1,dY=0,dT=0):")
print("   =", sp.expand(conjSchur))
# bare absorbed core = core(T) + schurCorrection = T + (-(Z)(1+X)^-1 Y)
bareAbs = T - Z*(1+X)**(-1)*Y
print("\nBARE absorbed core (T + schurCorrection, pivot 1+X):")
print("   =", sp.expand(bareAbs))
print("\nAre they equal?  conjSchur - bareAbs =", sp.simplify(conjSchur - bareAbs))
print("   (nonzero => the BARE absorbed core != conjSchur DIRECTLY; the frame transform must bridge them)")
print("\nAt the ORIGIN (X=Y=Z=T=0):")
print("   conjSchur(0) =", conjSchur.subs({X:0,Y:0,Z:0,T:0}), "  bareAbs(0) =", bareAbs.subs({X:0,Y:0,Z:0,T:0}))
print("   (both 0 at layer0 since dY=0; the deepest core is 0)")
