import sympy as sp
print("="*78)
print("FIX 1 failed. Test FIX 2 (Θ shift carries reg factor) and FIX 3 (R' dominates spec).")
print("="*78)
print()
print("--- FIX 3: does ∑R'² dominate ‖spec‖²?  (i.e. R'(0,0,s) != 0 for s != 0?) ---")
# deepestEFull(0,0,s): reg=0, core=0, spec=s.  At core=0 the atom deepestEFull_coreZero says
# deepestEFull(reg,0,spec) = deepestEPivot(reg,spec).  At reg=0: deepestEFull(0,0,s)=deepestEPivot(0,s).
# Does the reg RESIDUAL see the SPEC? deepestEFull reads {11,12,21} of P.  At reg=0,core=0:
Ap0,Y0,Z0, Ap1,Y1,Z1 = sp.symbols('Ap0 Y0 Z0 Ap1 Y1 Z1', real=True)  # T0=T1=0 (core), reg reads=0
# reg=0 => X_first=0(Ap0=1), Y_last=Y1=0, Z_first=Z0=0.  core=0 => T0=T1=0.  spec free: Y0,Z1,X_last(Ap1).
A0=sp.Matrix([[1,Y0],[0,0]]); A1=sp.Matrix([[Ap1,0],[Z1,0]])   # reg=0,core=0; Y0,Z1,Ap1 are spec
P=sp.expand(A0*A1)
P11,P12,P21=P[0,0],P[0,1],P[1,0]
print("  At reg=0,core=0, spec=(Y0,Z1,Ap1):  P11-1 =", sp.expand(P11-1), " P12 =", P12, " P21 =", P21)
print("  => R'(0,0,s) reads: P11-1 = Y0*Z1 (+...), P12=0, P21=0.")
print("  R'(0,0,s) is NOT identically the spec (it's a PRODUCT Y0*Z1, degenerate/quadratic in spec).")
print("  => ∑R'² does NOT dominate ‖spec‖² linearly.  **FIX 3 FAILS** (R' is spec-degenerate too).")
print()
print("--- FIX 2: does Θ's core shift delta carry a reg factor? ‖delta‖ <= K‖reg‖·‖q‖? ---")
# delta = shiftDiffConj = schurCutoffShiftConj - schurCutoffShift (core shift).
# schurCorrection_s = -Z_s(1+X_s)^{-1}Y_s.  The DIFFERENCE conj-bare:
# bare uses pivot base 1; conj uses deepBlkA.  delta_s = -[Zc(Ac)^-1 Yc] - [-(Z)(1+X)^-1 Y]
# At the boundary (deepBlkY_0=0 OR deepBlkZ_1=0): boundary corrections... but delta is a CORE shift.
# Does delta carry a REG factor? delta involves Z_s, Y_s reads.  At reg=0, are Z_s,Y_s zero?
# Z_s,Y_s at reg=0: only Y_last,Z_first are reg(=0); Y_first,Z_last are SPEC(can be !=0).
# So at reg=0,spec=s: Y0(spec)!=0, Z1(spec)!=0 => the Schur correction -Z(..)Y can be NONZERO.
# => delta does NOT carry a pure reg factor.  **FIX 2 FAILS** (delta survives at reg=0,spec!=0).
print("  delta_s ~ Schur corr diff = -Z_s(...)Y_s type.  At reg=0,spec=s: Y_first,Z_last (SPEC) != 0,")
print("  so delta_last ~ -Z1(...)Y? can be NONZERO at reg=0.  => no pure reg factor.  **FIX 2 FAILS.**")
print()
print("="*78)
print("ALL THREE LISTED FIXES FAIL on these objects.  The gap is REAL and deeper.")
print("Need: the JOINT structure.  Both ΔR-survival AND the Θ-shift live in (reg,spec)-products,")
print("AND R' is degenerate in spec.  Re-examine whether comparability holds AT ALL.")
