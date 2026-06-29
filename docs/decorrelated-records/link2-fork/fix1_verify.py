import sympy as sp
print("="*78)
print("EXACT VERIFY: which layer's Y and Z carry the M12/M21 core leak? (L=2, r=1)")
print("="*78)
# Product P = A0 * A1, block r|rest each.  A0 = [[Ap0, Y0],[Z0, T0]], A1 = [[Ap1, Y1],[Z1, T1]].
# (Ap = pivot+X, Y/Z off-diag, T core.)  At (2,2,2) r=1 all blocks are 1x1 scalars.
Ap0,Y0,Z0,T0, Ap1,Y1,Z1,T1 = sp.symbols('Ap0 Y0 Z0 T0 Ap1 Y1 Z1 T1', real=True)
A0 = sp.Matrix([[Ap0, Y0],[Z0, T0]])
A1 = sp.Matrix([[Ap1, Y1],[Z1, T1]])
P = A0*A1
P11,P12,P21 = P[0,0],P[0,1],P[1,0]
print("P12 =", sp.expand(P12), "  -> core T1 coeff:", sp.diff(P12,T1), "(= Y0, LAYER-0 Y read)")
print("P21 =", sp.expand(P21), "  -> core T0 coeff:", sp.diff(P21,T0), "(= Z1, LAYER-1=LAST Z read)")
print()
print("So the leak reads are:  Y0 = Y_FIRST (layer 0),   Z1 = Z_LAST (layer 1 = last).")
print()
print("ROUTING (regBoundaryToRegGauge, from the real def): reg half = { X_first, Y_LAST, Z_FIRST }.")
print("  => Y_first (=Y0) is NOT reg  => Y0 is a SPEC read.")
print("  => Z_last  (=Z1) is NOT reg  => Z1 is a SPEC read.")
print()
print("CONCLUSION: the core leak (Y0*T1, Z1*T0) couples to SPEC reads (Y_first, Z_last).")
print("  => at reg=0, spec=s!=0:  Y0=s_a, Z1=s_b NONZERO  => P12 ⊃ s_a*T1, P21 ⊃ s_b*T0 NONZERO.")
print("  => deepestEFull(0, c, s) DEPENDS on c when s!=0.   **FIX 1 FAILS.**")
print()
# Sanity: at reg=0, the REG reads (X_first, Y_last, Z_first) = 0.  For L=2: X_first=X0-component,
# Y_last=Y1, Z_first=Z0.  So at reg=0: Ap0 pivot (=1+X_first?) careful: X_first is the (0,0) X of layer0.
# At reg=0: X_first=0 => Ap0 = deepBlkA0 (pivot base, =1 at front-pivot).  Y_last=Y1=0, Z_first=Z0=0.
# But Y_first=Y0 and Z_last=Z1 are SPEC => can be != 0.
print("CHECK at reg=0 (X_first=0=>Ap0=1; Y_last=Y1=0; Z_first=Z0=0), spec free (Y0,Z1,X_last,...):")
sub_reg0 = {Y1:0, Z0:0, Ap0:1}   # reg reads zeroed; Ap0 pivot base 1 (front-pivot); spec Y0,Z1,Ap1,T0,T1 free
P12_r0 = sp.expand(P12.subs(sub_reg0)); P21_r0 = sp.expand(P21.subs(sub_reg0))
print("  P12|reg=0 =", P12_r0, " -> dP12/dT1 =", sp.diff(P12_r0,T1), "(= Y0 SPEC, NONZERO if spec!=0)")
print("  P21|reg=0 =", P21_r0, " -> dP21/dT0 =", sp.diff(P21_r0,T0), "(= Z1 SPEC, NONZERO if spec!=0)")
print()
print("=> deepestEFull(0,c,s) - deepestEFull(0,0,s) != 0 in general.  FIX 1 REFUTED by exact algebra.")
