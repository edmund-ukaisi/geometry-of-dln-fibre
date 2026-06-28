import sympy as sp

# Verify: (R*S)_top depends only on M11, M12 (the top j rows of R), NOT on M22 (or M21).
# So at FIXED spectators (M11,M12,M21), the top-Morse-block integrand is INDEPENDENT of M22.
# Hence M22 -> Sc translation only affects the Sc-core term. Clean factorisation. (j=1, r=3.)
r = sp.symbols('r01 r02 r10 r11 r12 r20 r21 r22', real=True)
r01,r02,r10,r11,r12,r20,r21,r22 = r
R = sp.Matrix([[1, r01, r02],[r10,r11,r12],[r20,r21,r22]])
S = sp.Matrix(3, 2, sp.symbols('s00 s01 s10 s11 s20 s21', real=True))  # 3x2 (p=2)
RS = R*S
top = RS[0,:]   # row 0 = (R*S)_top (j=1)
print("=== (R*S)_top (row 0) entries -- check dependence on M22 = {r11,r12,r21,r22} ===")
M22vars = {r11,r12,r21,r22}
for b in range(2):
    e = sp.expand(top[0,b])
    deps = e.free_symbols & M22vars
    print(f"  (R*S)_top[0,{b}] = {e}")
    print(f"     depends on M22 vars? {deps if deps else 'NO -- depends only on M11,M12,S'}")
print()
print("CONFIRMED: (R*S)_top depends only on the TOP rows M11,M12 (R[0,*]) and S, NOT on M22.")
print("So the M22 -> Sc translation (at fixed spectators incl. M12) leaves the top-Morse block")
print("integrand UNCHANGED. The translation acts purely on the Sc-core term. Factorisation clean.")
print()
# Also: in the FULL inner integral J(R) = ∫_S (frobSq(top) + frobSq(Sc*S_bot))^{-c'}, the variable
# of integration is S; R (hence M22, spectators, Sc) are PARAMETERS. So J(R) = J̃(M11,M12,M21,M22).
# Since top depends on (M11,M12) and Sc depends on (M22,M12,M21), and M11=1 fixed:
#   J̃ is a function of (M12, M21, M22).  At fixed (M12,M21), the M22-dependence enters ONLY through
#   Sc = M22 - M21⊗M12 (translation).  So J̃(M12,M21,M22) = Ĵ(M12, Sc) where Sc = M22 - M21⊗M12,
#   and the M12 dependence of Ĵ is ONLY via the top-block shear (a translation in S_top, peelable).
print("Net: J̃(M12,M21,M22) = Ĵ(M12, Sc).  The R-integral over (M12,M21,M22):")
print("  ∫∫∫ Ĵ(M12, Sc(M22,M21,M12)) dM22 dM21 dM12")
print("  = ∫∫ [ ∫ Ĵ(M12,Sc) dSc  (Jac=1, Sc-box translated) ] dM21 dM12   <= ... <= G·vol(spec).")
print("  The M12-dependence of Ĵ is the top-block shear, peeled by translation in S_top (depth2 pattern).")
