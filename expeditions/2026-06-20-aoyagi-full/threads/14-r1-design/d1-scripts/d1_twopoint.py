import sympy as sp
# The genuine D1 question restated EXACTLY in Aoyagi's frame:
#   F = sum f_i^2 where the f_i are the HOMOGENEOUS generators of the core ideal
#       (the entries of prod(A) for the CORE, B=0).
#   Deepest point = ORIGIN (0,...,0) in the core coords.
#   Arbitrary fibre point v = a point in the zero-set {prod=0}.
#   Claim (Thm 2): lambda_origin(F) <= lambda_v(F).
#
# Aoyagi's f_i are homogeneous AS FUNCTIONS. The two points compared are the ORIGIN
# (all core coords 0) and an arbitrary w* on the zero-set. The proof blows up the LINE from
# origin to w*: w_i = t * w*_i (here t is the blow-up param). Homogeneity of f_i =>
#   f_i(t*w*) = t^{n_i} f_i(w*).
# So along that ray, sum f_i(t w*)^2 = sum t^{2n_i} f_i(w*)^2. For the RLCT at the ORIGIN vs at w*:
# the blow-up (w', t) |-> t*w' carries a nbhd of origin to a nbhd of the ray; the comparison
# sum t^{2n_i} f_i'^2 <= sum f_i'^2 (|t|<1) is Lemma1(1) at the SAME blown-up point. NO value used.
#
# Let me verify the CORE inequality is purely homogeneity (value-free) on (2,1,2):
a0,a1,b0,b1,t = sp.symbols('a0 a1 b0 b1 t', real=True)
# core generators (B=0): f_ij = a_i * b_j  (homogeneous: degree 1 in A-vars, degree 1 in B-vars,
#   total degree 2, ALL n_ij = 2 if we scale BOTH A and B by t; or treat as bi-homogeneous).
fs = [a0*b0, a0*b1, a1*b0, a1*b1]
# Aoyagi blow-up scaling ALL core vars by t (j = all 4 vars here, the fully-deep directions):
fs_scaled = [f.subs({a0:t*a0,a1:t*a1,b0:t*b0,b1:t*b1}) for f in fs]
print("scaled generators:", fs_scaled)
# degree n_i in t:
degs = [sp.Poly(g, t).degree() if g!=0 else None for g in fs_scaled]
print("t-degrees n_i:", degs, "(all =2, homogeneous degree 2 in the joint scaling)")
F  = sum(f**2 for f in fs)
Fs = sum(g**2 for g in fs_scaled)
print("sum t^{2n_i} f_i^2 - F  =", sp.factor(Fs - F))
# For |t|<1: Fs = t^4 * F <= F. Confirm:
print("Fs =", sp.factor(Fs), " = t^4 * F ; for |t|<1, Fs <= F. => Lemma1(1) gives lambda_0 <= lambda_w*.")
print()
print("KEY: the inequality sum t^{2n_i} f_i^2 <= sum f_i^2 is PURE HOMOGENEITY + |t|<1.")
print("     Nowhere is the VALUE of lambda (lambdaCore / min monomialThreshold) used.")
print("     The two-point comparison = (blow-up c-o-v = S1) o (Lemma1(1) = rlctAt_mono).")
