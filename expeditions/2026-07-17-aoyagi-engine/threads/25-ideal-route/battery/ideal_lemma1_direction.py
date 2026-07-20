#!/usr/bin/env python3
"""
FIDELITY PIN: Lemma-1 direction (worked.tex:156).

worked.tex:153-156 states Aoyagi Lemma 1 as:
    G_1,...,G_m in J=<F_1,...,F_n>  =>  rlct(sum G^2) >= rlct(sum F^2).

The footnote justifies it by "pointwise domination sum G^2 <= c sum F^2 => integral
comparison". We test the DIRECTION exactly via a 1-D certificate with closed-form
zeta poles (rlct = the largest pole of int f^z, i.e. rlct(u^{2k}) = 1/(2k) with
trivial Jacobian h=0, matching the boxed S2 rule rlct=min (h+1)/(2k)).
"""
import sympy as sp

u, z = sp.symbols('u z', real=True)

def rlct_1d_monomial(power):
    # f = u^power (>=0 for even power near 0); zeta(z) = int_0^eps u^{power*z} du
    # converges iff power*z > -1 => pole at z = -1/power => rlct = 1/power.
    return sp.Rational(1, power)

# F = u  (ideal J = <u>);  G = u^2  (u^2 = u*u in <u>, so G in J).
F = u
G = u**2
print("F = u,  G = u^2,  and G in <F> since u^2 = u*u.")
# rlct of the SUM OF SQUARES (Aoyagi's convention rlct(J) = rlct(sum gen^2)):
rlct_F = rlct_1d_monomial(2)   # sum F^2 = u^2
rlct_G = rlct_1d_monomial(4)   # sum G^2 = u^4
print(f"  rlct(sum F^2) = rlct(u^2) = {rlct_F}")
print(f"  rlct(sum G^2) = rlct(u^4) = {rlct_G}")
print(f"  G in <F> gives rlct(G^2) {'>=' if rlct_G>=rlct_F else '<'} rlct(F^2): "
      f"{rlct_G} vs {rlct_F}")
print()
print("VERDICT:")
print(f"  rlct(sum G^2) = 1/4  <  1/2 = rlct(sum F^2).")
print("  So G in J gives rlct(sum G^2) <= rlct(sum F^2), NOT >=.")
print("  worked.tex:156 states >=; the CORRECT direction is <= (Lean rlctAt_mono).")
print()
print("  Three independent derivations of <= :")
print("   (i)  ideal inclusion I=<G> subset J=<F> => lct(I) <= lct(J)   (lct monotone in ideal);")
print("   (ii) K_G = sum G^2 <= c*K_F pointwise => {K_F<t/c} subset {K_G<t}")
print("        => V_G(t) >= V_F(t/c) ~ t^{lct_F} => lct_G <= lct_F;")
print("   (iii) boxed S2 rule: faster-vanishing K has smaller (h+1)/(2k).")
print()
print("  For the EQUALITY use (<prod C> = <b_i>, BOTH inclusions), the direction is")
print("  harmless: both <= applied give equality. But the one-sided Lemma-1 print is")
print("  BACKWARDS and should read rlct(G^2) <= rlct(F^2).")

# double-check the "pointwise domination" the footnote cites is itself correct:
c = sp.symbols('c', positive=True)
print()
print("  Footnote's premise 'sum G^2 <= c sum F^2' IS correct here: u^4 <= c*u^2 near 0")
print("  (take c=1, |u|<=1: u^4 = u^2*u^2 <= u^2). The premise is right; the")
print("  RLCT direction it is then plugged into is inverted.")
