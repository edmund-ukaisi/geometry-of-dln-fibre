import sympy as sp
# Can the multi-radial polar divergence be transcribed to a SINGLE-axis monomial (Tonelli) atom?
# The multi-radial integral: ∫∫ s^{c1-1} a^{c2-1} (s^2+a^2)^{-c'} ds da (the (s,a) part), threshold 
# c'=(c1+c2)/2. The Lean atom needs a SINGLE axis u with exponent <= -1 and others FINITE (Tonelli).
#
# OPTION B-transcribe: a change of variables (s,a) -> (u, v) that makes it monomial.
# Standard resolution of (s^2+a^2): blow up the origin. Chart 1: s=u, a=u·v. Then s^2+a^2=u^2(1+v^2),
# ds da = u du dv (Jacobian u). 
u,v = sp.symbols('u v', positive=True)
c1,c2,cp = sp.symbols('c1 c2 cp', positive=True)
# s^{c1-1} a^{c2-1} (s^2+a^2)^{-cp} ds da  with s=u, a=uv:
# = u^{c1-1} (uv)^{c2-1} (u^2(1+v^2))^{-cp} · u du dv
# = u^{(c1-1)+(c2-1)-2cp+1} v^{c2-1} (1+v^2)^{-cp} du dv
# = u^{c1+c2-1-2cp} · [v^{c2-1}(1+v^2)^{-cp}] du dv
expo_u = c1 + c2 - 1 - 2*cp
print("After blow-up s=u, a=uv: integrand = u^{c1+c2-1-2c'} · v^{c2-1}(1+v^2)^{-c'} du dv")
print("  u-exponent =", expo_u, " = (c1+c2) - 1 - 2c' = minAdm - 1 - 2c'  (single axis!)")
print("  at c'=minAdm/2: u-exponent = -1. ∫_0^δ u^{-1} du = ⊤. SINGLE AXIS u. ✓✓✓")
print()
# The v-integral ∫_0^V v^{c2-1}(1+v^2)^{-c'} dv: finite (v^{c2-1} integrable at 0 since c2>=1; 
# (1+v^2)^{-c'} bounded). So it's a FINITE positive constant. The divergence is PURELY on u. ✓
# This is EXACTLY the Lean atom shape: monomialIntegrand with binding axis u (k=?, h=?).
# u^{minAdm-1-2c'} = u^h · (u^{2k})^{-c'} with h=minAdm-1, k=1. So (k,h)=(1, minAdm-1)! 
print("=> (k,h) on the binding axis u = (1, minAdm-1) = foldDivisors[minAdm]. EXACT match to the atlas leaf.")
print()
print("CONCLUSION: the blow-up s=u,a=uv (and iterating for K blocks) CONVERTS the multi-radial wedge")
print("into the SINGLE-axis monomial the Lean atom consumes. The binding axis carries (1, minAdm-1).")
print("The OTHER chart coords (v, the block shapes, the surviving generic params) give FINITE factors.")
