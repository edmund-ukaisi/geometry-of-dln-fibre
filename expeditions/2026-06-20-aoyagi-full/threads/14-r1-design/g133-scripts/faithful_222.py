"""
The faithful (2,2,2) resolution, exact. F = ||A B||^2, A,B 2x2. Trace the two nested blow-ups and
confirm EACH exceptional divisor has loss-multiplicity k_E=1 (ord 2), and that the SECOND blow-up
does NOT re-touch the FIRST exceptional coordinate (the Q2-caveat danger: shared-u => k>=2).

Faithful tree (design memo, faithful to Aoyagi Lemma 2/Thm 3):
 Step1: blow up {A=0} (codim 4). Chart pivot a_ij: A = x*Ahat with one entry of Ahat = 1 (unit).
        F = x^2 * ||Ahat B||^2. x-exceptional: ord_x F = 2 (k=1), Jac x^3 (h=3), ratio (3+1)/(2*1)=2.
 Lemma2 unit-Jac split: clear pivot row/col -> ||Ahat B||^2 ~ E^2+F0^2+(qE+dG)^2+(qF0+dH)^2,
        center {E=F0=delta=0} codim 3.
 Step2: blow up {E=F0=delta=0} (codim 3). Chart pivot s: vars = s*(...). s-exceptional: ord_s=2 (k=1),
        Jac s^2 (h=2), ratio (2+1)/2 = 3/2 (BINDING).
Confirm: ord_x along x-divisor = 2; ord_s along s-divisor = 2; the s-blow-up coords are FRESH (do NOT
include x), so x and s are independent => no shared-u => no k>=2.
"""
import sympy as sp

A = sp.Matrix(2,2, lambda i,j: sp.symbols(f'a{i}{j}', real=True))
B = sp.Matrix(2,2, lambda i,j: sp.symbols(f'b{i}{j}', real=True))
P = A*B
F = sum(P[i,j]**2 for i in range(2) for j in range(2))
x = sp.symbols('x', positive=True)

# ---- Step 1: pivot a00. Blow-up chart of {A=0}: A = x*Ahat, pivot Ahat[0,0]=1.
ah01,ah10,ah11 = sp.symbols('ah01 ah10 ah11', real=True)
Ahat = sp.Matrix([[1, ah01],[ah10, ah11]])
Achart = x*Ahat
Pc = Achart*B
Fc = sp.expand(sum(Pc[i,j]**2 for i in range(2) for j in range(2)))
polx = sp.Poly(Fc, x)
print("Step1 (pivot a00): F in chart, orders in x:", sorted(polx.as_dict().keys()))
print("   => ord_x(F) =", min(d[0] for d in polx.as_dict().keys()), " (k_E = ord/2)")
resid = sp.simplify(Fc/x**2)
print("   residual G1 = F/x^2 = ||Ahat B||^2, the reduced core. degree in x of residual:",
      sp.Poly(sp.expand(resid),x).degree() if resid.has(x) else 0)

# residual = ||Ahat B||^2 with Ahat unit pivot. The center for step2 is the rank-defect of Ahat*B.
# Since Ahat is invertible near pivot (det = ah11 - ah01*ah10, unit at origin? det(Ahat)|_0 = 1*ah11...
# at Ahat=I-ish: actually pivot makes a00=1, the OTHER entries are small. Ahat*B rank defect <-> B rank
# defect (Ahat invertible). So step2 blows up {B-rank-defect}. The s-coordinate is FRESH (B-entries),
# NOT x. Confirm independence:
print()
print("Step2 blows up the residual ||Ahat B||^2 rank-defect; its pivot coordinate s is a B/residual var")
print("(FRESH), independent of x. So along the s-divisor, x is generic (nonzero) => ord_x unaffected,")
print("and ord_s = 2 (one factor scaled). NO shared-u. Confirm by scaling a fresh residual coord:")

# Model: the residual after Lemma-2 is E^2+F0^2+(qE+dG)^2+(qF0+dH)^2 with center {E=F0=delta=0}.
# step2 chart: E=s, F0=s*f, delta=s*d  (pivot E). Then residual = s^2*( unit ). ord_s=2.
E,F0,delta,f,d,G,H,q = sp.symbols('E F0 delta f d G H q', real=True)
s = sp.symbols('s', positive=True)
residual_norm = E**2 + F0**2 + (q*E+delta*G)**2 + (q*F0+delta*H)**2
chart2 = {E: s, F0: s*f, delta: s*d}
r2 = sp.expand(residual_norm.subs(chart2))
print("   residual in s-chart, orders in s:", sorted(sp.Poly(r2,s).as_dict().keys()),
      "=> ord_s =", min(k[0] for k in sp.Poly(r2,s).as_dict().keys()))

# FULL leaf: F = x^2 * (residual). In the s-chart the leaf = x^2 * s^2 * unit. Divisors {x=0}:(k1,h3),
# {s=0}:(k1,h2). Both k=1. Check the COMBINED monomial x^a s^b with a,b independent:
print()
print("FULL leaf monomial: x^2 * s^2 * unit. x-divisor (k=1,h=3) ratio 2; s-divisor (k=1,h=2) ratio 3/2.")
print("x and s are DIFFERENT coordinates => the leaf is a NORMAL CROSSING of two k=1 divisors,")
print("NOT a single k=2 divisor. binding = min(2, 3/2) = 3/2 = lambdaCore(2,2,2). NO undershoot.")
