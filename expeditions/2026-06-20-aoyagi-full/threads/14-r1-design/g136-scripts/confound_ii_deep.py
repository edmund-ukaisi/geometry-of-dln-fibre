# CONFOUND (ii) HARDER: the dangerous spots for k_E >= 2.
# (a) Wider first factor: blow up {A1=0} for A1 a 3x3 (codim 9). Does core∘φ vanish to order EXACTLY 2?
# (b) The (x^2+y^2)^2 trap: could a stratum where TWO rank drops coincide give order-4 vanishing?
# (c) The terminal smooth block monomialized: the cone Σy_i^2 blown up -> order exactly 2?
import sympy as sp
u = sp.Symbol('u', positive=True)

def blowup_first_factor_order(widths):
    # A1 (widths[0] x widths[1]), blow up {A1=0}: A1 = u * Ahat (Ahat the chart vars, pivot=1).
    n,m = widths[0], widths[1]
    Ahat = sp.Matrix(n,m, lambda i,j: 1 if (i,j)==(0,0) else sp.Symbol(f'h{i}_{j}'))
    A1 = u*Ahat
    mats=[A1]
    for s in range(1,len(widths)-1):
        a,bb = widths[s], widths[s+1]
        mats.append(sp.Matrix(a,bb, lambda i,j: sp.Symbol(f'm{s}_{i}_{j}')))
    P=mats[0]
    for A in mats[1:]: P=P*A
    F=sp.expand(sum(P[i,j]**2 for i in range(P.shape[0]) for j in range(P.shape[1])))
    orders=[mm[0] for mm in sp.Poly(F,u).monoms()]
    return min(orders), sorted(set(orders))

for w in [[2,2,2],[3,3,3],[4,4,4],[3,2,4],[2,2,2,2],[4,3,2],[2,4,2]]:
    mn, allo = blowup_first_factor_order(w)
    print(f"chain {w}: blow up {{A1=0}} -> min u-order={mn} (k_E={mn//2}) all-orders={allo}")

print()
# (b) the (x^2+y^2)^2 trap: this arises if the RESOLVED function has a divisor along which the
# core is a SQUARE of a sum of squares. In the matrix chain, does the strict transform ever become
# (something)^2 along an exceptional? The residual ‖S B‖^2 after straighten is itself a sum of squares
# = NOT a perfect 4th power generically. Test the (2,2,2) step-2 residual order in its blow-up coord.
# step-2: residual block E^2+F0^2+(qE+δG)^2+(qF0+δH)^2 (the (2,2,2) resolvedForm), blow up {E=F0=δ=0}.
E,F0,delta,q,G,H = sp.symbols('E F0 delta q G H')
s = sp.Symbol('s', positive=True)
# blow up {E=F0=δ=0} codim 3, pivot E=s: E=s, F0=s*f, δ=s*d
f,d = sp.symbols('f d')
res = E**2 + F0**2 + (q*E+delta*G)**2 + (q*F0+delta*H)**2
res_sub = res.subs({E:s, F0:s*f, delta:s*d})
res_sub = sp.expand(res_sub)
orders=[mm[0] for mm in sp.Poly(res_sub, s).monoms()]
print(f"(2,2,2) step-2 residual, blow up {{E=F0=δ=0}} pivot E: min s-order={min(orders)} (k_E={min(orders)//2})")

# (c) terminal smooth block cone Σ y_i^2 (n=4) blown up at vertex: y_0=u, y_i=u z_i.
y = sp.symbols('y0 y1 y2 y3')
z = sp.symbols('z1 z2 z3')
cone = sum(yi**2 for yi in y)
cone_sub = cone.subs({y[0]:u, y[1]:u*z[0], y[2]:u*z[1], y[3]:u*z[2]})
orders=[mm[0] for mm in sp.Poly(sp.expand(cone_sub),u).monoms()]
print(f"terminal cone Σy² (n=4) blown up at vertex: min u-order={min(orders)} (k_E={min(orders)//2})")
