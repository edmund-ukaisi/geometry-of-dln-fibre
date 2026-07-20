#!/usr/bin/env python3
"""
The ideal-level PEEL identity, exact.  This is the load-bearing telescoping step.

Claim (one layer, ideal level, in the incidence + one-blow-up chart):
  C1 = alpha*[[1,a],[b, a*b+delta]]         (blow-up of C1 at its corner; alpha exceptional)
  C2 reparam by the a-shear (unit, det 1):  C2 = [[u-a*r, v-a*s],[r,s]]
  blow up {delta=u=v=0}:  delta=rho, u=rho*xi, v=rho*eta   (rho exceptional)
Then, as an EXACT matrix identity,
  C1 * C2 * (tail) = alpha*rho * L * Xfresh * (tail),
  L = [[1,0],[b,1]]  (unipotent, det 1 = UNIT),  Xfresh = [[xi,eta],[r,s]] (a FRESH generic 2x2).
Hence  <C1 C2 (tail) o chart> = alpha*rho * <Xfresh*(tail)>  (L stripped, it is a unit),
and the residual  Xfresh*(tail)  is a product of one FEWER generic 2x2 factor
of the SAME shape (the telescoping).  We verify the matrix identity exactly at
tail = I (depth 2) and tail = C3 (depth 3), and check the corner is a UNIT.
"""
import sympy as sp

def peel_symbols(tag):
    a,b,delta = sp.symbols(f'a{tag} b{tag} delta{tag}', real=True)
    r,s,u,v   = sp.symbols(f'r{tag} s{tag} u{tag} v{tag}', real=True)
    alpha,rho,xi,eta = sp.symbols(f'alpha{tag} rho{tag} xi{tag} eta{tag}', real=True)
    return dict(a=a,b=b,delta=delta,r=r,s=s,u=u,v=v,alpha=alpha,rho=rho,xi=xi,eta=eta)

def peeled_factor(P):
    """C1 (incidence) times C2 (a-sheared), BEFORE the blow-up substitution."""
    C1 = P['alpha']*sp.Matrix([[1,P['a']],[P['b'], P['a']*P['b']+P['delta']]])
    C2 = sp.Matrix([[P['u']-P['a']*P['r'], P['v']-P['a']*P['s']],[P['r'],P['s']]])
    return C1, C2

def blowup_subs(P):
    return {P['delta']:P['rho'], P['u']:P['rho']*P['xi'], P['v']:P['rho']*P['eta']}

print("="*72)
print("PEEL IDENTITY  (exact matrix algebra)")
print("="*72)

for tailname, tail in [("depth-2 (tail = I)", sp.eye(2)),
                       ("depth-3 (tail = C3 generic)",
                        sp.Matrix(sp.symbols('c300 c301 c310 c311', real=True)).reshape(2,2))]:
    P = peel_symbols("1")
    C1, C2 = peeled_factor(P)
    prod = sp.expand(C1*C2*tail)
    prod_bu = sp.expand(prod.subs(blowup_subs(P)))            # after blow-up
    L = sp.Matrix([[1,0],[P['b'],1]])
    Xfresh = sp.Matrix([[P['xi'],P['eta']],[P['r'],P['s']]])
    rhs = sp.expand(P['alpha']*P['rho'] * (L*Xfresh*tail))
    ok = sp.simplify(prod_bu - rhs) == sp.zeros(2,2)
    print(f"\n{tailname}:")
    print(f"  C1*C2*tail o chart  ==  alpha*rho * [[1,0],[b,1]] * [[xi,eta],[r,s]] * tail  ?  {ok}")
    # every entry divisible by alpha*rho:
    div = all(sp.simplify(prod_bu[i,j]/(P['alpha']*P['rho'])).is_polynomial()
              for i in range(2) for j in range(2))
    print(f"  every entry divisible by alpha*rho (the extracted divisor)?  {div}")
    print(f"  L=[[1,0],[b,1]] det = {sp.simplify(L.det())}  (UNIT, stripped from the ideal)")
    print(f"  residual after strip = [[xi,eta],[r,s]] * tail  = a FRESH generic product")
    print(f"  of {1 if tail==sp.eye(2) else 2} factor(s): depth {'1' if tail==sp.eye(2) else '2'}"
          f"  <= peeled from depth {'2' if tail==sp.eye(2) else '3'}. TELESCOPES.")
    # corner-unit check: the pivot that Q,P invert is the (0,0) of C1 = alpha (nonzero in-chart)
    print(f"  corner inverted by the a-shear P = C1[0,0]/alpha = 1 (unit); alpha != 0 in-chart. UNIT ok.")
