"""
(2,2,2,2) r=1 L=3 EXPLICIT split. 3 regular entries (E00,E01,E10), 1 core (E11).
Unit-pivot solve the 3 regular entries, substitute into E11, check it reduces to the
(1,1,1,1) chain (= a3 b3 c3, the three index>=1 diagonal core vars) times unit + regular cross.
"""
import sympy as sp
a0,a1,a2,a3=sp.symbols('a0 a1 a2 a3',real=True)
b0,b1,b2,b3=sp.symbols('b0 b1 b2 b3',real=True)
c0,c1,c2,c3=sp.symbols('c0 c1 c2 c3',real=True)
allv=[a0,a1,a2,a3,b0,b1,b2,b3,c0,c1,c2,c3]
E00=a0*b0*c0+a0*b0+a0*b1*c2+a0*c0+a0+a1*b2*c0+a1*b2+a1*b3*c2+b0*c0+b0+b1*c2+c0
E01=a0*b0*c1+a0*b1*c3+a0*c1+a1*b2*c1+a1*b3*c3+b0*c1+b1*c3+c1
E10=a2*b0*c0+a2*b0+a2*b1*c2+a2*c0+a2+a3*b2*c0+a3*b2+a3*b3*c2
E11=a2*b0*c1+a2*b1*c3+a2*c1+a3*b2*c1+a3*b3*c3

x0,x1,x2=sp.symbols('x0 x1 x2',real=True)
# pivots: from E00 -> linear term c0 + b0 + a0 (units). Take pivot c0? E00 has c0(1+a0+b0+a0 b0+...).
# Cleanest: the linear parts are: E00 ~ a0+b0+c0+..., E01 ~ c1+..., E10 ~ a2+...
# Pivot choices (unit-coefficient, triangular):
#  E10 -> a2 (coeff (1+b0)(1+c0)+... =1 at 0)   solve a2.
#  E01 -> c1 (coeff (1+a0)(1+b0)... ) solve c1.
#  E00 -> c0 (coeff 1+a0+b0+a0 b0 = (1+a0)(1+b0)) solve c0.
# core vars: a0,a1,a3,b0,b1,b2,b3,c2,c3 (9 vars) - but we only keep 12-3=9 core coords.
# E11 core target = a3 b3 c3 (the chain). Let's solve and substitute.
# Solve order: c0 (from E00), c1 (from E01), a2 (from E10). They are coupled; solve as linear system in (c0,c1,a2)?
# c0 appears in E00,E10,E11? E10 has c0; E11 has none of c0. a2 appears in E10,E11. c1 in E01,E11.
# E00 depends on c0 (and c1? E00 has no c1). E01 depends on c1 (and c0? E01 has c0 via a0 b0 c1? no, c0 not in E01).
# Actually E01 has 'a0 b0 c1' etc - c1 only. E00 has c0 only (no c1). E10 has c0, a2.
# Solve c0 from E00; then a2 from E10 (uses c0); c1 from E01.
c0_sol = sp.solve(sp.Eq(E00, x0), c0)[0]
E10b = E10.subs(c0, c0_sol)
a2_sol = sp.solve(sp.Eq(E10b, x2), a2)[0]
c1_sol = sp.solve(sp.Eq(E01, x1), c1)[0]
sub={c0:c0_sol, a2:a2_sol, c1:c1_sol}
# verify
print("E00 pullback - x0:", sp.simplify(E00.subs(sub)-x0))
print("E01 pullback - x1:", sp.simplify(E01.subs(sub)-x1))
print("E10 pullback - x2:", sp.simplify(E10.subs(sub)-x2))
E11_sub=sp.simplify(E11.subs(sub))
print("\nE11 (core) after substitution:")
print("  =", E11_sub)
E11_slice=sp.simplify(E11_sub.subs({x0:0,x1:0,x2:0}))
print("\nE11 on regular-zero slice {x=0}:")
print("  =", sp.factor(E11_slice))
# Is it unit * (a3 b3 c3)? factor and check
fac=sp.factor(E11_slice)
ratio=sp.simplify(E11_slice/(a3*b3*c3))
print("  E11_slice / (a3 b3 c3) =", sp.simplify(ratio))
print("  value at all core vars=0 (the unit at origin):", sp.simplify(ratio.subs({a0:0,a1:0,b0:0,b1:0,b2:0,c2:0,c3:0,b3:0})) if ratio.free_symbols else ratio)
