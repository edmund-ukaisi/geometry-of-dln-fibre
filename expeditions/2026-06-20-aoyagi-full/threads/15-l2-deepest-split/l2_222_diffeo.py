"""
VERIFY the explicit change of variables for (2,2,2) r=1 is a genuine local diffeo at 0,
and that F splits as x1^2+x2^2+x3^2 + (unit*a11*b11)^2 with the unit analytic, unit(0)=1.

The change Phi : (a00,a01,a10,a11,b00,b01,b10,b11) -> (x1,x2,x3, a00,a01,a11,b10,b11) where
  x1 = E00 = a00 + b00 + a00 b00 + a01 b10
  x2 = E01 = b01 + a00 b01 + a01 b11
  x3 = E10 = a10 + a10 b00 + a11 b10
i.e. we REPLACE the three pivot vars (b00, b01, a10) by (x1,x2,x3) and keep (a00,a01,a11,b10,b11).

Check: is Phi a local diffeo at 0? Jacobian of (x1,x2,x3,a00,a01,a11,b10,b11) wrt original 8.
"""
import sympy as sp

a00,a01,a10,a11,b00,b01,b10,b11 = sp.symbols('a00 a01 a10 a11 b00 b01 b10 b11', real=True)
orig = [a00,a01,a10,a11,b00,b01,b10,b11]
E00 = a00 + b00 + a00*b00 + a01*b10
E01 = b01 + a00*b01 + a01*b11
E10 = a10 + a10*b00 + a11*b10
E11 = a10*b01 + a11*b11

new_map = [E00, E01, E10, a00, a01, a11, b10, b11]   # 8 outputs
Jac = sp.Matrix([[sp.diff(f,v) for v in orig] for f in new_map])
Jac0 = Jac.subs({v:0 for v in orig})
print("Jacobian of the change at 0:")
sp.pprint(Jac0)
print("det at 0 =", Jac0.det())
print("=> local diffeo at 0:", Jac0.det()!=0)

# Now express the WHOLE loss in the new coords and confirm the split.
# We need to invert: solve b00,b01,a10 in terms of (x1,x2,x3, a00,a01,a11,b10,b11).
x1,x2,x3 = sp.symbols('x1 x2 x3', real=True)
# From E01: b01(1+a00) = x2 - a01 b11  => b01 = (x2 - a01 b11)/(1+a00)
b01_sol = (x2 - a01*b11)/(1+a00)
# From E00: b00(1+a00) = x1 - a00 - a01 b10 => b00 = (x1 - a00 - a01 b10)/(1+a00)
b00_sol = (x1 - a00 - a01*b10)/(1+a00)
# From E10: a10(1+b00) = x3 - a11 b10 => a10 = (x3 - a11 b10)/(1+b00)
a10_sol = (x3 - a11*b10)/(1+b00_sol)

sub = {b01:b01_sol, b00:b00_sol, a10:a10_sol}
# Verify E00,E01,E10 pull back to x1,x2,x3:
print("\nCheck pivots recover x's:")
print("  E00 ->", sp.simplify(E00.subs(sub)))
print("  E01 ->", sp.simplify(E01.subs(sub)))
print("  E10 ->", sp.simplify(E10.subs(sub)))

# The full loss F = E00^2+E01^2+E10^2+E11^2. After the change:
F = E00**2+E01**2+E10**2+E11**2
F_new = sp.simplify(F.subs(sub))
target = x1**2 + x2**2 + x3**2 + sp.simplify(E11.subs(sub))**2
print("\nF in new coords - (x1^2+x2^2+x3^2 + E11_new^2) =", sp.simplify(F_new - target))

# The core in new coords:
core_new = sp.simplify(E11.subs(sub))
print("\nCore E11 in new coords:")
print("  core =", core_new)
core_factored = sp.factor(core_new)
print("  factored =", core_factored)

# At x=0, core = unit * a11*b11 ?
core_at_x0 = sp.simplify(core_new.subs({x1:0,x2:0,x3:0}))
print("\nCore at x1=x2=x3=0:", core_at_x0, " = a11*b11 *", sp.simplify(core_at_x0/(a11*b11)))
unit = sp.simplify(core_at_x0/(a11*b11))
print("  unit at origin (all core vars 0):", unit.subs({a01:0,b10:0}))
