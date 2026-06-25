"""
Q1 — Test the `hnode` Schur-form claim on the (2,2,2,2) rank-1 peel (L=3).

hnode (from GeneralR1Recursion.lean:620-623) asserts that near the deepest point,
after a measure-preserving det-1 GL-straightening + blow-up, the per-node core is

    flatCore w = (sum_j w.1 j^2)  +  sum_{i,j} (bcol_i * w.1_j + SΓ_{i,j})^2
    G(w.2)^2   = sum_{i,j} SΓ_{i,j}^2
    sum_i bcol_i^2 <= T^2

The load-bearing structure: the cross term is `bcol_i * w.1_j`, a RANK-1 outer
product (pivot column ⊗ pivot row). w.1 = the nReg regular coords (= Erow, the
pivot-row product); bcol = the pivot column.

We work the (2,2,2,2) chain, rank-1 layer-1 peel t=(1,0,0), Mval=3.
This is the CLEAN/corank-≤1 case where the squeeze form is EXPECTED to hold.
Following verify-r1-shortcut.md: layer-1 incidence + one blow-up gives
    F = α²ρ²·‖X·C³‖²    (a fresh (2,2,2) core)
We check whether the residual, after the regular coords are split off, lands in
the hnode Schur form.
"""
import sympy as sp

# Free variables for the (2,2,2,2) chain after the layer-1 incidence chart.
# Following /tmp/r1_L3_chain.py structure from verify-r1-shortcut.md:
#   A = α[[1,a],[b,ab+δ]]   (layer 1, incidence chart, α the radial)
#   B = [[u-ar, v-as],[r,s]] (layer 2)
#   C = C³ free 2x2 (layer 3)
# blow up {δ=u=v=0}: δ=ρ, u=ρξ, v=ρη
al, a, b, delta = sp.symbols('alpha a b delta', real=True)
u, v, r, s = sp.symbols('u v r s', real=True)
rho, xi, eta = sp.symbols('rho xi eta', real=True)
c11,c12,c21,c22 = sp.symbols('c11 c12 c21 c22', real=True)

A = al*sp.Matrix([[1, a],[b, a*b+delta]])
B = sp.Matrix([[u-a*r, v-a*s],[r, s]])
C3 = sp.Matrix([[c11,c12],[c21,c22]])

# The core product C¹C²C³ (here A·B·C3) ; F = ‖A·B·C3‖²
P = A*B*C3
F = sum(P[i,j]**2 for i in range(2) for j in range(2))

# blow up {δ=u=v=0} in δ-chart: δ=ρ, u=ρξ, v=ρη
sub = {delta: rho, u: rho*xi, v: rho*eta}
Fb = sp.expand(F.subs(sub))

# Factor out α²ρ²
Fb_over = sp.simplify(Fb / (al**2 * rho**2))
print("=== (2,2,2,2) rank-1 peel, t=(1,0,0) ===")
print("F / (α²ρ²) =")
Fb_over_s = sp.expand(Fb_over)
print(Fb_over_s)
print()

# The residual U from the doc: U = ‖[[ξ,η],[bξ+r, bη+s]]·C3‖²
X = sp.Matrix([[xi, eta],[b*xi+r, b*eta+s]])
U = sum((X*C3)[i,j]**2 for i in range(2) for j in range(2))
print("doc residual U = ‖[[ξ,η],[bξ+r,bη+s]]·C3‖² matches F/(α²ρ²)? :",
      sp.simplify(Fb_over_s - sp.expand(U)) == 0)
print()

# Now the question: U = ‖[[1,0],[b,1]]·[[ξ,η],[r,s]]·C3‖².  Order at deepest point.
print("U order check (substitute all free vars -> t·(random dir), find leading order):")
import random
random.seed(1)
freev = [b, xi, eta, r, s, c11, c12, c21, c22]
t = sp.symbols('t', positive=True)
dirs = {x: sp.Integer(random.randint(-3,3)) for x in freev}
Ut = sp.expand(U.subs({x: dirs[x]*t for x in freev}))
poly = sp.Poly(Ut, t)
print("  leading order in t along random ray:", poly.monoms()[-1][0] if poly.monoms() else "0",
      " (doc says order 4 => NOT a unit, U vanishes at deepest pt)")
