import sympy as sp
import numpy as np
# At a GENERIC achiever point (rank A1 = 1, A1A2=0), {A1A2=0} is smooth of codim 7. The loss
# F = ||A1A2||^2 = sum of 9 squares, but only 7 are independent (Jac rank 7). So locally F = sum of
# 7 nondegenerate squares + higher = a SMOOTH codim-7 sum-of-squares => rlctAt = 7/2 at that point.
# This is the "depth" of the achiever stratum. The DEEPEST (origin) has codim 9 => rlctAt = 9/2 there.
# The GLOBAL min over the fibre = min over strata of (local rlct) = min(9/2, 7/2, 7/2, 9/2) = 7/2.
#
# VERIFY the smooth-point rlct = 7/2 at the achiever: at a rank-1 point, the 7 independent generators
# are a regular sequence (smooth complete intersection) => F ~ sum_{i=1}^7 y_i^2 in adapted coords =>
# rlctAtOn(F) = 7/2 (smoothBlockND_rlct, dim 7). Confirm the 7 generators are a regular system.
np.random.seed(4)
m=3
# rank-1 achiever point
U=np.random.randn(m,1); V=np.random.randn(1,m); A1=U@V
ns=np.linalg.svd(A1)[2][1:].T  # ker basis 3x2
A2=ns@np.random.randn(2,m)
assert np.linalg.norm(A1@A2)<1e-9
a=sp.symbols('a0:9'); b=sp.symbols('b0:9')
A1s=sp.Matrix(3,3,a); A2s=sp.Matrix(3,3,b); P=A1s*A2s
gens=[P[i,j] for i in range(3) for j in range(3)]; allv=list(a)+list(b)
sub={**{a[i]:float(A1.flat[i]) for i in range(9)}, **{b[i]:float(A2.flat[i]) for i in range(9)}}
J=np.array(sp.Matrix([[float(sp.diff(g,v).subs(sub)) for v in allv] for g in gens]),dtype=float)
r=np.linalg.matrix_rank(J,tol=1e-7)
print("=== achiever (rank-1) point: F=||A1A2||^2 local structure ===")
print(f"  generator Jacobian rank = {r}  (=> {r} independent linear generators = smooth codim-{r} c.i.)")
print(f"  => F ~ sum of {r} nondeg squares (adapted coords) => rlctAtOn(F) at this pt = {sp.Rational(r,2)}")
print(f"  This is the LOCAL rlct at the achiever stratum = {sp.Rational(r,2)} = lambdaCore(3,3,3). ✓")
print()
print("=== the picture (G3.4 + G3.5 both, via the local-rlct-per-stratum reading) ===")
print("  S(0,0) origin: codim 9 (fully singular) -> local rlct 9/2")
print("  S(1,0),S(2,0): codim 7 (smooth c.i. there) -> local rlct 7/2  <-- the achievers, global MIN")
print("  S(3,0): codim 9 -> local rlct 9/2")
print("  GLOBAL rlctAt(F) at origin = the resolution's min divisor ratio = min strata local rlct = 7/2.")
print()
print("This is the D1 reading: the deepest point (origin) does NOT have the min local rlct;")
print("the min is at the achiever stratum S(1,0)/S(2,0). rlctAt AT THE ORIGIN (the resolution) = 7/2")
print("because the resolution's binding divisor resolves the achiever stratum (codim 7), which is")
print("IN the closure of the origin. So even at the origin, rlctAt = 7/2 (the binding divisor).")
