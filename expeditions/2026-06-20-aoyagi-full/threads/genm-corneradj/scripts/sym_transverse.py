import sympy as sp

print("=== Exact transverse normal form of det(B B^T) near {rank B < b} ===\n")

# ---- Test case: b=2, rho=3.  B = 2x3, rows r1, r2 in R^3.
# Rank-1 locus = {r2 parallel r1}.  Fix r1 generic; parametrize r2 = t*r1 + z (z transverse).
r1 = sp.Matrix(sp.symbols('p0 p1 p2', real=True))      # generic fixed row 1
t  = sp.symbols('t', real=True)
# transverse displacement z lives in orthogonal complement of r1 (2-dim). Build orthonormal-ish basis.
# Use two explicit vectors orthogonal to a *specific* generic r1 to keep it exact & simple:
r1v = sp.Matrix([1,0,0])
z1,z2 = sp.symbols('z1 z2', real=True)
u1 = sp.Matrix([0,1,0]); u2 = sp.Matrix([0,0,1])        # basis of r1^perp
r2 = t*r1v + z1*u1 + z2*u2
B = sp.Matrix.hstack(r1v, r2).T                          # 2x3
G = B*B.T
detG = sp.simplify(G.det())
print("b=2,rho=3, r1=e1:  det(B B^T) =", detG, "  => |z|^2 exactly (z in R^2), codim 2")
assert sp.simplify(detG - (z1**2 + z2**2)) == 0
print("  CONFIRMED det = z1^2+z2^2  (vanishing order 2 transverse, transverse dim = 2 = rho-b+1)\n")

# general generic r1 (not axis-aligned): det should be |r1|^2 * |z_perp|^2 form
# quick numeric-exact check with r1=(2,-1,3)
r1g = sp.Matrix([2,-1,3])
# basis of r1g^perp
import sympy
perp = r1g.T.nullspace()  # returns basis of {x : r1g.x=0}
w1,w2 = perp[0], perp[1]
za,zb = sp.symbols('za zb', real=True)
r2g = t*r1g + za*w1 + zb*w2
Bg = sp.Matrix.hstack(r1g, r2g).T
detGg = sp.expand(sp.simplify((Bg*Bg.T).det()))
print("generic r1=(2,-1,3): det(B B^T) =", sp.factor(detGg))
print("  (t drops out -> vanishes exactly on rank-1 locus; quadratic in (za,zb) => order 2)\n")

# ---- Confirm codim for b=2,rho=4 (interior test) : transverse dim should be rho-b+1 = 3
print("=== codim of {rank<b} for b x rho ===")
for (b,rho) in [(1,1),(1,2),(2,2),(2,3),(2,4),(3,5)]:
    codim = (b-(b-1))*(rho-(b-1))   # = rho-b+1
    print(f"  b={b} rho={rho}: codim{{rank<b}} = rho-b+1 = {codim}")

print("\n=== Threshold (radial criterion) ===")
print("  transverse: det(Gram)^{-a/2} ~ |z|^{-a},  z in R^{rho-b+1}")
print("  int_{R^d} |z|^{-a} dz near 0 converges iff a < d = rho-b+1")
print("  => converge iff a <= rho-b (integers) iff a+b <= rho")
print("  boundary a = rho-b+1 (rho=a+b-1): |z|^{-d} over R^d = r^{-1} dr => LOG-DIVERGE")
for (a,b,rho) in [(2,2,3),(2,2,4),(2,3,3),(1,1,1),(1,1,2)]:
    d = rho-b+1
    verdict = "CONVERGE" if a < d else ("LOG-DIV (endpoint)" if a==d else "POWER-DIV")
    print(f"  a={a} b={b} rho={rho}: transverse dim d={d}, a vs d -> {verdict}   (a+b={a+b}, rho={rho})")
