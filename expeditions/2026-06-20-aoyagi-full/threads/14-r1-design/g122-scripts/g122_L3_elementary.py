import sympy as sp
# L=3 (2,2,2,2), v in S(1,0,0) (Jac rank 2, residual core non-empty). Can the (a)-split be done by
# an EXPLICIT gauge + linear change (elementary), or does it need the general constant-rank/IFT?
#
# The general constant-rank theorem solves q generators with INDEPENDENT linear parts for q variables.
# The ELEMENTARY version for this family: the q linear-leading generators are LINEAR forms in the
# perturbation; solving them = GAUSSIAN ELIMINATION (a finite, explicit linear-algebra operation),
# PROVIDED the higher-order terms don't obstruct. The constant-rank theorem's content beyond Gaussian
# elimination is handling the NONLINEAR coupling (the implicit function for the higher-order part).
#
# THE KEY: is the (a)-split for the chain family achievable by LINEAR Gaussian elimination on the
# linear parts + the chain structure, OR does the nonlinear coupling genuinely need the IFT?
w = sp.symbols('w0:12', real=True)
v1=sp.Matrix([[1,0],[0,0]]); v2=sp.Matrix([[0,0],[1,1]]); v3=sp.Matrix([[1,1],[1,1]])
C1=v1+sp.Matrix([[w[0],w[1]],[w[2],w[3]]]); C2=v2+sp.Matrix([[w[4],w[5]],[w[6],w[7]]]); C3=v3+sp.Matrix([[w[8],w[9]],[w[10],w[11]]])
P=sp.expand(C1*C2*C3)
g=[sp.expand(P[i,j]) for i in range(2) for j in range(2)]
allv=list(w)
# Linear parts: g0,g1 lin = 2w1+w4+w5 ; g2,g3 lin = 2w3.  Independent: 2.
# The q=2 regular generators: pick g0 (lin 2w1+w4+w5) and g2 (lin 2w3). Solve g0=0 for w4, g2=0 for w3.
# This solve: g0 = (2w1+w4+w5) + [higher order], solve w4 = -(2w1+w5) - [h.o.](w4,...). The higher-order
# terms CONTAIN w4 (nonlinearly) -- so it's NOT a pure linear solve; it's an implicit solve.
# BUT: w4 appears in g0's higher-order part. Is the solve still EXPLICIT (analytic, by the unit pivot)?
sol=sp.solve([g[0],g[2]],[w[4],w[3]],dict=True)
print("=== L=3 intermediate v: solving the 2 regular generators g0=0 (w4), g2=0 (w3) ===")
if sol:
    s=sol[0]
    for k,vv in s.items(): print(f"  {k} =", sp.simplify(vv))
    print()
    print("The solve SUCCEEDED explicitly (sympy solved it as rational functions = analytic near 0).")
    print("This is because the linear part has a UNIT pivot (coeff of w4 in g0 = 1, of w3 in g2 = 2),")
    print("so the implicit solve is by an ANALYTIC geometric series (unit denominator) -- ELEMENTARY")
    print("for THIS family (the generators are polynomial, the pivot coeff is a constant unit).")
else:
    print("  solve failed -- would need genuine IFT")
print()
print("=== Is this 'elementary' or does it need the general constant-rank theorem? ===")
print("The solve is: w4 = (linear) + (higher-order rational with unit denominator). This is the")
print("ANALYTIC IMPLICIT FUNCTION for a system whose linear part has a UNIT pivot. For POLYNOMIAL")
print("generators with a constant unit pivot coefficient, the implicit solution is an explicit power")
print("series (Lagrange inversion / unit-denominator rational). Mathlib HAS: analytic inverse function")
print("for unit-Jacobian analytic maps? Let me characterize what's actually needed.")
