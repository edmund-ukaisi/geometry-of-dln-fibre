import sympy as sp
# (2,2,2) r=0. Core F = ||A1 A2||^2, A1,A2 in R^{2x2}. deepest = origin (A1=A2=0).
# lambda_deepest = lambdaCore(2,2,2) = 3/2 (the ground-truth ladder value).
#
# A non-deepest optimal point v: A1 = [[1,0],[0,0]] (rank 1), A2 = [[0,0],[0,1]] (rank 1), A1*A2=0.
# This is in the fibre but NOT all-layers-rank-0. Compute lambda_v by exact local analysis.
a = sp.symbols('a0:4', real=True)  # A1 perturbation entries
b = sp.symbols('b0:4', real=True)  # A2 perturbation entries
A1v = sp.Matrix([[1+a[0], a[1]],[a[2], a[3]]])
A2v = sp.Matrix([[b[0], b[1]],[b[2], 1+b[3]]])
P = sp.expand(A1v*A2v)
F = sp.expand(sum(P[i,j]**2 for i in range(2) for j in range(2)))
print("=== (2,2,2) r=0, non-deepest v (A1,A2 each rank1, product 0) ===")
for i in range(2):
    for j in range(2):
        print(f"  P_{i}{j} =", sp.expand(P[i,j]))
# Lowest-order (linear) part of each generator in the 8 local vars:
vars8 = list(a)+list(b)
print("\nLinear (leading) parts of generators:")
lin_parts = []
for i in range(2):
    for j in range(2):
        g = sp.expand(P[i,j])
        lin = sum(sp.diff(g,v).subs({vv:0 for vv in vars8})*v for v in vars8)
        lin_parts.append(lin)
        print(f"  lin P_{i}{j} =", lin)
# Count how many generators have NONZERO linear part (=> smooth directions => regular contribution)
nz_lin = [lp for lp in lin_parts if lp != 0]
print(f"\n# generators with nonzero linear part: {len(nz_lin)} of 4")
# The Jacobian rank of the generator map at v = # independent linear parts = codim of the smooth part.
J = sp.Matrix([[sp.diff(sp.expand(P[i,j]), v).subs({vv:0 for vv in vars8}) for v in vars8]
               for i in range(2) for j in range(2)])
print("Jacobian rank of (P_ij) at v:", J.rank(), " (=# nondegenerate quadratic directions in F)")
print()
print("INTERPRETATION: F = sum P_ij^2. The Jacobian-rank-many directions are NONDEGENERATE quadratics")
print("(smooth point in those dirs) => each contributes 1/2 to the local RLCT (regular). The RESIDUAL")
print("singular core at v is SMALLER than at the deepest origin (fewer fully-degenerate directions).")
print("=> lambda_v >= lambda_deepest. The deepest has the MOST degenerate (homogeneous) core.")
