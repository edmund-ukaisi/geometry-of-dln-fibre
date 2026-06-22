import sympy as sp
# ADVERSARIAL on (a2): can the atlas inf UNDERSHOOT lambdaCore?
# The undershoot danger: a root-to-leaf path whose leaf monomialThreshold < ½·min_t Mval.
# Since the per-divisor ratio is (h_E+1)/(2k_E) with k_E=1 (mult 1, structural) and h_E = |center|-1,
# the ratio = |center|/2 = (codim of that center)/2. The leaf threshold = ⨅ over the path's divisors of
# these ratios = ½·(min codim along the path). So the atlas inf = ½·min over ALL paths of min-codim-along-path
# = ½·(min codim over all centers in the tree). The MINIMUM codim center = the top-dimensional stratum =
# min_t Mval. So atlas inf = ½·min_t Mval EXACTLY — no undershoot IF k_E=1 everywhere (mult control).
#
# The ONLY way to undershoot: a center with k_E ≥ 2 (F vanishing to order ≥4 in the pivot), giving ratio
# < codim/2. Test: in the recursion F = x²·(reduced), is the pivot ALWAYS exactly order 2 (k=1)?
# The pivot x normalizes a SINGLE matrix entry to 1 (the hard pivot), and F = ‖A1·A2‖² with A1 = x·Â.
# F = x²·‖Â·A2‖². The x-order is EXACTLY 2 (one factor of x² from ‖x·Â·A2‖² = x²‖Â A2‖²). NEVER x⁴,
# because A1 appears LINEARLY in the product ∏C (each factor appears to degree 1 in the matrix product),
# so x (scaling A1) appears to degree 1 in ∏C, degree 2 in ‖∏C‖². STRUCTURAL: matrix-chain product is
# MULTILINEAR in the factors ⟹ each blow-up coordinate enters F to order exactly 2. k_E = 1 always.
print("=== (a2) no-undershoot: matrix-chain product is MULTILINEAR ⟹ each blow-up coord enters F to order 2 ===")
# Verify multilinearity → order-2 on a 3-factor chain (2,2,2,2): scale the FIRST factor by x.
import itertools
L=3  # 3 factors, widths (2,2,2,2)
facs=[sp.Matrix(2,2, sp.symbols(f'c{s}_0:4')) for s in range(L)]
P=facs[0]
for s in range(1,L): P=P*facs[s]
P=sp.expand(P)
F=sp.expand(sum(P[i,j]**2 for i in range(2) for j in range(2)))
x=sp.Symbol('x')
# scale factor 0 by x: c0_* -> x·c0_*
sub={s:x*s for s in facs[0]}
Fx=sp.expand(F.subs(sub))
# order of Fx in x:
poly=sp.Poly(Fx,x); degs=[m[0] for m in poly.monoms()]
print(f"  3-factor chain, scale factor-0 by x: F(x·C0) has x-degrees {sorted(set(degs))}")
print(f"  ⟹ homogeneous of degree {min(degs)}..{max(degs)} in x; the blow-up extracts x^{min(degs)} (= x²).")
# scale the MIDDLE factor:
sub2={s:x*s for s in facs[1]}
Fx2=sp.expand(F.subs(sub2)); poly2=sp.Poly(Fx2,x); degs2=[m[0] for m in poly2.monoms()]
print(f"  scale MIDDLE factor-1 by x: x-degrees {sorted(set(degs2))} (also exactly 2 — multilinear).")
print("""
  ⟹ EVERY factor enters ‖∏C‖² to degree EXACTLY 2 (multilinearity of the matrix product + squaring).
  So every pivot blow-up gives F = x²·(reduced), k_E = 1 on every exceptional divisor. The atlas inf
  = ½·(min codim over all centers) = ½·min_t Mval — NO undershoot, NO (x²+y²)²-style multiplicity-2 trap.
  The regular-sequence/multiplicity-1 property is FORCED by multilinearity, not assumed.
""")
print("CONCLUSION (a2): atlas inf = ½·min_t Mval exactly (k_E=1 structural via multilinearity). No undershoot.")
