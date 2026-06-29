import sympy as sp
# Does the PER-LAYER Agen equality hold, or only the CHART (composed prod) level?
# φ = B(pbo x) confirmed (chart). Question: chartParamsGen (x_p) GBx == chartParamsGen 1 (GB(pbo x))  PER LAYER?
# At (2,2,2): layers A_0, A_1. The fixed pivot E(0,0) lives in A_0[1,1] (the x0·1 = u term).
# chartParamsGen (x_p) GBx layer A_0: has x5*x1 + x0  (the u·pivotEIndicator)
# chartParamsGen 1 (GB(pbo x)) layer A_0: GB reads pbo x; the FIXED pivotEIndicator is x-INDEPENDENT (literal 1),
#   so Agen 1 gives x5*x1 + 1·1 = x5*x1 + 1  (the radial scalar is 1, anchor unscaled)
# These differ (x0 vs 1) UNLESS the x0 is recovered elsewhere. Let's check the actual layer matrices.
x = sp.symbols('x0:8', real=True); u = x[0]
# A_0 of chartParamsGen (x_p) GBx (the achiever chart layer 0):
A0_lhs = sp.Matrix([[x[4], x[4]*x[1]], [x[5], x[5]*x[1] + x[0]]])   # ...+u·1 (fixed pivot, radial x0)
# A_0 of chartParamsGen 1 (GB(pbo x)): radial=1, GB reads pbo x. Fixed pivotEIndicator unscaled (=1), readers at pbo x.
# B's A0[1,1] = (read at pbo x: x5,x1 are NON-active K/X coords → unchanged) + 1·pivotEIndicator(0,0)=1·1=1
A0_rhs = sp.Matrix([[x[4], x[4]*x[1]], [x[5], x[5]*x[1] + 1]])      # radial=1, anchor=1
print("PER-LAYER A_0 equal?", sp.simplify((A0_lhs - A0_rhs)) == sp.zeros(2,2))
print("  A0_lhs[1,1] =", A0_lhs[1,1], "  A0_rhs[1,1] =", A0_rhs[1,1], " → differ by", sp.simplify(A0_lhs[1,1]-A0_rhs[1,1]))
print("So per-layer Agen equality is FALSE at the anchor (x0 vs 1) — the chart-level φ=B(pbo) recovers x0 via the PROD, not per-layer.")
