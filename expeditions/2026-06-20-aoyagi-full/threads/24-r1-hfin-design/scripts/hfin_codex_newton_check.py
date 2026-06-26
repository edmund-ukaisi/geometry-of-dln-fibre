from fractions import Fraction
from scipy.optimize import linprog
# Codex's Newton model for F = r^2 U_T + a^2 s^2 U_D (the (3,3,4) disjoint sum, generic units):
# monomials: r^2 (term 1), a^2 s^2 (term 2). The RLCT via the integral
#   int (r^2 + a^2 s^2)^{-c} r^3 a^3 s^3 dr da ds  (Jacobian r^3 a^3 s^3 from the two radial blow-ups).
# Codex LP: min 4 w_r + 4 w_a + 4 w_s s.t. 2 w_r >= 1, 2 w_a + 2 w_s >= 1.
# Here weights w come from the Jacobian +1: each var contributes (h+1) = 4 (since r^3->h_r=3,+1=4).
# The constraints: each monomial term's exponent dotted with w >= 1 (the threshold-1 normalization):
#   term r^2: 2 w_r >= 1. term a^2 s^2: 2 w_a + 2 w_s >= 1.  Minimize sum (h_i+1) w_i = 4(w_r+w_a+w_s).
# This is the toric/Newton LP for the RLCT lambda = min over the Newton polytope.
c = [4.0, 4.0, 4.0]  # minimize 4(w_r + w_a + w_s)
A_ub = [[-2,0,0],[0,-2,-2]]  # -2 w_r <= -1 ; -2 w_a - 2 w_s <= -1
b_ub = [-1,-1]
res = linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=[(0,None)]*3, method='highs')
print("Codex Newton LP for F = r^2 U_T + a^2 s^2 U_D:")
print("  lambda =", Fraction(res.fun).limit_denominator(1000), " (Codex says 4)")
print("  optimum w =", [Fraction(x).limit_denominator(100) for x in res.x])
print()
# This = 4 = minAdm/2 for (3,3,4). CONFIRMED. The disjoint-sum value 4 is realized by the Newton LP
# on the TWO-monomial model with the Jacobian weights -- a TORIC computation, no determinantal geometry.
print("CONFIRMED: lambda = 4 = minAdm/2. The additive value 2+2=4 is a 2-monomial toric Newton LP.")
print("Codex's monomial-sum-refinement (blow up {r,a} then {beta,s}) realizes it as a single-axis")
print("monomial leaf (h+1=8 on the dominant axis) -- matching my /tmp/hfin_crux3b.py (h+1=8, threshold 4).")
