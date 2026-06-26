import sympy as sp

# (2,2,2): F = x0^2 x4^2 + x0^2 x5^2 + 2 x0 x1 x4 x6 + 2 x0 x1 x5 x7 + x1^2 x6^2 + x1^2 x7^2
#            + x2^2 x4^2 + x2^2 x5^2 + 2 x2 x3 x4 x6 + 2 x2 x3 x5 x7 + x3^2 x6^2 + x3^2 x7^2
# = ||A B||^2 with A=[[x0,x1],[x2,x3]], B=[[x4,x5],[x6,x7]].
#
# WEDGE HYPOTHESIS: find a FLAT region R (positive measure) + flat function g with
#   F(x) <= C·g(x) on R, and ∫_R g^{-c'} = ⊤ at c'=3/2.
# The chart says the binding direction has F~u_b^2, Jac~u_b^2 (the z1 axis). Translate to flat.
#
# IDEA: the achiever is "A becomes rank-1, B free-ish".  Take A = rank-1: x0=p, x1=p·a, x2=q, x3=q·a 
# (rows proportional: row2 = (q/p)·row1, i.e. A has rank 1 when x0 x3 = x1 x2).
# On the rank-1 locus of A: P = A B has rank ≤ 1. Parametrize A = c · w^T (outer of col c, row w).
# Actually for divergence we want a TUBE, not the exact rank-1 locus (measure zero).
#
# Let me test the DIRECT flat monomial tube the chart suggests. The chart phiUnit pulls back to
# u0 (A-pivot) and z1 (the resolved-leaf pivot). The flat image of the binding axis: as z1 varies
# with u0 fixed generic, the flat point moves along a CURVE. F = u0^2 z1^2 U.  In flat coords, 
# along this curve some coordinate ~ z1.  The KEY: is the flat tube's monomial bound valid on 
# positive measure? Let me just compute the chart image and its preimage measure honestly via the 
# proven facts (it IS positive measure — phiUnit''([0,δ]^8 minus null) and CoV gives the Jacobian).
#
# So for (2,2,2) the WEDGE = the CHART (phiUnit''box is the tube, Jacobian is the volume weight).
# A "lighter" wedge would be a flat region NOT requiring the full Jacobian computation.
#
# TEST: can we use a SINGLE pivot blow-up (lighter) instead of the depth-2 composition?
# Single A-pivot: step1A(y) = [y0, y0 y1, y0 y2, y0 y3, y4,y5,y6,y7]. 
#   F(step1A y) = y0^2 · Q(y),  Q = ||Â B||^2, Â=[[1,y1],[y2,y3]].  (myF222_step1A, proven)
# Jacobian of step1A = y0^3. So ∫ y0^3 (y0^2 Q)^{-c} = ∫ y0^{3-2c} Q^{-c}.
# At c=3/2: y0^0 = 1. So ∫_{box in y0} dy0 · ∫ Q^{-3/2} (over y1..y7, y4..y7).
# Q = ||Â B||^2 with Â=[[1,y1],[y2,y3]], B free. Is ∫ Q^{-3/2} = ⊤ over a box?
# Q's zero set: Â B = 0. Â=[[1,y1],[y2,y3]] is generically rank 2 (det = y3 - y1 y2). 
# If det≠0, Â B=0 iff B=0. So Q=0 locus near 0 is {B=0} ∪ {det=0 stuff}. 
# rlct of Q at 0? Q = (y3? )... let me just compute the threshold of Q via its structure.
y = sp.symbols('y0:8', real=True)
Ahat = sp.Matrix([[1,y[1]],[y[2],y[3]]])
B = sp.Matrix([[y[4],y[5]],[y[6],y[7]]])
Q = sp.expand(sum((Ahat*B)[i,j]**2 for i in range(2) for j in range(2)))
print("Q =", Q)
print("det Ahat =", sp.expand(Ahat.det()))
# Q as quadratic form in B (y4..y7) with coefficient matrix depending on (y1,y2,y3):
# Q = ||Ahat B||^2 = tr(B^T Ahat^T Ahat B) = sum over columns b of b^T (Ahat^T Ahat) b.
# Ahat^T Ahat is PD when det Ahat ≠0. So Q ≈ (positive const)·||B||^2 near generic (y1,y2,y3).
# => Q ~ ||B||^2 (4 vars), rlct of ||B||^2 over R^4 box at 0 = 4/2 = 2. Threshold 2 > 3/2.
# So ∫ Q^{-3/2} CONVERGES (3/2 < 2). The single A-pivot does NOT reach the achiever! 
print()
print("Q ~ (pos const)·||B||^2 for generic (y1,y2,y3): rlct(Q)=2, ∫Q^{-3/2} converges (3/2<2).")
print("=> SINGLE pivot blow-up UNDERSHOOTS. Need the 2nd (resolved-leaf) pivot. depth-2 needed for (2,2,2).")
