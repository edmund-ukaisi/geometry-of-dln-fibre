import sympy as sp
# RIGOROUS: the single weighted blow-up for (3,3,4), EXACT in flat coords. Test F = u^2·U, U bounded below.
u = sp.symbols('u', positive=True)
# Achiever center: scale T-block (C2 top row, 4 coords) by u, Delta-block (C1 bottom-right 2x2, 4 coords) by u.
# Surviving: C1 pivot (0,0)=1, S = C2 bottom 2 rows (8 coords) generic. Off-blocks: 0 (or generic spectators).
# Construct C1, C2 with the weighted scaling:
g = sp.symbols('g0:20', real=True)  # generic bounded params (the "xbar" / shape coords)
# C1: pivot (0,0)=1; Delta-block (rows1-2, cols1-2) = u·D̄; col0 rows1,2 and row0 cols1,2 = ? 
#   For the achiever stratum, the off-pivot entries of C1 should be 0 (the gauge eliminated them) or 
#   small. Set them to 0 (we pick a convenient sub-wedge; lower bound only needs positive measure).
C1 = sp.Matrix([[1,0,0],[0,u*g[0],u*g[1]],[0,u*g[2],u*g[3]]])
# C2: top row = u·tbar (T-block, scaled by u); bottom 2 rows = S (generic, NOT scaled).
C2 = sp.Matrix([[u*g[4],u*g[5],u*g[6],u*g[7]],[g[8],g[9],g[10],g[11]],[g[12],g[13],g[14],g[15]]])
P = sp.expand(C1*C2)
F = sp.expand(sum(P[i,j]**2 for i in range(3) for j in range(4)))
# Factor out u^2:
Fq = sp.Poly(F, u)
print("F as polynomial in u:", Fq)
# Check: lowest power of u in F, and F/u^2 at u=0 (the unit U).
F_over_u2 = sp.simplify(F / u**2)
U0 = sp.expand(F_over_u2.subs(u, 0))
print()
print("F / u^2 at u=0  (the unit U(0)) =", U0)
# U(0) should be a sum of squares (>= 0), and bounded below away from 0 on the generic tube.
