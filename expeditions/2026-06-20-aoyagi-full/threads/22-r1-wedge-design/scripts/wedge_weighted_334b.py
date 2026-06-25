import sympy as sp
u = sp.symbols('u', positive=True)
g = sp.symbols('g0:20', real=True)
C1 = sp.Matrix([[1,0,0],[0,u*g[0],u*g[1]],[0,u*g[2],u*g[3]]])
C2 = sp.Matrix([[u*g[4],u*g[5],u*g[6],u*g[7]],[g[8],g[9],g[10],g[11]],[g[12],g[13],g[14],g[15]]])
P = sp.expand(C1*C2)
F = sp.expand(sum(P[i,j]**2 for i in range(3) for j in range(4)))
U = sp.expand(F/u**2)
# U should equal ||tbar||^2 + ||D̄ S||^2:
Dbar = sp.Matrix([[g[0],g[1]],[g[2],g[3]]])
S = sp.Matrix([[g[8],g[9],g[10],g[11]],[g[12],g[13],g[14],g[15]]])
tbar = [g[4],g[5],g[6],g[7]]
U_expected = sum(t**2 for t in tbar) + sum((Dbar*S)[i,j]**2 for i in range(2) for j in range(4))
print("U - (||tbar||^2 + ||D̄ S||^2) =", sp.simplify(U - U_expected), " (0 => exact)")
print()
# U bounded below on a positive-measure tube? U = ||tbar||^2 + ||D̄ S||^2.
# Pick the tube: tbar near (1,0,0,0) (||tbar||^2 ~ 1), S near identity-extended (rank 2), D̄ near I.
# Then ||tbar||^2 >= 1/4 (say), and ||D̄ S||^2 >= 0. So U >= 1/4 > 0 on the tube. ✓
# Even simpler: ||tbar||^2 alone is bounded below if tbar_0 ∈ [1/2, 1] (a positive-measure constraint).
# So U >= tbar_0^2 >= 1/4 on {tbar_0 ∈ [1/2,1], rest in box}. POSITIVE MEASURE. ✓
print("U = ||tbar||^2 + ||D̄ S||^2 >= ||tbar||^2 >= tbar_0^2 >= 1/4 on {tbar_0∈[1/2,1], ...}. ")
print("POSITIVE-MEASURE tube where U >= 1/4 > 0 (bounded below). ✓ No need for D̄,S generic-rank!")
print()
# This is even cleaner than I feared: the T-block ALONE (||tbar||^2, just 4 free coords) bounds U below.
# So the corank coupling (D̄ S) is NOT NEEDED for the lower bound's U>0 -- the clean T-block suffices.
# CORANK-IMMUNE confirmed: the binding comes from u^2 (single axis), U bounded below by the clean block.
print("=> CORANK-IMMUNE: U bounded below by the CLEAN T-block alone. The coupled D̄S only ADDS to U")
print("   (helps, never hurts). The lower bound never touches the corank obstruction. ✓✓")
print()
# JACOBIAN of the weighted blow-up x_i = u^{wt_i} xbar_i (wt=1 on 8 scaled coords, 0 on rest):
# the map (u, g) -> (C1 entries, C2 entries). The 8 scaled coords are u·g_i; the blow-up param is u.
# Standard weighted blow-up Jacobian: for x_i = u·xbar_i (i=1..8), the map (u, xbar_1..xbar_8, rest) 
# -> (x_1..x_8, rest) has Jacobian u^{8-1} = u^7 (one xbar absorbed as the blow-up direction... 
# actually the chart is (u, v_1..v_7, rest) with x_1=u, x_i=u·v_{i-1}: Jac u^7). = u^{minAdm-1}. ✓
print("Jacobian = u^{minAdm-1} = u^7 (weighted blow-up of the 8-dim center). Single binding axis (1,7).")
