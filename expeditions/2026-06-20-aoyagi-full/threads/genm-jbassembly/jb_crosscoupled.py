import sympy as sp
# On a GOOD chart (pivot a bounded below), is the CROSS-COUPLED Schur loss
#   g_cc(Gamma,v) = a^2 * frobSq(v A2) + frobSq((C v + Gamma W) A2)
# (i) degree-2-homogeneous jointly in (Gamma, v)?  (ii) > 0 on the joint sphere
# when a != 0 and A2, W A2 full row rank?  If yes, the endpoint accepts g_cc DIRECTLY
# (no "drop L", no det-inverse).  Test symbolically on tiny dims (t=1, corank 1x1).
a, r = sp.symbols('a r', positive=True)
v0,v1 = sp.symbols('v0 v1')          # v : 1x2 row (reduced-chain front, dim 2)
G = sp.symbols('G')                   # Gamma : 1x1 corank block (dim 1)
C = sp.symbols('C')                   # C : 1x1
# A2 : 2x2 full rank, W : 1x2
A2 = sp.Matrix([[1,2],[0,3]]); W = sp.Matrix([[1,1]])
v = sp.Matrix([[v0,v1]])
vA2 = v*A2
cross = (C*v + sp.Matrix([[G]])*W)*A2        # (1x2)
def frob(M): return sum(x**2 for x in M)
g_cc = a**2*frob(vA2) + frob(cross)
# (i) homogeneity in (Gamma,v): substitute (v,G) -> r*(v,G)
g_scaled = g_cc.subs({v0:r*v0, v1:r*v1, G:r*G})
hom_ok = sp.simplify(g_scaled - r**2*g_cc) == 0
print("g_cc degree-2-homog in (Gamma,v):", hom_ok)
# (ii) positivity: g_cc = 0 with (v,G)!=0 and a!=0 ? Solve.
sol = sp.solve([sp.Eq(x,0) for x in [a**2*vA2[0], a**2*vA2[1], cross[0], cross[1]]],
               [v0,v1,G], dict=True)
print("zeros of g_cc (a!=0):", sol, " -> only trivial (v=G=0) means positive on sphere")
# Also confirm: DISJOINT form g_dis = a^2 frobSq(vA2) + frobSq(G W A2) after dropping L
g_dis = a**2*frob(vA2) + frob(sp.Matrix([[G]])*W*A2)
print("g_dis degree-2-homog:", sp.simplify(g_dis.subs({v0:r*v0,v1:r*v1,G:r*G}) - r**2*g_dis)==0)
