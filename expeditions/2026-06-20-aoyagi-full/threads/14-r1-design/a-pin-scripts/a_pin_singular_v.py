import sympy as sp
import numpy as np
# Where is the loss germ at v genuinely SINGULAR (residual core non-empty)?
# A fibre point v is a smooth point of {prod=0} iff it's in the OPEN part of its stratum (generic).
# At a NON-generic v -- one in the closure of a DEEPER stratum -- the germ is singular.
# But Aoyagi Thm2 / D1>= compares deepest vs ARBITRARY v. The relevant v's for the INF are the
# GENERIC points of each stratum (smooth), where lambda_v = codim/2. The deeper (singular) v's have
# even SMALLER... no, LARGER lambda? Let me reconsider what D1>= actually needs.
#
# D1>= : lambda_deepest <= lambda_v for ALL v in the fibre. The MINIMUM lambda over the fibre is at the
# GENERIC point of the ACHIEVER stratum (smooth, codim = min Mval, lambda = min/2). The deepest (origin)
# has lambda = min/2 too (its resolution sees the achiever divisor). Singular v's (stratum boundaries)
# have lambda >= min/2 (more singular = ... actually the rlct at a more singular point is SMALLER or
# LARGER?). For sum-of-squares, MORE singular (higher codim tangent cone) => SMALLER rlct. So the
# DEEPEST (origin, most singular) should have the SMALLEST rlct. But we computed rlctAt(origin)=min/2,
# and generic-achiever-point also = min/2. So they're EQUAL, and deeper-than-generic points...
#
# Let me just DIRECTLY test: is there a fibre point v with lambda_v < min/2? If D1>= holds, NO.
# And is the (a)-split at EVERY v = [regular] + [homog core]? Test at a genuinely singular v.
#
# Genuinely singular fibre point for (2,2,2): the origin is one. Another: v where A1, A2 both rank 1
# AND aligned so the germ is singular. Take v: A1=[[1,0],[0,0]], A2=[[0,1],[0,0]] -> A1A2=[[0,1],[0,0]]!=0.
# Not in fibre. Need A1A2=0. v: A1=[[1,0],[0,0]], A2=[[0,0],[1,0]] -> A1A2 = [[0,0],[0,0]]? 
# A1A2 = [[1,0],[0,0]]@[[0,0],[1,0]] = [[0,0],[0,0]]. YES in fibre. rank A1=1, rank A2=1.
w = sp.symbols('w0:8', real=True)
W1=sp.Matrix([[w[0],w[1]],[w[2],w[3]]]); W2=sp.Matrix([[w[4],w[5]],[w[6],w[7]]])
v1=sp.Matrix([[1,0],[0,0]]); v2=sp.Matrix([[0,0],[1,0]])
P=sp.expand((v1+W1)*(v2+W2))
allv=list(w)
J=sp.Matrix([[sp.diff(sp.expand(P[i,j]),vv).subs({x:0 for x in allv}) for vv in allv] for i in range(2) for j in range(2)])
print("=== (2,2,2) v: A1=[[1,0],[0,0]], A2=[[0,0],[1,0]] (both rank1, A1A2=0) ===")
print(f"  Jacobian rank = {J.rank()} (codim of stratum). gens=4.")
for i in range(2):
    for j in range(2):
        print(f"    P_{i}{j} =", sp.expand(P[i,j]))
print(f"  This v is in S(1,0) (rank A1=1). codim={J.rank()}=Mval(1,0)=3. SMOOTH (rk=3, 1 gen dependent).")
print()
print("OBSERVATION: at this v, P10 = w2*(...)+... let me check if a residual core remains after the split.")
P00,P01,P10,P11=P[0,0],P[0,1],P[1,0],P[1,1]
# linear parts:
for nm,g in [('P00',P00),('P01',P01),('P10',P10),('P11',P11)]:
    lin=sum(sp.diff(g,vv).subs({x:0 for x in allv})*vv for vv in allv)
    print(f"  lin {nm} = {lin}")
