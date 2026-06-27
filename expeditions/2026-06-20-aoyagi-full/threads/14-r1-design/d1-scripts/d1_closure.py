import sympy as sp
import numpy as np
# (C): is the deepest core point (all C^(s)=0) in the closure of EVERY fibre stratum?
# Fibre stratum of v = the set of fibre points with v's rank pattern (ranks of partial products).
# Claim: for ANY fibre point v, the path A^(s)(eps) = eps * A^(s)(v) (scale all layers by eps->0)
# stays in the fibre's homogeneous core variety {prod=0 core} and limits to the all-zero deepest core.
# But does it stay in the SAME stratum? No -- it DEGENERATES (ranks drop). The point is the deepest is
# in the closure (limit), which is what Aoyagi needs (deepest is the most degenerate, a limit of every v).
print("=== (C) deepest in closure of every stratum: the scaling path ===")
print("For any core fibre point v=(C^(1),...,C^(L)) with prod=0 (core, B=0):")
print("  path t |-> (t C^(1), ..., t C^(L)), t->0, stays in {prod=0} (prod(tC)=t^L prod(C)=0),")
print("  and limits to (0,...,0) = deepest core. So deepest is in the closure of the ray through v.")
print("  This is PURELY the homogeneity of prod (multilinear degree L) + the fibre being a cone.")
print("  NO RLCT value involved. The fibre core variety is a CONE (scale-invariant) => 0 in every closure.")
print()
# Sanity: prod is multilinear => prod(t.A) = t^L prod(A). Verify on (2,2,2) generic:
a = sp.symbols('a0:4', real=True); b=sp.symbols('b0:4', real=True); t=sp.symbols('t', real=True)
A1=sp.Matrix([[a[0],a[1]],[a[2],a[3]]]); A2=sp.Matrix([[b[0],b[1]],[b[2],b[3]]])
P=A1*A2
Pt=(t*A1)*(t*A2)
print("prod(t.A) - t^2 prod(A) =", sp.simplify((Pt - t**2*P)))
print("=> prod(t.A)=t^L prod(A) (L=2 here). Fibre core {prod=0} is a cone. deepest=0 in every closure. VALUE-FREE.")
print()
print("=== the raw-loss B!=0 caveat (the (a) obligation) ===")
print("For B!=0 the RAW loss is NOT homogeneous; D1 is applied to the HOMOGENEOUS CORE after the")
print("L2/G3.2 rank-r split (the regular E_r carries B's nonzero part; the singular core has B'=0).")
print("That split is G3.2 (now task #111, the chart) -- its EXISTENCE, not its VALUE. So D1>= consumes")
print("G3.2's chart (normal-form existence) + S1 + rlctAt_mono + homogeneity. None is R1's value.")
