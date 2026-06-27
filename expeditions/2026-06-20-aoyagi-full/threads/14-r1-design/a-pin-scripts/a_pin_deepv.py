import sympy as sp
# Test the (a)-split at a DEEPER fibre point v (non-smooth), where a residual core SHOULD remain.
# Use (3,3,3) r=0. Deepest = origin. Take v in the S(1,0) stratum (rank A1=1) -- but that's the
# achiever (smooth, codim 7), residual would be empty too. Instead test v at S(0,0)-ADJACENT, i.e.
# a point that is in the closure structure but deeper. Actually the deepest non-origin singular point:
# take v = a rank-1 A1 but NOT generic -- still smooth. The NON-smooth fibre points ARE the deeper
# strata (S(0,0)=origin only for (3,3,3)? No: S(2,0),S(3,0) also). Let me reconsider.
#
# KEY REALIZATION: for D1>=, the comparison is deepest (origin) vs ARBITRARY v. The arbitrary v ranges
# over ALL fibre points. At a SMOOTH fibre point (generic, achiever stratum) the split is trivial
# (pure regular, residual core EMPTY) and lambda_v = codim/2 = min. At a DEEPER v (higher stratum) the
# residual core is NON-empty. The (a) prereq must handle ALL v, including the deep ones.
#
# The DEEPEST non-origin v for (3,3,3): S(3,0) stratum (rank A1=3, A2=0), Mval=9, NOT smooth (codim 9
# but the rank-3 condition... actually rank A1=3 is generic/open, so S(3,0)={A2=0} is smooth codim 9!).
# Hmm. So which strata are NON-smooth (have a residual core)? A stratum S(t) is smooth where the rank
# conditions are transverse. The ORIGIN (all ranks 0) is the deepest. Let me test v = origin-adjacent:
# actually the cleanest NON-trivial test: v in S(1,0) for a chain where S(1,0) is NOT the achiever.
# For (4,3,2): achiever = S(2,0)/S(3,0) (Mval 6). S(1,0) has Mval 8 > 6, S(0,0)=12. So at a v in
# S(1,0) (Mval 8), the loss has a residual core (it's NOT the generic stratum). Test the split there.
print("=== (a)-split at a NON-generic v: (4,3,2), v in S(1,0) (Mval 8, NOT the achiever) ===")
# A1 4x3 rank 1, A2 3x2 with A1A2=0. v: A1 = e0 e0^T-ish rank1, A2 in ker.
w1 = sp.symbols('p0:12', real=True)  # A1 perturbation (4x3)
w2 = sp.symbols('q0:6', real=True)   # A2 perturbation (3x2)
W1 = sp.Matrix(4,3,w1); W2 = sp.Matrix(3,2,w2)
# v1: rank-1 4x3 = col [1,0,0,0] times row [1,0,0]
v1 = sp.zeros(4,3); v1[0,0]=1
# v2: 3x2 in ker(v1). ker(v1) = {x: v1 x =0} = rows 2,3 of x free... v1 x = [x0; 0;0;0] so ker = x0=0.
# v2 cols with first entry 0:
v2 = sp.Matrix([[0,0],[1,0],[0,1]])  # cols (0,1,0),(0,0,1) -- first entry 0, in ker(v1)
A1 = v1+W1; A2 = v2+W2
P = sp.expand(A1*A2)  # 4x2
allv = list(w1)+list(w2)
J = sp.Matrix([[sp.diff(sp.expand(P[i,j]),vv).subs({x:0 for x in allv}) for vv in allv] for i in range(4) for j in range(2)])
rk = J.rank()
print(f"  generators: {4*2}=8, local vars: {len(allv)}=18")
print(f"  Jacobian rank at v (S(1,0)) = {rk}")
print(f"  => {rk} regular directions; residual core dim ~ (singular part).")
print(f"  Mval(S(1,0)) for (4,3,2) = 8; codim of {{prod=0}} at v.")
print(f"  Jacobian rank {rk} vs gens 8: residual core present iff rk < (effective generators).")
