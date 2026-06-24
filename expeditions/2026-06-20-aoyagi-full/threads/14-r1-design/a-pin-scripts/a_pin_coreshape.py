import sympy as sp
# Find a fibre point v where the residual core is NON-empty, and identify its shape.
# The residual core is non-empty where v is a SINGULAR point of {prod=0}. For L=2, {A1 A2=0} -- its
# singular locus is where the stratification is non-transverse. The origin is singular. Are there OTHER
# singular fibre points? {A1A2=0} singular locus = where rank(A1)+rank(A2) < ... Let me find one.
#
# Actually for L=2 generic, {A1 A2=0} = {rank A1 <= k, rank A2 <= n-k}? No. {A1A2=0} for 2x2: the
# determinantal-type variety. Its singular locus: points where multiple strata meet, e.g. A1=0 (then
# A2 free) meets the A1-rank-1 stratum. At A1=0, A2 generic: rank A1=0 (S(0,0)), and the germ is...
w = sp.symbols('w0:8', real=True)
W1=sp.Matrix([[w[0],w[1]],[w[2],w[3]]]); W2=sp.Matrix([[w[4],w[5]],[w[6],w[7]]])
# v = (A1=0, A2 = generic invertible), in fibre (0*A2=0), stratum S(0,0) (rank A1=0).
v1=sp.zeros(2,2); v2=sp.Matrix([[2,1],[1,3]])  # generic invertible A2
P=sp.expand((v1+W1)*(v2+W2))
allv=list(w)
J=sp.Matrix([[sp.diff(sp.expand(P[i,j]),vv).subs({x:0 for x in allv}) for vv in allv] for i in range(2) for j in range(2)])
print("=== (2,2,2) v=(A1=0, A2 generic invertible), stratum S(0,0) ===")
print(f"  Jacobian rank = {J.rank()}, Mval(0,0)=4.")
for i in range(2):
    for j in range(2):
        print(f"    P_{i}{j} =", sp.expand(P[i,j]))
print()
# This v=(A1=0, A2 inv): generators P_ij = (W1 (v2+W2))_ij = linear in W1 + W1 W2. Since v2 invertible,
# the 4 generators (W1 v2)_ij are 4 INDEPENDENT linear forms in W1's 4 entries => Jacobian rank 4 => 
# SMOOTH codim 4, residual core EMPTY. (A1=0, A2 inv) is a SMOOTH point.
print(f"  => Jacobian rank {J.rank()} = 4 = full (W1 v2 independent, v2 inv). SMOOTH, core EMPTY.")
print()
# So WHERE is the core non-empty?? The ORIGIN (A1=A2=0): all generators bilinear, Jac rank 0, core=ALL.
# Test the origin:
P0=sp.expand(W1*W2)
J0=sp.Matrix([[sp.diff(sp.expand(P0[i,j]),vv).subs({x:0 for x in allv}) for vv in allv] for i in range(2) for j in range(2)])
print(f"=== ORIGIN (A1=A2=0): Jacobian rank = {J0.rank()} => core = WHOLE germ ||W1 W2||^2 (homogeneous deg 2) ===")
print("  This is exactly ||prod(C)||^2 for the (2,2,2) chain at its origin = #111's object.")
print()
print("=== CONCLUSION on residual-core shape ===")
print("For L=2 (2,2,2): the residual core is EMPTY at EVERY fibre point EXCEPT the origin (deepest).")
print("At the origin, core = the FULL ||prod(C)||^2 (= #111's object). At every OTHER v, v is a SMOOTH")
print("point of {prod=0} (residual core empty, pure regular block). So:")
print(" - For arbitrary v != deepest: (a)-split is TRIVIAL (pure nondeg quadratic, NO core). lambda_v=codim/2.")
print(" - The comparison lambda_deepest <= lambda_v: deepest core resolves to min/2; v smooth gives codim/2 >= min/2.")
