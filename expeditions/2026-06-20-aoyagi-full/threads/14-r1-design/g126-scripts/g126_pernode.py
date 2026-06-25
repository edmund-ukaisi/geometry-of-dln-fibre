import sympy as sp
# BRIDGE: does #125's unit-pivot construction apply PER-NODE (each dlnLoss M' 0, B'=0 zero-core),
# or is it just the OUTER L2 split (B rank r > 0)?
#
# #125 setting: F = ‖∏C − B‖², B RANK r > 0. The deepest point has B's regular block; the perturbed
# pivot is (1+w0) (a UNIT). Unit-pivot regular peel strips nReg, leaves the Schur core.
#
# PER-NODE R1 setting: dlnLoss M' 0 = ‖∏C'‖², B' = 0 (ZERO-product core). Deepest point = the ORIGIN
# (all C'=0). At the origin, prod=0 => P[0,0]=0, NOT a unit. So the unit-pivot regular peel CANNOT
# apply at the zero-core origin (no regular block, no unit pivot — the whole thing is the singular core).
#
# Test: (2,2,2) zero-core dlnLoss (2,2,2) 0 = ‖A1 A2‖², at the origin.
a=sp.symbols('a0:4'); b=sp.symbols('b0:4')
A1=sp.Matrix(2,2,a); A2=sp.Matrix(2,2,b); P=A1*A2
gens=[sp.expand(P[i,j]) for i in range(2) for j in range(2)]
allv=list(a)+list(b)
J=sp.Matrix([[sp.diff(g,vv).subs({x:0 for x in allv}) for vv in allv] for g in gens])
print("=== per-node: dlnLoss (2,2,2) 0 = ‖A1 A2‖² at the ORIGIN (B'=0 zero-core) ===")
print("  generators P_ij:", gens)
print(f"  Jacobian rank at origin = {J.rank()} (= nReg here)")
print("  ALL generators are BILINEAR (homogeneous degree 2), NO linear part => Jac rank 0 => NO regular")
print("  block, NO unit pivot. The unit-pivot regular peel (#125) does NOT apply at the zero-core origin.")
print()
print("=== So the per-node R1 chart is NOT #125's unit-pivot regular peel. What IS it? ===")
print("It's the C2 node (#118/#121): BLOW UP the rank-stratum center FIRST (which makes a pivot a HARD 1,")
print("e.g. {A1=0} → A1=x·Â, Â[0,0]=1 hard), THEN the det-1/transvection Schur straighten (lemma2Fwd-style,")
print("MEASURE-PRESERVING), THEN recurse on the smaller zero-core. The monomial weight comes from the blow-up.")
print()
print("CONTRAST with #125 (outer L2 split): B rank r>0, regular block present, perturbed-unit pivot (1+w0),")
print("unit-pivot peel (unit-Jacobian, no blow-up). #125 is the OUTER split; per-node is the C2 blow-up+straighten.")
