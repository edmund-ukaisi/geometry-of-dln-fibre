import sympy as sp
# THE DECISIVE TEST: apply the det-1 Schur substitution to the ZERO-product core ||A1 A2||^2 (B=0).
# Does it give a clean nReg/2 + smaller-core split (A), or does the leading minor FAIL to be a unit
# (so no det-1 chart exists at the origin -> you NEED the blow-up (B))?
#
# My #109 cert's hypothesis: "the leading t1xt1 minor of the partial product is a UNIT". At the ORIGIN
# (A1=A2=0), the product P = 0, so P[0,0] = 0 -- NOT a unit. So the det-1 Schur chart hypothesis FAILS
# at the origin. The det-1 chart only exists where P[0,0] != 0 (a principal-open chart), NOT at the
# deepest singular point. THIS is the gap fm-2 caught.
print("=== Does the det-1 Schur chart exist at the ZERO-CORE origin? ===")
a=sp.symbols('a0:4'); b=sp.symbols('b0:4')
A1=sp.Matrix(2,2,a); A2=sp.Matrix(2,2,b)
P=A1*A2
print("P[0,0] =", sp.expand(P[0,0]), " -- at origin (a=b=0): P[0,0] =", P[0,0].subs({s:0 for s in list(a)+list(b)}))
print("=> at the ZERO-CORE origin, P[0,0]=0, NOT a unit. The det-1 Schur chart HYPOTHESIS (leading")
print("   minor is a unit) FAILS at the origin. So (A) det-1 does NOT apply at the deepest singular pt.")
print()
print("WHERE does the det-1 chart apply? On the principal-open {P[0,0] != 0} -- the SMOOTH part of the")
print("zero-locus's complement, OR after a B!=0 rank-r reduction where the regular block makes a minor")
print("a unit. The det-1 chart is for PEELING THE REGULAR (rank-r, B!=0) part, NOT resolving the core.")
print()
print("=== So the honest reconciliation ===")
print("(A) det-1 Schur [my #109]: applies where a leading minor is a UNIT (B!=0 regular block, or off")
print("    the singular locus). Peels the rank-r regular generators CLEANLY: F = ||reg||^2 + ||C'||^2.")
print("    = Aoyagi Thm 3 / product_reduction (the nReg/2 shift). MEASURE-PRESERVING.")
print("(B) blow-up [R1 / (2,2,2) / #111]: resolves the SINGULAR zero-core ||C'||^2 AT THE ORIGIN, where")
print("    NO minor is a unit. Nontrivial Jacobian -> monomialThreshold. = the resolution.")
print()
print("They are BOTH-IN-SEQUENCE and DIFFERENT: (A) handles B!=0 (the rank-r regular peel), terminating")
print("at the zero-core; (B) resolves the zero-core. My #109 cert validated (A) -- the B!=0 Schur peel --")
print("and its 'bottoms at a smooth leaf' was IMPRECISE: (A) bottoms at the SINGULAR zero-core (B's input),")
print("NOT a smooth leaf. The (3,3,3)->(2,2,2)->(1,1,1) multi-step was the WIDTH reduction; (1,1,1) core")
print("||c1 c2||^2 is a MONOMIAL-ish core (still needs B), not a smooth block.")
