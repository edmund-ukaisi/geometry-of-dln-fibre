import sympy as sp
# DISENTANGLE the two recursions. fm-2's catch: are (A) det-1 Schur and (B) blow-up the SAME step or
# different? My #109 cert was about the B!=0 rank-r PRODUCT reduction. Let me verify it's (A)-clean
# AND that it does NOT resolve the singular zero-core (which still needs (B)).
#
# RECURSION 1 (my #109 / G3.2 / Aoyagi Thm 3): F = ||prod(C) - B||^2, B rank r > 0.
#   Schur-peel the rank-r regular block via det-1 unimodular Q. Get F = ||reg E_r||^2 + ||prod(C')||^2,
#   C' the reduced chain, B' = 0 (the residual core is a ZERO-product core). This is a det-1 c-o-v,
#   measure-preserving, CLEAN additive split. rlctAt(F) = nReg/2 + rlctAt(||prod(C')||^2 at 0).
#   The residual ||prod(C')||^2 at 0 is STILL SINGULAR (a zero-product core) -- NOT resolved.
#
# RECURSION 2 (R1 / #111 / the (2,2,2) blow-up): resolve ||prod(C')||^2 at the ORIGIN. This is the
#   SINGULAR core; it needs the BLOW-UP (nontrivial Jacobian) -> monomialThreshold. This is R1's job.
#
# So: my #109 G3.2 = RECURSION 1 = (A) det-1 clean, peeling the r regular blocks (the n/2 shift).
#     It TERMINATES at the zero-product core ||prod(C_reduced)||^2 (B=0), which is then handed to R1
#     (RECURSION 2 = the blow-up = (B)) for the singular resolution.
#
# fm-2's confusion: the cert's "ΣM strictly drops, base = smooth block leaf" suggested RECURSION 1
# bottoms at a SMOOTH leaf. Let me CHECK what RECURSION 1 actually bottoms at.
#
# Test: (3,3,3) r=1. RECURSION 1 peels the rank-1 regular block. Residual = ||prod(C')||^2, C' the
# reduced (2,2,2) chain, B'=0. Is the (2,2,2) zero-core SMOOTH or SINGULAR?
def Mval(M,t):
    tt=[M[0]]+list(t); L=len(M)-1
    return sum((tt[j-1]-tt[j])*(M[j]-tt[j]) for j in range(1,L+1))
print("=== Disentangling the two recursions ===")
print("RECURSION 1 (#109 G3.2, B!=0 rank-r product reduction):")
print("  det-1 unimodular Q Schur-peel => F = ||reg E_r||^2 + ||prod(C')||^2 (C' reduced, B'=0).")
print("  CLEAN additive (measure-preserving c-o-v). Peels the r REGULAR generators (the nReg/2 shift).")
print("  TERMINATES when r=0: residual = ||prod(C_reduced)||^2 at origin = the SINGULAR zero-core.")
print()
print("RECURSION 2 (R1 / #111 / (2,2,2) blow-up):")
print("  resolve the SINGULAR zero-core ||prod(C')||^2 at 0 => BLOW-UP (nontrivial Jac) => monomialThreshold.")
print()
print("(3,3,3) r=1: RECURSION 1 peels rank-1 reg block => residual = (2,2,2) zero-core ||C'||^2.")
print(f"  Is the (2,2,2) zero-core smooth? Its rlct = lambdaCore(2,2,2) = {sp.Rational(min(Mval((2,2,2),(t,0)) for t in range(3)),2)} (= 3/2, SINGULAR, not n/2).")
print(f"  The (2,2,2) zero-core is SINGULAR (rlct 3/2 != smooth 4/2=2). So RECURSION 1 does NOT bottom")
print(f"  at a smooth leaf -- it bottoms at the SINGULAR zero-core, which R1 (RECURSION 2 / blow-up) resolves.")
print()
print("=> (A) and (B) are DIFFERENT steps: (A)=#109 peels the rank-r regular blocks (clean, det-1);")
print("   (B)=R1 resolves the residual zero-core (blow-up, monomialThreshold). BOTH-IN-SEQUENCE.")
