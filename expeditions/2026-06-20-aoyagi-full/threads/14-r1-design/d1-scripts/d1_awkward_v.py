import sympy as sp
# (2,1,2) r=0. Core loss F(A1,A2) = ||A1 A2||^2 = (a0^2+a1^2)(b0^2+b1^2).
# deepest = origin (0,0,0,0). lambda_origin = lambdaCore = 1 (known: (2,1,2) core RLCT = 1).
#
# AWKWARD optimal v: A1=0, A2=(c0,c1)=(1,0). Local coords: A1=(w0,w1), A2=(1+e0, e1).
# F(v+w) = (w0^2+w1^2)((1+e0)^2 + e1^2).
a0,a1 = sp.symbols('a0 a1', real=True)  # not used
w0,w1,e0,e1 = sp.symbols('w0 w1 e0 e1', real=True)
Floc = (w0**2 + w1**2)*((1+e0)**2 + e1**2)
print("F at awkward v (local coords):", sp.expand(Floc))
# Near (w,e)=(0,0): the factor ((1+e0)^2+e1^2) -> 1 (a UNIT, positive). So locally
#   F ~ (w0^2 + w1^2) * unit.  RLCT of (w0^2+w1^2) at origin in R^2 = 1 (it's x^2+y^2, an A_1-type;
#   actually rlct of x^2+y^2 in 2 vars = 1). The e-directions are FREE (unit factor) => no contribution
#   beyond the bump. So lambda_v = rlct(w0^2+w1^2) = 1.  EQUAL to lambda_deepest = 1.
#
# Let me confirm rlct(w0^2+w1^2 at 0 in R^2):
# int |w0^2+w1^2|^{-c} over a disk = int_0^1 r^{-2c} * r dr * (angle) ~ int r^{1-2c} dr,
# converges iff 1-2c > -1 iff c < 1. So rlct = 1. YES.
print("\nlambda_v (awkward) = rlct((w0^2+w1^2)*unit) = rlct(w0^2+w1^2 in R^2) = 1")
print("lambda_deepest = lambdaCore(2,1,2) = 1")
print("=> 1 <= 1. Inequality HOLDS (with EQUALITY here).")
print()
# Now check a TRULY different optimal v where the inequality is STRICT, to be sure the deepest is min.
# v: A1=(1,0), A2=0. Local: A1=(1+w0, w1), A2=(e0,e1). F = ((1+w0)^2+w1^2)(e0^2+e1^2).
Floc2 = ((1+w0)**2 + w1**2)*(e0**2+e1**2)
print("F at v=(A1=(1,0),A2=0):", sp.expand(Floc2))
print("Near 0: ((1+w0)^2+w1^2)->1 unit; F ~ unit*(e0^2+e1^2). lambda_v = rlct(e0^2+e1^2)=1. Again =1.")
print()
print("OBSERVATION: for (2,1,2) r=0 the fibre is a single GL1 gauge orbit (rank-1 factorizations of 0),")
print("so ALL fibre points are GL-equivalent => SAME local RLCT = 1. The inequality is EQUALITY everywhere.")
print("This is a DEGENERATE test for strictness. Need a case with genuinely DIFFERENT-depth strata.")
