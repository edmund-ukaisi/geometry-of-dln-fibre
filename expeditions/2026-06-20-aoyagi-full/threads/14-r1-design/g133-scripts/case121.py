"""
Concrete (1,2,1): F = (a1 b1 + a2 b2)^2,  A=(a1,a2) 1x2, B=(b1,b2)^T 2x1, product scalar.
lambdaCore(1,2,1) = 1/2 (admPred min Mval = 1). The forbidden t=(1,1) has Mval=0.

Attack (i) here: does the resolution ever 'see' the t=(1,1) center (Mval 0)? Geometrically t_L=t_2=
rank(AB). On {AB=0}, rank(AB)=0=t_2, so the only strata IN the zero-locus have t_2=0. t=(1,1) means
rank(AB)=1 => AB != 0 => NOT in {F=0}. So the resolution of {F=0} cannot have a center there.

EXACT RLCT of F=(a1 b1 + a2 b2)^2 at 0. F = g^2 with g = a1 b1 + a2 b2 a single bilinear form.
The rlct of g^2 = 2 * (the contribution)... let's compute directly: rlct_0(F) = sup{c : |F|^{-c} integrable
near 0} = sup{c: |g|^{-2c} integrable}. g = a1 b1 + a2 b2 is a NONDEGENERATE quadratic form in 4 vars
(signature (2,2)): the map (a1,a2,b1,b2) -> a1 b1 + a2 b2. Its zero set is a smooth-away-from-0 quadric
cone. The lct of a nondegenerate quadratic form in n variables is n/2 ... wait that's for SOS positive
definite. For an indefinite/smooth quadric g (rank-4 quadratic form), the real log-canonical threshold of
|g| is: rlct_0(|g|^s) ... Let me just compute the integral exponent exactly via the resolution.

Better: directly blow up. g = a1 b1 + a2 b2. This is the equation of a rank-4 quadric (a smooth point at
the cone vertex resolved by one blow-up). Standard fact: for a smooth hypersurface {g=0} with g having an
ordinary double point (nondegenerate quadratic), lct_0(g) = min(1, n/2) where n=#vars... For n=4 vars,
nondeg quadratic g, lct_0(g)=1 (it's <= 1 always for a hypersurface, and =1 here since multiplicity is 2
and 2 <= n=4; lct = min(n/mult-ish)). Actually lct of a quadratic cone x1^2+...+xn^2 (n>=2) is n/2 if we
treat the SOS, but here g is a single polynomial whose zero set is codim 1.

The CLEAN way: rlct of dlnLoss. F is a sum of squares (here one square (AB)^2, plus the structure). The
claimed answer lambdaCore=1/2. Let me VERIFY 1/2 by exact integration of |F|^{-c} = |g|^{-2c} near 0 and
finding the threshold c.
"""
import sympy as sp

a1,a2,b1,b2 = sp.symbols('a1 a2 b1 b2', real=True)
g = a1*b1 + a2*b2
F = g**2
print("F =", sp.expand(F))

# Resolve {g=0}: g = a1 b1 + a2 b2. Blow up at origin via chart a1 = u (pivot), then a2=u*x2? No --
# g is bilinear in (a) and (b). The rlct of a NONDEGENERATE bilinear pairing a.b on R^k x R^k:
# substitute polar: the variety {a.b=0} is the incidence; rlct of |a.b|^{-s}.
# Cleanest exact route: 1-D reduction. Fix generic direction; |g|^{-2c} integrable near 0 in R^4
# iff 2c < (codim contribution). For a quadratic form q of rank r in n vars, the lct of |q| is:
#   lct(q) = min(1, r/2) for the COMPLEX threshold of a single quadratic poly? No.
# For REAL: rlct_0(|q|) where q nondeg rank n: the integral int |q|^{-s} over a ball converges iff
#   s < 1 (since {q=0} is codim 1, a hypersurface; near a smooth point of the hypersurface |q|~|coord|,
#   giving threshold 1; the cone vertex 0 is the only singular point and contributes a milder condition).
# So sup{s: |q|^{-s} integrable} = 1 for n>=2 nondeg quadratic (the smooth-locus codim-1 condition binds).
# Hence with s=2c: 2c<1 => c<1/2 => rlct_0(F)=1/2. MATCHES lambdaCore(1,2,1)=1/2.
# Let me CONFIRM the threshold 1 for |g|^{-s} by an exact 1-var slice + a blow-up at the vertex.

# Blow-up at vertex 0 in R^4, chart a1=u, a2=u*p, b1=u*q, b2=u*r  (Jacobian u^3, |Jac|=u^3).
u,p,q,r = sp.symbols('u p q r', real=True, positive=True)
g_chart = (u*1)*(u*q) + (u*p)*(u*r)  # a1=u,b1=u q,a2=u p,b2=u r
g_chart = sp.expand(g_chart)
print("g in vertex-blowup chart:", g_chart, " = u^2 *", sp.simplify(g_chart/u**2))
# g_chart = u^2 (q + p r). |F|^{-c}=|g|^{-2c}= u^{-4c} (q+pr)^{-2c}; |Jac|=u^3.
# Integrand: u^{3-4c} * (q+pr)^{-2c}. u-integral near 0 converges iff 3-4c > -1 => c<1.  -> u-divisor ratio 4/4=1?
# Wait: the u-exceptional divisor: order of F along it = 4c exponent vs Jac 3 => threshold (3+1)/4=1 for c (in |F|^{-c}).
# So the VERTEX blow-up gives u-divisor threshold 1, and the residual (q+pr) is a SMOOTH quadric (rank-2-ish)
# whose own threshold is 1 (codim-1 smooth). min = 1. So rlct_0(|g|) = 1, rlct_0(F=g^2): |F|^{-c}=|g|^{-2c},
# threshold in c is 1/2. => rlct_0(F)=1/2 = lambdaCore. CONFIRMED.
print()
print("rlct_0(|g|) = 1 (codim-1 smooth quadric binds);  rlct_0(F=g^2) = 1/2 = lambdaCore(1,2,1). CONFIRMED.")
print("The t=(1,1) (Mval=0) center lies OFF {F=0} (rank(AB)=1 => AB!=0), so the resolution never blows it up.")

# numeric sanity: Monte-Carlo threshold (GUIDE ONLY) for c where int |F|^{-c} diverges
import numpy as np
rng=np.random.default_rng(0)
def mc(c, R=0.3, N=4_000_000):
    X=(rng.random((N,4))*2-1)*R
    gg=X[:,0]*X[:,2]+X[:,1]*X[:,3]
    val=np.abs(gg)**(-2*c)
    return val.mean()*(2*R)**4
for c in [0.40,0.45,0.49,0.50,0.51,0.55]:
    print(f"  [MC guide] c={c}: mean integrand estimate {mc(c):.3e}")
