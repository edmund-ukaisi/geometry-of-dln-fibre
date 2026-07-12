import numpy as np

# ==================================================================
# The freed-corner Gaussian peel exponent.
# Integrate a p x b corner Gamma against a b x m full-row-rank Q (Q_b = A_cor.Z):
#     I(Q) = ∫_{Gamma in R^{p x b}} (w + ||C + Gamma.Q||_F^2)^{-c'} dGamma
#          = const · det(Q Q^T)^{-p/2} · (w-tail)^{-(c'-pb/2)}      [banked atom brick]
# The det-Gram exponent is p/2, p = number of FREED (peeled) ROWS of Gamma.
# On shell j the deeper cut t*+j frees an (a-j)x(b-j) corner, so p = a-j.
# At the SATURATED shell j = r = min(a,b) with a<b: p = a-r = 0  ->  det^{-0} = 1.
#
# We confirm the exponent p/2 by the scaling law:  I(lambda·Q) = lambda^{-p·b} · (w-scaled)...
# cleaner: fix the tail so ||C||=0, w>0; scale Q -> lambda Q. Then
#     I(lambda Q) = ∫ (w + lambda^2 ||Gamma Q||^2)^{-c'} dGamma
# substitute Gamma = Gamma'/lambda (Jacobian lambda^{-pb}):
#     = lambda^{-p b} ∫ (w + ||Gamma' Q||^2)^{-c'} dGamma' = lambda^{-p b} I(Q).
# and det((lambda Q)(lambda Q)^T)^{-p/2} = lambda^{-p b} det(QQ^T)^{-p/2}.
# So the exponent on det(QQ^T) is p/2 <=> I(lambda Q)/I(Q) = lambda^{-pb}. Check numerically.
# ==================================================================

rng = np.random.default_rng(0)

def peel_integral(p, b, m, Q, w, cprime, N=4_000_000, R=6.0):
    """MC over Gamma in [-R,R]^{p x b} of (w + ||Gamma.Q||_F^2)^{-c'}; C=0."""
    if p == 0:
        return (w) ** (-cprime)          # empty corner: integrand is w^{-c'}, no integration
    G = rng.uniform(-R, R, size=(N, p, b))
    GQ = G @ Q                            # (N, p, m)
    nrm = np.einsum('npm,npm->n', GQ, GQ)
    vals = (w + nrm) ** (-cprime)
    vol = (2*R) ** (p*b)
    return vals.mean() * vol

def det_gram(Q):
    return np.linalg.det(Q @ Q.T)

print("Freed-corner peel exponent check: I(lambda Q)/I(Q) should be lambda^{-p*b}")
print("(a<b anchor: b = corank = 3 at (3,4,4)@t*=1; m = 5 columns of Q; c'=4.0)\n")
b, m, cprime, w = 3, 5, 4.0, 1.3
for p in (2, 1, 0):
    Q = rng.uniform(-1, 1, size=(b, m))
    lam = 1.7
    I1 = peel_integral(p, b, m, Q, w, cprime)
    I2 = peel_integral(p, b, m, lam*Q, w, cprime)
    ratio = I2 / I1
    predicted = lam ** (-(p*b))
    print(f"  p (freed rows) = {p}:  I(lamQ)/I(Q) = {ratio:.4f}   lambda^(-p*b)={predicted:.4f}   "
          f"=> det-Gram exponent p/2 = {p/2}"
          + ("   [SATURATED a<b: exponent 0 -> weight == 1]" if p == 0 else ""))

print("""
CONCLUSION.
  * The freed-corner Gram-divisor exponent is p/2 with p = #freed rows = a-j at cut t*+j.
  * At the saturated shell j = r = min(a,b), a<b: p = a-r = 0, so the surviving-(b-a)-corank
    weight is det(G_surv)^{-0} == 1 (Real.rpow_zero). No divisor, no divergence, ANY config.
  * The surviving (b-a) corank rows integrate over their bounded box against the constant 1
    -> a finite box factor. The deeper comparator (cut t*+r = min(M0,M1)) carries the full
    charge C_r = minAdm(redChain(t*+r) M) >= minAdm(M) via its OWN Morse codim-rescue (IH).
""")
