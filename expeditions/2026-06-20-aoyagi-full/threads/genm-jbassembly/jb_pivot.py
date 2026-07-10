import numpy as np
from math import lgamma, log

# ============================================================
# CLAIM 1: the CRUDE lower-bound model  h = a^2||v||^2 + ||Gamma||^2
#   over the box, with a a SEPARATE variable, has rlct = 1/2 + d_Gamma/2.
#   (Thom-Sebastiani in disjoint var-groups (a,v) and Gamma.)
#   For vslice (3,3,3,4): d_v = 3 (boundary-1 row in R^3), d_Gamma = 4 (2x2 corank block).
#   => rlct(crude) = 1/2 + 4/2 = 5/2.
# Verify the 1-D reductions exactly (each factor's abscissa).
# ============================================================
# rlct(a^2||v||^2) over (a,v), d_v vars:  int a^{-2c} da * int ||v||^{-2c} dv
#   = finite iff c<1/2 and c<d_v/2  => min = 1/2 (for d_v>=1).
# rlct(||Gamma||^2), d_G vars: c < d_G/2.
# Thom-Sebastiani (disjoint var groups): rlct(f(x)+g(y)) = rlct f + rlct g.
d_v, d_G = 3, 4
rlct_crude = 0.5 + d_G/2.0
print("CLAIM1 crude-model rlct (a variable):", rlct_crude, " (expect 2.5)")

# Numeric cross-check of the disjoint-sum abscissa for h = a^2 r_v^2 + r_G^2
# reduce to radial: v -> (u_v, sphere S^{d_v-1}), Gamma -> (u_G, sphere).
# I = int_a int_{u_v} int_{u_G} (a^2 u_v^2 + u_G^2)^{-c} u_v^{d_v-1} u_G^{d_G-1}
# We estimate the abscissa by testing finiteness of the (a,u_v,u_G) 3-D integral on [0,1]^3.
def crude_int(c, N=400):
    # deterministic grid on (a, uv, uG) in (0,1]^3, midpoint rule with the radial jacobians folded
    xs = (np.arange(N)+0.5)/N
    a = xs[:,None,None]; uv = xs[None,:,None]; uG = xs[None,None,:]
    val = (a**2*uv**2 + uG**2)**(-c) * uv**(d_v-1) * uG**(d_G-1)
    return val.mean()  # /1 (box vol 1); grows -> inf near abscissa
for c in [2.3, 2.45, 2.5, 2.55, 2.7]:
    print(f"  crude 3D grid c={c}: I~{crude_int(c):.4g}")

# ============================================================
# CLAIM 3: the full front-factor  A0 -> 0  direction.
#   F = frobSq(A0 * A1 * A2) ~ ||A0 * (A1 A2)||^2. Near A0=0 (A1,A2 generic),
#   F ~ ||A0||^2 * (bounded below by sigma_min(A1A2)^2 >0 generic).
#   dim(A0) = M0*M1 = 9. rlct of ||A0||^2 quadratic in 9 vars = 9/2.
#   => pivot/scale (A0->0) branch threshold = 9/2 > 7/2 (non-binding).
M0,M1 = 3,3
print("CLAIM3 A0->0 branch threshold:", (M0*M1)/2.0, " (expect 4.5, > 3.5)")
