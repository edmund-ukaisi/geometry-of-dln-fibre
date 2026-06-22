# Is the codim-1 first-factor stratum {rank C1 = 1} a REAL threshold divisor, or harmless?
# The core ‖C1 C2‖^2 along {rank C1 = 1}: if the PRODUCT C1 C2 is nonzero there, core > 0 = a UNIT,
# blowing up creates NO threshold-relevant divisor (the integrand |core|^{-c} is bounded). The divisor
# only bites where core = 0, i.e. on {prod = 0}. So the relevant centers are {rank C1 = s} ∩ {prod=0}.
import sympy as sp, numpy as np
rng=np.random.default_rng(2)

# (2,2,2): C1 rank 1, C2 generic. Is C1 C2 generically nonzero? YES. So {rank C1=1} alone is NOT in
# {prod=0}; the core is a unit there. The blow-up of {rank C1=1} is only threshold-relevant on its
# intersection with {prod=0}, where t_1=rank(C1) refines to an ADMISSIBLE stratum.
# Verify numerically: sample C1 rank-1, C2 generic; fraction with product != 0.
def frac_product_nonzero(M, nsamp=20000):
    M1,M2,M3 = M
    cnt=0
    for _ in range(nsamp):
        # C1 rank 1: outer product
        u=rng.standard_normal((M1,1)); v=rng.standard_normal((1,M2)); C1=u@v
        C2=rng.standard_normal((M2,M3))
        P=C1@C2
        if np.linalg.norm(P)>1e-9: cnt+=1
    return cnt/nsamp

for M in [[2,2,2],[3,3,3],[4,3,2]]:
    print(f"M={M}: P(prod != 0 | rank C1 = 1) = {frac_product_nonzero(M):.4f}  "
          f"=> {{rank C1=1}} generically OFF {{prod=0}}, core is a UNIT there (no threshold divisor)")

print()
# The CORRECT reading: the resolution resolves {prod=0}. Within a first-factor blow-up CHART, the
# strict transform of {prod=0} is the reduced chain's {prod'=0}. The blow-up's exceptional divisor is
# threshold-relevant ONLY where it meets the strict transform = the deeper admissible stratum. So the
# codim-1 {rank C1=1} does NOT contribute a ratio-1/2 divisor; it contributes only through its
# intersection with {prod=0}, which is an admissible stratum of codim Mval >= minAdm.
# CONFIRM: the divisor's k,h are read off core∘φ on the chart, and core∘φ = u^2 · (residual). The
# residual's OWN zero locus (the strict transform) is where the threshold lives. The u-divisor ratio
# is (h+1)/2 with h = codim of the {prod=0}-stratum the blow-up resolves, NOT the raw first-factor codim.
print("KEY: core∘φ = u^2·residual. The u-exceptional ratio uses h = (codim of the {prod=0}-stratum")
print("resolved), not the raw first-factor codim-1. The codim-1 locus is OFF {prod=0} (core=unit there).")
