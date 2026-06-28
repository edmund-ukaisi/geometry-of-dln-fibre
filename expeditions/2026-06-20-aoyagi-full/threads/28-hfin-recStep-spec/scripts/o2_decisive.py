import sympy as sp
import numpy as np
from numpy.random import default_rng

# ============================================================
# THE DECISIVE corank-3 computation. r=3, j=1, M11=R00=1.
# The honest joint integral over the M11-dominant chart:
#   I(c') = ∫_R ∫_{S_bot} frobSq(Sc(R)*S_bot)^{-c'} dS_bot dR    (the Sc-CORE part of the recursion)
# Sc(R) is 2x2, depends on 8 R-coords + the constraint they live in [-1,1] with R00=1 max-modulus.
# S_bot is 2xp.  We test p=3 (corank-3 binding case (3,3,3) -> lambda_{3,3}=7/2; corank-2 sub: lambda_{2,3}=2).
#
# KEY QUESTION (O2, sharpened): is this integral finite for c' < lambda_{2,p}?  And does the
# RECURSION's mechanism (re-blowup Sc=a'R') give a SPECTATOR-UNIFORM bound, i.e. is the inner
# Sc-core integral, AFTER the R-cover, controlled by a corank-2 problem whose constants don't
# depend on the spectators (M12=r01,r02 ; M21=r10,r20)?
# ============================================================

# Step 1: confirm the variable structure. Sc[a,b] = M22[a,b] - M21[a]*M12[b]  (since M11=1).
# Treat the joint (M22-entries, S_bot) with spectators (M12,M21) as PARAMETERS.
# Change of variable in the JOINT (R, S_bot) integral: keep spectators, replace M22 by Sc.
# We showed d(Sc)/d(M22) = Identity at fixed spectators (translation). So:
#   ∫_{M22 in box'} ∫_{S_bot} frobSq(Sc*S_bot)^{-c'} dS_bot dM22
#     = ∫_{Sc in TRANSLATED box} ∫_{S_bot} frobSq(Sc*S_bot)^{-c'} dS_bot dSc      (Jac=1)
# i.e. AT FIXED SPECTATORS, the M22-integral IS a free Sc-box integral (translated). THE PUSHFORWARD
# IS VOLUME-PRESERVING (translation). The translated box [-1,1] - M21[a]*M12[b] contains a neighborhood
# of 0 iff |M21[a]*M12[b]| < 1, which holds on the chart (|spectators|<=1, strict a.e.).
print("=== Sc-pushforward at FIXED spectators is a TRANSLATION (Jacobian = 1) ===")
print("∫_{M22-box} g(Sc(M22,spectators)) dM22 = ∫_{translated Sc-box} g(Sc) dSc.")
print("The translated box = [-1,1]^4 shifted by -M21⊗M12 (entrywise). Volume-preserving.")
print()

# Step 2: THE FREE Sc-BOX core integral.  g_box(spectators, c') = ∫_{Sc in [-1,1]^4 - M21⊗M12} g(Sc) dSc
#   where g(Sc) = ∫_{S_bot in box} frobSq(Sc*S_bot)^{-c'} dS_bot.
# Compare to the FREE box C (the team-lead's "free (r-j)x(r-j) box"): ∫_{C in [-1,1]^4} g(C) dC.
# Since the translated box and [-1,1]^4 are both 4-dim boxes of side 2, and g(Sc) is finite-integrable
# (the corank-2 IH: ∫_{Sc-box}∫_{S_bot} frobSq(Sc*S_bot)^{-c'} = the corank-2 core, finite for c'<lambda_{2,p}),
# the translated-box integral is comparable to the free-box integral UP TO THE TRANSLATION OVERLAP.
# Both boxes have side 2; their intersection with any fixed neighborhood differs only by the shift.
# Crucially g(Sc) is LOCALLY INTEGRABLE and the boxes are bounded -> the ratio is bounded by a constant
# depending only on the box geometry (side 2), INDEPENDENT of the spectators (the shift only moves the box).

# But we must double-check: does the translated box always CONTAIN the singular locus {det Sc=0} region
# the same way? The shift -M21⊗M12 is rank-1, |entries|<=1. The free box [-1,1]^4 contains Sc=0 (center-ish).
# The translated box [-1,1]^4 - shift contains Sc = -shift = -M21⊗M12, a rank-1 (singular) matrix, plus
# a neighborhood. The {det Sc=0} variety passes through both. The integral over EITHER box is the same
# TYPE of corank-2 core, finite at the same threshold. Let's verify NUMERICALLY that
#   sup over spectators of [ box-integral ] / [ free-box-integral ]  is BOUNDED (spectator-uniform).

def core_integral_montecarlo(shift, c, p=3, N=400000, T=1.0, seed=0):
    """g_box = ∫_{Sc in [-1,1]^4 - shift} ∫_{S_bot in [-T,T]^{2xp}} frobSq(Sc*S_bot)^{-c} dS_bot dSc / by MC.
       shift is a 2x2 array (the rank-1 -M21⊗M12 translation; pass 0 for the free box)."""
    rng = default_rng(seed)
    # Sc uniform in [-1,1]^4 then subtract shift  => Sc in [-1-shift, 1-shift]
    Sc = rng.uniform(-1,1,size=(N,2,2)) - shift[None,:,:]
    Sb = rng.uniform(-T,T,size=(N,2,p))
    prod = np.einsum('nij,njk->nik', Sc, Sb)     # (N,2,p)
    fs = (prod**2).sum(axis=(1,2))               # frobSq, (N,)
    # integrand = fs^{-c}; box volumes: Sc-box vol=2^4, S_bot-box vol=(2T)^{2p}
    vol = (2.0**4) * ((2*T)**(2*p))
    with np.errstate(divide='ignore'):
        vals = fs**(-c)
    # MC estimate of the integral (mean * volume); cap inf->large to see divergence trend
    finite = np.isfinite(vals)
    est = vals[finite].mean() * vol
    frac_huge = np.mean(vals > 1e6)
    return est, frac_huge

# lambda_{2,3} = min(2^2/2, min_j(j*3/2 + lambda_{2-j,3}))  -- corank-2, p=3.
# = min(2, [j=1: 3/2 + lambda_{1,3}], [j=2: 3 + lambda_{0,3}=3]) ; lambda_{1,3}=min(1/2, 1*3/2+0)=1/2
# j=1: 3/2 + 1/2 = 2.  So lambda_{2,3} = min(2,2,3) = 2.  Threshold c' < 2 for the corank-2 Sc-core.
c_test = 1.8   # below lambda_{2,3}=2
print(f"=== MC test: corank-2 Sc-core integral, p=3, c'={c_test} (< lambda_(2,3)=2) ===")
free, fh0 = core_integral_montecarlo(np.zeros((2,2)), c_test)
print(f"  free box (shift=0):            integral ~ {free:.4g}  (frac>1e6: {fh0:.2e})")
for (m21,m12) in [((1,0),(1,0)), ((1,1),(1,1)), ((0.9,0.9),(0.9,0.9)), ((1,-1),(1,-1))]:
    shift = -np.outer(np.array(m21), np.array(m12))   # -M21⊗M12
    est, fh = core_integral_montecarlo(shift, c_test, seed=1)
    print(f"  shift=-M21⊗M12, M21={m21},M12={m12}: integral ~ {est:.4g}  ratio~{est/free:.3f}  (frac>1e6: {fh:.2e})")
