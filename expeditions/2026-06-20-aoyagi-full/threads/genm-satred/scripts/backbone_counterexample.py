"""
Reliable INDEPENDENT verification of the load-bearing (2,2,2)@t=1 counterexample
asserted in backbone-cert.md (the "naive backbone is UNSOUND" verdict).
Exact-N arithmetic for minAdm/gate; scipy.quad + analytic power-law criterion for the integrals.
NO Monte Carlo. Withhold-then-check discipline (my error history is on exactly this).
"""
from functools import lru_cache
from math import isinf
import scipy.integrate as si

# ---------- exact-N minAdm recursion ----------
def redChain(t, M):        # (t, M2, ..., M_last), arity-1
    return (t,) + tuple(M[2:])

@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(M)
    if len(M) <= 1:
        return 0
    if len(M) == 2:
        return M[0]*M[1]
    best = None
    for t in range(min(M[0], M[1]) + 1):
        val = (M[0]-t)*(M[1]-t) + minAdm(redChain(t, M))
        best = val if best is None else min(best, val)
    return best

M = (2,2,2)
t = 1
peel = (M[0]-t)*(M[1]-t)
rc = redChain(t, M)
mM = minAdm(M)
mRC = minAdm(rc)
print("=== exact-N arithmetic ===")
print(f"M={M}  minAdm(M)={mM}  (expect 3)")
print(f"t={t}  peelCharge=(M0-t)(M1-t)={peel}  (expect 1)")
print(f"redChain(t,M)={rc}  minAdm(redChain)={mRC}  (expect 2)")

cp = 5/4
gate_M   = cp < mM/2          # c' < 1/2 minAdm(M)
shifted  = cp - peel/2        # c' - peelCharge/2  (= q)
gate_rc  = shifted < mRC/2    # shifted < 1/2 minAdm(redChain)
q = shifted
two_q = 2*q
print(f"\nc'={cp}")
print(f"gate  c'<minAdm(M)/2={mM/2}: {gate_M}")
print(f"q = c'-peelCharge/2 = {q}   (expect 3/4)")
print(f"gate  q<minAdm(rc)/2={mRC/2}: {gate_rc}  (SAFE => naive gate passes)")
print(f"2q (exponent on p and on ||z||) = {two_q}   (expect 3/2)")

# ---------- analytic power-law convergence criteria ----------
# 1D:  ∫_0^1 p^{-s} dp  converges  iff  s < 1
# nD:  ∫_{ball} ||z||^{-s} dz  converges  iff  s < n  (radial: r^{n-1-s})
def conv_1d(s):  return s < 1
def conv_nd(s, n):  return s < n

print("\n=== analytic power-law criteria ===")
print(f"p-integral   ∫_0^1 p^(-{two_q}) dp  : converges? {conv_1d(two_q)}  (s={two_q} >= 1 => DIVERGES)")
print(f"z-integral   ∫_[ball,2D] ||z||^(-{two_q}) dz : converges? {conv_nd(two_q, 2)}  (s={two_q} < 2 => FINITE)")

# ---------- scipy.quad confirmation (finite cutoff eps->0 shows blow-up) ----------
print("\n=== scipy.quad confirmation ===")
for eps in [1e-2, 1e-4, 1e-6, 1e-8]:
    val,_ = si.quad(lambda p: p**(-two_q), eps, 1.0)
    print(f"  ∫_{eps}^1 p^(-3/2) dp = {val:.4f}   (grows ~ eps^(-1/2) -> ∞)")
# z radial in 2D: ∫_0^1 r^(1) * r^(-3/2) dr = ∫_0^1 r^(-1/2) dr  (times 2π)
zr,_ = si.quad(lambda r: r*(r**(-two_q)), 0.0, 1.0)
print(f"  ∫_0^1 r^(1-3/2) dr = {zr:.4f}  finite  (z-factor over disk = 2π*{zr:.4f})")

# ---------- verdict ----------
naive_diverges = (not conv_1d(two_q)) and conv_nd(two_q, 2)
print("\n=== VERDICT ===")
print(f"gate SAFE (naive would proceed): {gate_M and gate_rc}")
print(f"naive factorized model  ∫p^(-2q)dp · ∫||z||^(-2q)dz  =  (DIVERGES)·(FINITE) = ∞ : {naive_diverges}")
print("=> the NAIVE 'absorb invertible pivot p, land in reduced z-box' step is UNSOUND. CONFIRMED." if naive_diverges
      else "=> counterexample DID NOT reproduce -- RECHECK before asserting.")
