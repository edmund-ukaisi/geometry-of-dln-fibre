import numpy as np
from scipy import integrate

# ============================================================
# Codex's coupled-recursion one-step integral (the "sum-not-min" mechanism):
#   J(h) = int_{||x||<=1} (||x||^2 + h)^{-c} dx,  x in R^q.
#   For c > q/2:  J(h) ~ C * h^{q/2 - c}   as h -> 0.
#   => peeling a q-dim block shifts the residual exponent c -> c - q/2.
# Verify the h-scaling exponent for q=4, c=3 (so q/2=2, expect J~h^{2-3}=h^{-1}).
# ============================================================
def J(h, q, c):
    f = lambda r: (r**2 + h)**(-c) * r**(q-1)
    val,_ = integrate.quad(f, 0, 1, limit=200)
    return val  # * surface area const (drops out of exponent)
q, c = 4, 3.0
hs = np.array([1e-2,1e-3,1e-4,1e-5])
Js = np.array([J(h,q,c) for h in hs])
# fit log J vs log h
slope = np.polyfit(np.log(hs), np.log(Js), 1)[0]
print(f"one-step: q={q},c={c}: measured h-exponent={slope:.4f}  expected q/2-c={q/2-c:.4f}")

# ============================================================
# TWO-block composition = the additive threshold (3+2+1=6 -> 7/2 vslice check,
#   but here the abstract coupled model): peel block1 (dim q1) then block2 (dim q2)
#   with the SHARED residual, threshold should be (q1+q2)/2, NOT min(q1/2,q2/2).
#   Model: F = ||x||^2 * U1 + ||y||^2 * U2, x in R^q1, y in R^q2, U1,U2>0 units.
#   This is a nondeg quadratic in (x,y) => rlct = (q1+q2)/2  [ADD, sum-not-min].
# Numeric abscissa of int (||x||^2+||y||^2)^{-c} over unit box (U1=U2=1):
# ============================================================
def box_int(c, q1, q2, N=200000, seed=0):
    rng = np.random.default_rng(seed)
    X = rng.uniform(-1,1,size=(N,q1)); Y = rng.uniform(-1,1,size=(N,q2))
    val = (np.sum(X**2,1)+np.sum(Y**2,1))**(-c)
    return val.mean()*(2**(q1+q2))
q1,q2=4,3   # vslice corank(4)+row(3): expect abscissa (4+3)/2 = 7/2
for c in [3.0, 3.4, 3.5, 3.6, 4.0]:
    vals=[box_int(c,q1,q2,seed=s) for s in range(4)]
    print(f"  two-block abscissa test c={c}: mean~{np.mean(vals):.4g} std~{np.std(vals):.2g}")
print("  (expect finite/stable below 3.5, blowing up/high-variance above)")
