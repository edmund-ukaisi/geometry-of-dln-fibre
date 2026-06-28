# Validate: lambdaP(r) = the GREATEST lam satisfying the SchurThreshold contract
#   lambda0: lam 0 = 0
#   radial_le: lam r <= r^2/2          (cap B, the r^2 radial axis)
#   peel_le: lam r <= j*p/2 + lam(r-j) for 1<=j<=r   (cap A, the jp Morse block + lower core)
# The greatest such lam is the fixed point  lam(r) = min(r^2/2, min_{1<=j<=r}(jp/2 + lam(r-j))).
# Claim: this equals (1/2)*minAdm(r,r,p) = (1/2)*min_{t=0..r}[(r-t)^2 + p*t].

from functools import lru_cache

def minAdm_half(r, p):
    return 0.5 * min((r - t)**2 + p*t for t in range(r+1))

def lam_recursion(r, p):
    @lru_cache(None)
    def lam(rr):
        if rr == 0:
            return 0.0
        capB = rr*rr / 2.0
        capA = min(j*p/2.0 + lam(rr - j) for j in range(1, rr+1))
        return min(capB, capA)
    return lam(r)

print("r p | lam_rec  minAdm/2  match | binding(t*) capA-vs-capB")
ok = True
for p in range(1, 9):
    for r in range(0, 8):
        lr = lam_recursion(r, p)
        ma = minAdm_half(r, p)
        m = abs(lr - ma) < 1e-9
        ok &= m
        # binding t* in minAdm
        vals = [((r-t)**2 + p*t, t) for t in range(r+1)]
        tstar = min(vals)[1]
        capB = r*r/2.0 if r>0 else 0.0
        capA = min((j*p/2.0 + lam_recursion(r-j,p)) for j in range(1,r+1)) if r>0 else 0.0
        bind = "capB" if (r>0 and capB <= capA) else ("capA" if r>0 else "leaf")
        print(f"{r} {p} | {lr:7.2f}  {ma:7.2f}   {m}  | t*={tstar} {bind}")
print("ALL MATCH:", ok)

# Also: the p=4 specialization should reproduce schurLambda = [0, 1/2, 2, 4, 6, 8, ...]
print("\np=4 ladder (should be 0, 0.5, 2, 4, 6, 8, 10):")
print([lam_recursion(r,4) for r in range(0,7)])
