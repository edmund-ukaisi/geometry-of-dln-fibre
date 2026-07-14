import mpmath as mp
mp.mp.dps = 40

# Exact 1-D representation of the multi-scale front-B box integral:
#   g(lam) = ∫_{[-1,1]^{p r}} (Σ_i lam_i ‖B_{·i}‖²)^{-c'} dB
#          = 1/Γ(c') ∫_0^∞ s^{c'-1} ∏_i E(s·lam_i)^p ds,
#   E(w) = ∫_{-1}^1 e^{-w t²} dt = sqrt(pi/w)·erf(sqrt(w))   (E(0)=2).
def E(w):
    if w == 0: return mp.mpf(2)
    return mp.sqrt(mp.pi/w)*mp.erf(mp.sqrt(w))

def g(lams, p, cprime):
    lams=[mp.mpf(x) for x in lams]
    def integrand(s):
        prod=mp.mpf(1)
        for lam in lams:
            prod*= E(s*lam)**p
        return s**(cprime-1)*prod
    val = mp.quad(integrand, [0, mp.inf])
    return val/mp.gamma(cprime)

def slope(lams_fn, ts):
    gs=[g(lams_fn(t),p,cprime) for t in ts]
    logs=[mp.log(x) for x in gs]
    logt=[mp.log(t) for t in ts]
    # linear fit
    n=len(ts); sx=sum(logt); sy=sum(logs); sxx=sum(x*x for x in logt); sxy=sum(a*b for a,b in zip(logt,logs))
    m=(n*sxy-sx*sy)/(n*sxx-sx*sx)
    return m, gs

p=3
ts=[mp.mpf('0.01')*2**k for k in range(4)]  # 0.01,0.02,0.04,0.08

for cprime in [mp.mpf('2.6'), mp.mpf('1.2'), mp.mpf('3.4')]:
    r=3
    print(f"\n===== p={p}, r={r},  c'={float(cprime)},  2c'={float(2*cprime)},  d_s(k=1)=p(r-1)={p*(r-1)}, d_s(k=2)=p(r-2)={p*(r-2)} =====")
    # k=1 weak: lam=(t,1,1)
    m,gs=slope(lambda t:[t,1,1], ts); print(f" k=1 weak (t,1,1):        exp = {float(m):+.4f}")
    # k=2 weak both together: (t,t,1)
    m,gs=slope(lambda t:[t,t,1], ts); print(f" k=2 weak (t,t,1):        exp = {float(m):+.4f}   (both scales = t)")
    # k=2 weak, vary one with other fixed small: (t,0.001,1)
    m,gs=slope(lambda t:[t,mp.mpf('0.001'),1], ts); print(f" k=2, vary lam1 (t,1e-3,1): exp = {float(m):+.4f}")
    # k=3 weak all: (t,t,t)
    m,gs=slope(lambda t:[t,t,t], ts); print(f" k=3 weak (t,t,t):        exp = {float(m):+.4f}")
