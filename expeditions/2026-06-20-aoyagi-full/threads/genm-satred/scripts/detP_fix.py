"""
satred DECISIVE TEST: does the pure-frobSq saturated model have an RLCT DROP (lambda_H<lambda_R),
and does a |det P|^{M2} Jacobian factor RESTORE lambda_H = lambda_R?

Rationale: the CoV z0 -> w=P z0 + B12 Acor has dz0 = |det P|^{-M2} dw. If the honest
frontChargeBox integrand carries a |det P|^{+M2} weight (a chart Jacobian), it cancels exactly:
   ∫ frobSq(...)^{-c'} |det P|^{M2} d(...) --CoV--> ∫_P ∫_{w in slab} frobSq(w Zdeep)^{-c'} dw dP
which is clean (<= vol(P) * RMBTF(redChain @ T*)), giving lambda_H = lambda_R.
WITHOUT the weight, the pushforward density rho(w) is singular and lambda_H may drop.

We measure lambda via the volume-scaling slope of the WEIGHTED sublevel measure
   mu_w{F<t} = ∫ 1[F<t] * weight,   slope -> lambda (finiteness threshold of ∫F^{-c'} weight).
Compare weight=1 (pure) vs weight=|det P|^{M2}.
Also part (b): the FULL box RMBTF(1,3,3,3) should have lambda=1.5 (Aoyagi sanity).
"""
import numpy as np
rng = np.random.default_rng(11)

def measure_lambda(sampler, ts, weight_fn=None, N=8_000_000):
    F, W = sampler(N)
    w = np.ones(len(F)) if weight_fn is None else weight_fn(*W)
    tot = w.sum()
    mu = np.array([ (w*(F<t)).sum()/tot for t in ts ])
    lt, lmu = np.log(ts), np.log(np.clip(mu,1e-15,None))
    sl = np.diff(lmu)/np.diff(lt)
    return mu, sl

# ---- honest saturated model, u=1, M2, M3, b=1 ----
def make_honest(u,M2,M3,b):
    def sampler(N):
        P  = rng.uniform(-1,1,(N,u,u)); z0=rng.uniform(-1,1,(N,u,M2))
        B12= rng.uniform(-1,1,(N,u,b)); Ac=rng.uniform(-1,1,(N,b,M2))
        z1 = rng.uniform(-1,1,(N,M2,M3))
        Z = np.einsum('nij,njk->nik',P,z0)+np.einsum('nij,njk->nik',B12,Ac)
        Pr= np.einsum('nij,njk->nik',Z,z1)
        F = (Pr**2).sum((-1,-2))
        detP = np.linalg.det(P)          # (N,)
        return F, (detP,)
    return sampler

def make_full(widths):
    # full box integral RMBTF(widths): prod of all layers
    L1=len(widths)
    def sampler(N):
        As=[rng.uniform(-1,1,(N,widths[i],widths[i+1])) for i in range(L1-1)]
        Pr=As[0]
        for A in As[1:]:
            Pr=np.einsum('nij,njk->nik',Pr,A)
        F=(Pr**2).sum((-1,-2))
        return F, ()
    return sampler

ts = np.array([3e-2,1e-2,3e-3,1e-3,3e-4,1e-4,3e-5])

for (label,u,M2,M3,b,minAdmRed,minAdmM) in [
        ("(1,3,3,3): redMinAdm=3 (lamR=1.5), M-minAdm=3 (thr 1.5)", 1,3,3,1,3,3),
        ("(1,2,2,2): redMinAdm=2 (lamR=1.0), M-minAdm=2 (thr 1.0)", 1,2,2,1,2,2),
        ("(1,2,3,3): redMinAdm(1,3,3)=3 (lamR=1.5), M-minAdm=2 (thr 1.0)", 1,3,3,1,3,2),
    ]:
    print(f"\n=== {label} ===")
    s = make_honest(u,M2,M3,b)
    muP,slP = measure_lambda(s, ts, weight_fn=None)
    s2 = make_honest(u,M2,M3,b)
    muD,slD = measure_lambda(s2, ts, weight_fn=lambda detP: np.abs(detP)**M2)
    print(f"  PURE (weight 1)      small-t slope lambda_H ~ {slP[-1]:.3f}   full: {np.array2string(slP,precision=2)}")
    print(f"  WEIGHTED |detP|^{M2}   small-t slope lambda_H ~ {slD[-1]:.3f}   full: {np.array2string(slD,precision=2)}")
    print(f"    -> lamR={minAdmRed/2}, needed thr=1/2*minAdm(M)={minAdmM/2}")

# sanity: full box RMBTF(1,3,3,3) lambda should be 1.5
print("\n=== SANITY: full box RMBTF(1,3,3,3), Aoyagi lambda=1.5 ===")
s=make_full([1,3,3,3]); mu,sl=measure_lambda(s,ts)
print(f"  slope -> {sl[-1]:.3f}   full: {np.array2string(sl,precision=2)}")
print("=== SANITY: full box RMBTF(1,2,2,2), lambda=1.0 ===")
s=make_full([1,2,2,2]); mu,sl=measure_lambda(s,ts)
print(f"  slope -> {sl[-1]:.3f}   full: {np.array2string(sl,precision=2)}")
