"""
V3 (clean structural fact): full-collapse boundedness reduces to  minAdm(deep_chain) >= minAdm(M).
    Full-collapse (k=rho) codim-with-charge = min( u*rho, kappa_rho - a*b ),
    kappa_rho = CR(deep,0) = minAdm(deep). Need >= minAdm(M)-a*b, i.e. (charge branch)
    minAdm(deep) - a*b >= minAdm(M) - a*b  <=>  minAdm(deep_chain) >= minAdm(M).
Verify minAdm((M2,...,M_last)) >= minAdm(M) exhaustively at binding strict-shell cuts.

V2 (RLCT onset): direct numerical RLCT of the ASSEMBLED local integrand at a rank-(rho-k) drop
    integrand = tau^{-a*max(0,k-d)} * (|y|^2 + tau^2 |W_lost|^2)^{-q},  measure dy dW_lost tau^{kappa_k-1}dtau,
    y in R^{u(rho-k)}, W_lost in R^{u k}.  Predicted onset q* = C*(k)/2 = min(u*rho, G(k))/2.
Confirm the integral is finite just below q* and divergent just above (MC over the ball + tau-radial quadrature).
"""
import itertools, numpy as np
from deepgate_scan import CR, minAdm, binding_cut, analyze

# ---------- V3 ----------
def v3(arity_widths, Wmax):
    nwidths=arity_widths
    fails=[]; cnt=0; mindiff=None
    for M in itertools.product(*([range(1,Wmax+1)]*nwidths)):
        deep = M[2:]
        tstar,r=binding_cut(M)
        for j in range(1,r):
            u=tstar+j; a=M[0]-u; b=M[1]-u
            if a<1 or b<1: continue
            cnt+=1
            diff = minAdm(deep) - minAdm(M)
            if mindiff is None or diff<mindiff: mindiff=diff
            if diff < 0:
                fails.append((M,u,minAdm(deep),minAdm(M)))
    return cnt, fails, mindiff

# ---------- V2 ----------
def assembled_integral(u, rho, b, a, kappa_k, k, q, Nmc=400000, delta=1.0, seed=0):
    """MC over y,W_lost in balls + tau radial in (0,delta]; returns integral estimate (finite if converges)."""
    rng=np.random.default_rng(seed)
    d = rho-b
    ny = u*(rho-k); nw = u*k
    charge_exp = -a*max(0,k-d)
    # radial tau: integrand has tau^{kappa_k-1+charge_exp} * inner(tau).  Sample tau log-uniform, reweight.
    # We estimate I = \int_0^delta tau^{kappa_k-1} tau^{charge_exp} f_tau dtau, f_tau = E_{y,W in ball}[(|y|^2+tau^2|W|^2)^{-q}] * vol
    # Use fine tau grid (quadrature) x MC over (y,W).
    ntau=240
    taus = np.linspace(delta/ntau, delta, ntau)
    dtau = delta/ntau
    # MC sample y (ball radius delta) and W (ball radius delta)
    m = Nmc
    # sample in cube then it's fine for onset (ball vs cube doesn't change exponent)
    Y = rng.uniform(-delta, delta, size=(m, ny)) if ny>0 else np.zeros((m,0))
    Wv = rng.uniform(-delta, delta, size=(m, nw))
    y2 = (Y**2).sum(1) if ny>0 else np.zeros(m)
    w2 = (Wv**2).sum(1)
    total=0.0
    for tau in taus:
        loss = y2 + tau*tau*w2
        loss = np.maximum(loss, 1e-300)
        inner = np.mean(loss**(-q))            # E over the cube (vol factor const, irrelevant for finiteness)
        total += (tau**(kappa_k-1+charge_exp)) * inner * dtau
    return total

def v2_onset(M, u, k, seed=0):
    info = analyze(M,u)
    rho=info['rho']; a=info['a']; b=info['b']
    kappa_k = CR(info['deep'], rho-k)
    Cstar = info['recs'][k-1][4]   # C*(k)
    qstar = Cstar/2.0
    # scan q around qstar: finite below, divergent above (integral grows with resolution / large)
    qs = [qstar-0.4, qstar-0.15, qstar+0.15, qstar+0.4]
    vals=[]
    for q in qs:
        if q<=0: vals.append(('q<=0',None)); continue
        v = assembled_integral(u,rho,b,a,kappa_k,k,q,Nmc=200000,delta=1.0,seed=seed)
        vals.append((round(q,3), v))
    return Cstar, qstar, vals

if __name__=="__main__":
    print("=== V3: minAdm(deep_chain) >= minAdm(M) at binding strict shells ===")
    for nw, Wmax in [(4,9),(5,7),(6,5)]:
        cnt, fails, mindiff = v3(nw, Wmax)
        print(f"  {nw}-width chains widths 1..{Wmax}: {cnt} cuts; violations minAdm(deep)<minAdm(M): {len(fails)}; min(minAdm(deep)-minAdm(M))={mindiff}")
        for f in fails[:5]: print("     FAIL", f)

    print("\n=== V2: assembled-integrand RLCT onset (finite below C*(k)/2, divergent above) ===")
    # pick charge-biting strata to test the charge's effect on the onset
    tests = [((3,3,5,5),1,4),((3,3,5,5),1,5),   # a=b=2, rho=5, d=3: k=4,5 charge; C* capped by u*rho=5
             ((4,4,6,6),2,5),((4,4,6,6),2,6),   # a=b=2, rho=6, d=4: k=5,6 charge
             ((3,3,7,7),1,6),((3,3,7,7),1,7)]   # a=b=2, rho=7, d=5: k=6,7 charge
    for (M,u,k) in tests:
        Cstar,qstar,vals = v2_onset(M,u,k)
        info=analyze(M,u); d=info['d']
        cb = " charge-biting(k>d)" if k>d else ""
        print(f"  M={M} u={u} k={k}{cb}: C*(k)={Cstar} predicted onset q*={qstar}")
        for (q,v) in vals:
            print(f"      q={q}: I={v:.4e}" if isinstance(v,float) else f"      q={q}: {v}")
