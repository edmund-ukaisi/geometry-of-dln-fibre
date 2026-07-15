"""
Verify the ASSEMBLY formula  C*(k) = min(u*rho, G(k)),  G(k)=u(rho-k)+kappa_k - a*max(0,k-d)
via a log-tau-resolved quadrature of the local integrand, on SYNTHETIC parameter sets chosen so
the charge branch G(k) < u*rho is VISIBLE (in-scope DLN cases always cap at u*rho so the charge
never controls the onset -- which is exactly the BOUNDED conclusion; here we stress-test the charge
branch directly to validate the formula).

Local integrand at a k-drop:
   I(q) = \int_0^delta dtau tau^{kappa-1} tau^{-a*max(0,k-d)} * inner(tau),
   inner(tau) = \int_{y in R^{ny}, W in R^{nw}, balls} (|y|^2 + tau^2|W|^2)^{-q},  ny=u(rho-k), nw=u*k.
The tau->0 tail exponent flips sign at 2q = C*(k). We detect divergence by log-tau tail growth.
"""
import numpy as np

def inner_tau(tau, q, ny, nw, rng, m=120000, delta=1.0):
    Y = rng.uniform(-delta,delta,size=(m,ny)) if ny>0 else np.zeros((m,0))
    W = rng.uniform(-delta,delta,size=(m,nw))
    y2 = (Y**2).sum(1) if ny>0 else np.zeros(m)
    w2 = (W**2).sum(1)
    loss = np.maximum(y2 + tau*tau*w2, 1e-300)
    vol = (2*delta)**(ny+nw)
    return np.mean(loss**(-q))*vol

def integral(u,rho,b,a,kappa,k,q, seed=0, delta=1.0, decades=8, per_decade=6):
    """log-tau quadrature from delta down to delta*10^{-decades}."""
    rng=np.random.default_rng(seed)
    d=rho-b; ny=u*(rho-k); nw=u*k; ce=-a*max(0,k-d)
    # log-spaced tau nodes; integrate tau^{kappa-1+ce} inner(tau) dtau via log substitution:
    # dtau = tau dln(tau); integrand_in_lntau = tau^{kappa+ce} inner(tau)
    lnts = np.linspace(np.log(delta), np.log(delta)-decades*np.log(10), decades*per_decade+1)
    dl = abs(lnts[1]-lnts[0])
    tot=0.0; tail_terms=[]
    for lt in lnts:
        tau=np.exp(lt)
        val = tau**(kappa+ce) * inner_tau(tau,q,ny,nw,rng)
        tot += val*dl
        tail_terms.append((tau,val))
    return tot, tail_terms

def onset_test(u,rho,b,a,kappa,k, label=""):
    d=rho-b
    G = u*(rho-k)+kappa - a*max(0,k-d)
    Cstar = min(u*rho, G)
    qstar = Cstar/2.0
    print(f"[{label}] u={u} rho={rho} b={b} a={a} d={d} kappa={kappa} k={k}: "
          f"G(k)={G} u*rho={u*rho} => C*={Cstar}, predicted onset q*={qstar}")
    for q in [qstar-0.5, qstar-0.2, qstar+0.2, qstar+0.5]:
        if q<=0: continue
        tot,tail = integral(u,rho,b,a,kappa,k,q)
        # divergence signal: ratio of last-decade term to first (if growing as tau->0 => diverges)
        t_big = tail[0][1]; t_small = tail[-1][1]
        growth = t_small/max(t_big,1e-300)
        verdict = "DIVERGES(tau->0 grows)" if growth>5 else ("finite" if growth<0.2 else "borderline")
        print(f"     q={q:.2f} ({'below' if q<qstar else 'ABOVE'} q*): I~{tot:.3e}  tail-growth(small/big tau)={growth:.2e}  -> {verdict}")

if __name__=="__main__":
    print("=== SYNTHETIC charge-branch-visible (G<u*rho): does charge lower the onset to G/2? ===")
    # u=1,rho=4,b=1(d=3),a=1,k=4 charge=a*(k-d)=1. Choose kappa small so G<u*rho.
    onset_test(1,4,1,1, kappa=4, k=4, label="charge lowers onset")   # G=0+4-1=3 < u*rho=4 => C*=3 q*=1.5
    onset_test(1,4,1,1, kappa=6, k=4, label="charge, bigger kappa")  # G=6-1=5 > u*rho=4 => C*=4 q*=2.0 (u*rho caps)
    # compare NO-charge counterpart (a=0 style: set k<=d so charge inert) at same kappa
    onset_test(1,4,1,1, kappa=4, k=3, label="no-charge k=d")         # k=3=d, charge 0, G=1*1+4=5>4 => C*=4 q*=2
    print("\n=== control: single-drop k=1 loss-only (design 4.1 analog), charge inert ===")
    onset_test(2,3,1,1, kappa=1, k=1, label="(3,3,3,3)-like k=1")    # u=2,rho=3,b=1,a=1,kappa=1,k=1: G=2*2+1=5,u*rho=6 => C*=5 q*=2.5=T1_q
