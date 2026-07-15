"""
The det-charge's FULL t-power = pointwise + A_cor-integral degeneration.
Measure  I(t) = \int_{A_cor} det(Q_b Q_b^T)^{-a/2} dA_cor  at a k-drop, Q_b = A_cor * Z,
Z having k singular values ~ t.  Extract the t-power (log-log slope of I(t)).

Compare to:
  (a) pointwise-only prediction:  a*max(0, k-d)                       [what G(k) used]
  (b) corrected prediction incl A_cor-integral degeneration.
Derivation of (b): eigenvalues of G = B_s B_s^T + t^2 B_l B_l^T (b x b), B_s=A_cor S_surv (b x (rho-k)),
B_l=A_cor S_lost (b x k). Effective column dim of the O(1) part is m := rho-k.
Wishart smallest-eigenvalue: charge-integral \int det(G)^{-a/2} dA_cor has t-power
  gamma_charge(k) = a*max(0, k-d)  [pointwise, from the max(0,k-d) forced-small eigenvalues]
                   + max(0, a - (m - b + 1) + 1)*... -> measure it, don't guess.
We MEASURE gamma_charge(k) directly and tabulate.
"""
import numpy as np

def charge_Acor_integral(b, m, k, a, t, Nmc=400000, seed=0):
    """m = rho-k = effective surviving columns of Z. Q_b = A_cor S = [B_s | t B_l], B_s b x m, B_l b x k.
       Integrate det(B_s B_s^T + t^2 B_l B_l^T)^{-a/2} over generic (B_s,B_l) (A_cor image), box measure."""
    rng = np.random.default_rng(seed)
    Bs = rng.uniform(-1,1,size=(Nmc,b,m))
    Bl = rng.uniform(-1,1,size=(Nmc,b,k))
    G = np.einsum('nij,nkj->nik', Bs, Bs) + t*t*np.einsum('nij,nkj->nik', Bl, Bl)
    dets = np.linalg.det(G)
    dets = np.abs(dets) + 1e-300
    vals = dets**(-a/2.0)
    return vals.mean()

def measure_gamma(b, rho, k, a, seed=0):
    m = rho - k                       # effective surviving columns of Z
    ts = np.array([3e-1,1e-1,3e-2,1e-2,3e-3,1e-3])
    Is = np.array([charge_Acor_integral(b,m,k,a,t,seed=seed) for t in ts])
    # slope of log I vs log t (the t-power exponent). I ~ t^{-gamma} => slope = -gamma
    sl = np.polyfit(np.log(ts), np.log(Is), 1)[0]
    return -sl   # gamma_charge

if __name__=="__main__":
    print("Measured charge-integral t-power gamma_charge(k) = -dlogI/dlogt")
    print("vs pointwise prediction a*max(0,k-d), d=rho-b, m=rho-k")
    print(f"{'b':>2}{'rho':>4}{'a':>2}{'k':>3}{'d':>3}{'m':>3} | {'pointwise':>9} {'measured':>9}  note")
    # scenario: rho=5, b=2, a=? choose a so a+b can exceed rho-k in the d-a<k<=d window
    cases=[]
    for (rho,b,a) in [(5,2,2),(5,2,1),(6,3,2),(6,2,3),(5,3,1),(7,3,3)]:
        d=rho-b
        for k in range(1, rho+1):
            m=rho-k
            if m<0: continue
            cases.append((b,rho,a,k,d,m))
    for (b,rho,a,k,d,m) in cases:
        # need m>=0; charge finite requires b<=m+k always (rank Q_b<=min(b,m+k)); det>0 needs enough cols
        # skip if even with t it's structurally 0 (b>m+k=rho) -> rho>=b always here
        pointwise = a*max(0,k-d)
        try:
            g = measure_gamma(b,rho,a,k,a=a) if False else measure_gamma(b,rho,k,a)
        except Exception as e:
            g=float('nan')
        # corrected prediction: pointwise + A_cor-integral Wishart degeneration
        # Wishart: \int det(B_s B_s^T)^{-a/2} over b x m converges iff a+b<=m (k<=d-a). If a+b>m, extra t-power.
        note=""
        if m>=b:  # B_s can be full rank b
            if a+b > m:  # d-a < k <= d : A_cor-integral degenerates even though pointwise charge finite
                note="A_cor-deg (d-a<k<=d)"
        print(f"{b:>2}{rho:>4}{a:>2}{k:>3}{d:>3}{m:>3} | {pointwise:>9} {g:>9.3f}  {note}")
