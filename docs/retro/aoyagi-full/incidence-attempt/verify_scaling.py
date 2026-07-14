import numpy as np
from scipy import integrate

# ---- Claim A: the completed-square 2D radial block integral scales as A_p^{4-2c'} ----
# G(A_p) = int_0^{A_B} int_0^{A_p} (rB^2+rp^2)^{-c'} rB rp drp drB  ~  A_p^{4-2c'} (A_p->0, A_B fixed).
def G(A_p, c, A_B=1.0):
    f=lambda rp,rB:(rB**2+rp**2)**(-c)*rB*rp
    val,_=integrate.dblquad(f,0,A_B, lambda rB:0, lambda rB:A_p, epsabs=1e-12,epsrel=1e-10)
    return val
print("Claim A: G(A_p) ~ A_p^{4-2c'}")
for c in [1.3,1.6,1.9]:
    Aps=np.array([0.1,0.05,0.025,0.0125])
    vals=np.array([G(a,c) for a in Aps])
    slope=np.polyfit(np.log(Aps),np.log(vals),1)[0]
    print(f"  c'={c}: fitted slope={slope:.3f}  predicted 4-2c'={4-2*c:.3f}")

# ---- Claim B: F(r,al,|t|) ~ r^{2-2c'} (from lambda_-^{1-c'}, lambda_- = r^2|t|^2/(al^2+|t|^2)) ----
# Verify F's r-power via the eigen-reduced formula F ~ const * lam_p^{-1} lam_m^{1-c'}, 2D-stiff x 2D-soft.
# Direct: F(r) = int_{box^4} (lam_p(x1^2+x2^2)+lam_m(x3^2+x4^2))^{-c'} ; check d log F/d log r = 2-2c'.
def Fbox(r, al, t, c, L=1.0):
    lam_p = al**2+t**2
    lam_m = r**2*t**2/(al**2+t**2)
    # reduce: int stiff(2D) -> ~ (pi/(lam_p(c-1))) m^{2-2c'} with m^2=lam_m(x3^2+x4^2); then soft 2D.
    inner=lambda rho:(np.pi/(lam_p*(c-1)))*(lam_m*rho**2)**(1-c)*rho  # x3,x4 -> polar rho, measure rho
    val,_=integrate.quad(inner,1e-9,L*np.sqrt(2),epsabs=1e-12,epsrel=1e-9)
    return val
print("Claim B: F(r) ~ r^{2-2c'} (al=1,|t|=1)")
for c in [1.3,1.6,1.9]:
    rs=np.array([0.1,0.05,0.025,0.0125])
    vals=np.array([Fbox(r,1.0,1.0,c) for r in rs])
    slope=np.polyfit(np.log(rs),np.log(vals),1)[0]
    print(f"  c'={c}: fitted r-slope={slope:.3f}  predicted 2-2c'={2-2*c:.3f}")

# ---- Claim C: shell t-integral gives polylog, NOT a power of 1/r ----
# S(r)=int_{|t|: r|t|<eps*al, |t|>? } |t|^{3-2c'} (al^2+|t|^2)^{c'-2} d|t|,  al~O(1). Upper limit ~ eps/r.
# Tail |t|>>al integrand ~ |t|^{-1} -> log. Verify S(r) ~ C + C' log(1/r) (no power).
def S(r, c, al=0.3, eps=0.5):
    tmax=eps*al/r
    f=lambda t:t**(3-2*c)*(al**2+t**2)**(c-2)
    val,_=integrate.quad(f,1e-9,tmax,epsabs=1e-12,epsrel=1e-9,limit=200)
    return val
print("Claim C: shell radial integral S(r) ~ polylog(1/r)  (test: S(r)/log(1/r) -> const)")
for c in [1.6,1.9]:
    for r in [1e-2,1e-3,1e-4,1e-5]:
        s=S(r,c); import math; print(f"  c'={c} r={r:.0e}: S={s:.4g}  S/log(1/r)={s/math.log(1/r):.4g}")
