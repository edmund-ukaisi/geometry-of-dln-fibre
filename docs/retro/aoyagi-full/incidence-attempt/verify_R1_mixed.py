import numpy as np
from scipy import integrate
# R1: mixed stratum for (3,3,N) large-N, cut u=2, j=2, b=1 (b<j => degeneration FORCED into R).
# Coord model at X=0 (Q_b transverse): loss = ||U_{:,1}||^2 + mu^2||U_{:,2}||^2 + tau^2||W||^2,
#   U_{:,1},U_{:,2},W in R^3 (M0=3);  mu=sigma_min(R) (part of z, ->0, ||R||_F=sqrt(1+mu^2)~1 FLOORED);
#   tau=||Y|| small (shell), measure tau^{(N-2)-1} d tau.   T1 = 9/2 for N large (t*=0).
# Inner 9D integral I(mu,tau) via radial (a=||U1||^2,b=||U2||^2,c=||W||^2), 3D-box radial measure ~ s^{1/2} ds.
N=7; T1=4.5
def rad3(s):  # density of ||v||^2 for v uniform in [-L,L]^3, L=1  (approx: exact via convolution; use MC-free approx)
    return s**0.5   # leading small-s behavior (measure of {||v||^2 in ds}) ; box cutoff at s<3
def I(mu,tau,c, Smax=3.0):
    f=lambda a,b,cc:(a+mu**2*b+tau**2*cc)**(-c)*rad3(a)*rad3(b)*rad3(cc)
    val,_=integrate.tplquad(f,0,Smax,0,Smax,0,Smax,epsabs=1e-10,epsrel=1e-7)
    return val
def Psi(mu,c,eps=0.5):
    g=lambda tau: tau**((N-2)-1)*I(mu,tau,c)
    val,_=integrate.quad(g,0,eps,epsabs=1e-10,epsrel=1e-6,limit=100)
    return val
print(f"(3,3,{N}) u=2 j=2 b=1 mixed stratum. T1={T1}. Test Psi(mu) as sigma_min(R)=mu->0, ||R||_F floored ~1.")
for c in [3.5, 4.0, 4.4]:   # all < T1=4.5
    print(f" c'={c} (<T1={T1}):")
    for mu in [0.5,0.2,0.1,0.05,0.02]:
        print(f"    mu={mu:.3f}: Psi={Psi(mu,c):.5g}")
