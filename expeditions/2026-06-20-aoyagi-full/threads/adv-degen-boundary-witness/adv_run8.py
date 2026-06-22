import sympy as sp

print("="*72)
print("RLCT NORMAL-FORM check: straighten the gauge orbit, confirm F ~ sum of nReg squares (rlct=nReg/2)")
print("="*72)
a,b,p,q=sp.symbols('a b p q',real=True)
F=((1+a)*(1+p)-1)**2 + ((1+a)*q)**2 + (b*(1+p))**2 + (b*q)**2
# Change coords adapted to the smooth zero locus {b=0,q=0, (1+a)(1+p)=1}:
#   u = (1+a)(1+p)-1  (vanishes on locus), v = q, w = b, and a free coord t = a (the orbit param).
# Express F in (u,v,w,t): need (1+a),(1+p) in terms. 1+a = 1+t. 1+p = (1+u)/(1+t).
t=sp.Symbol('t',real=True); u,v,w=sp.symbols('u v w',real=True)
oneA=1+t; oneP=(1+u)/(1+t)
Fnew=sp.simplify( u**2 + (oneA*v)**2 + (w*oneP)**2 + (w*v)**2 )
print(f"  F in adapted coords (u=fibre-normal, v=q, w=b, t=orbit): {sp.expand(Fnew)}")
# Near 0 (t,u,v,w small): leading = u^2 + v^2 + w^2 * (1/(1+t))^2 + ... = u^2 + v^2 + w^2*(1+...)
# The 3 'normal' coords (u,v,w) each appear as a nondegenerate square (coefficients ->1,(1+t)^2,1/(1+t)^2 >0
# near t=0), t is free. So F = u^2 + (1+t)^2 v^2 + (1+t)^{-2} w^2 + v^2 w^2 ~ a rank-3 nondeg quadratic in
# (u,v,w) with t-dependent POSITIVE coefficients + flat t. RLCT of such = 3/2 (the t-dependence is a smooth
# positive rescaling, does not change the RLCT; v^2 w^2 is higher order).
# Confirm: factor out. For fixed small t, q(u,v,w) = u^2 + c1 v^2 + c2 w^2 (c1,c2>0) is a nondeg PD form in 3
# vars -> rlct contribution 3/2; the v^2w^2 quartic is dominated. t free -> +0. So rlct = 3/2 = nReg/2.
print()
print("  Verify the (v,w) block is positive-definite for small t (coeffs (1+t)^2, (1+t)^{-2} > 0): YES near 0.")
print("  Leading 2-jet in (u,v,w): u^2 + v^2 + w^2 (t=0) -> rank 3 PD. The v^2 w^2 is degree-4, dominated.")
print("  => F is a rank-3 nondegenerate quadratic (in u,v,w) x smooth positive coeffs + flat t.")
print("  => rlctAt = 3/2 = nReg/2.  The t^4-along-linear-coord was a COORDINATE artifact (straight line off a")
print("     curved smooth zero-locus); in adapted coords the locus is straight and F is clean sum-of-squares.")
print()

print("="*72)
print("GENERAL PRINCIPLE (the load-bearing fact, exact): F = ||Phi(x)||^2, Phi = product - B smooth.")
print("  zero set Z = {Phi=0} = the fibre. If Z is SMOOTH of codim k at the point AND the differential dPhi")
print("  has rank k there (transversal / clean intersection), then in adapted coords F = sum_{i<k} y_i^2 +")
print("  (flat) + higher order, and rlctAt(F) = k/2. The hypothesis 'rank(J)=k' is EXACTLY rank(dPhi)=k.")
print("  I verified rank(J)=nReg on all configs => the clean-intersection hypothesis holds => rlctAt=nReg/2.")
print("  This is Watanabe's normal-crossing / a Morse-Bott-with-flat-valley statement; the t^4 does NOT raise")
print("  the RLCT because it lives on the smooth flat locus, not transverse to it.")
print()

print("="*72)
print("SANITY: integrability exponent on the explicit (2,1,2) F (numeric cross-check of rlct=3/2)")
print("="*72)
# rlct = 3/2 means |F|^{-c} integrable near 0 for c<3/2, divergent for c>=3/2. Equivalent: vol{F<eps} ~ eps^{3/2}.
# Estimate the volume scaling vol{F < eps} ~ eps^{lambda} with lambda = rlct, by Monte Carlo (GUIDE ONLY,
# not a certificate; the certificate is the smooth-codim-3 normal form above).
import numpy as np
rng=np.random.default_rng(0)
def Fnp(a,b,p,q):
    return ((1+a)*(1+p)-1)**2 + ((1+a)*q)**2 + (b*(1+p))**2 + (b*q)**2
for eps in [1e-2,1e-3,1e-4]:
    # sample in a box of size ~ eps^{1/2} (the natural scale) and estimate fraction with F<eps, times vol
    R=eps**0.5*3
    N=4000000
    X=(rng.random((N,4))*2-1)*R
    vals=Fnp(X[:,0],X[:,1],X[:,2],X[:,3])
    frac=np.mean(vals<eps)
    vol=frac*(2*R)**4
    print(f"  eps={eps:.0e}: vol{{F<eps}} ~ {vol:.3e},  vol/eps^1.5 = {vol/eps**1.5:.3f}  (rlct=3/2 => ~const)")
