"""
incidence estimate — exact corner blow-up + pivot-energy scaling probes.
NO shell yet; parts (A),(B). Exact where load-bearing, MC/quadrature as guide.

Objects (L=0 leaf):
  M=(M0,M1,M2); cut u; a=M0-u, b=M1-u.
  Qp : u x M2 (pivot product, fn of z).  Qb=A_cor : b x M2.  hsQ=(Qp;Qb) : (u+b) x M2.
  Pi_b = proj onto row(Qb).
  q = c' - ab/2.
  target inner integrand (front block P:uxu, B:uxb, C:axu):
     det(Qb Qb^T)^(-a/2) * ( ||P Qp + B Qb||_F^2 + ||C Qp (I-Pi_b)||_F^2 )^(-q)
"""
import numpy as np
from numpy.linalg import svd, det, pinv
rng = np.random.default_rng(0)

# ---------- (A) exact corner: M=(2,2,3), u=1,a=b=1, Qp=e1, Qb=(1,t2,t3) -------------
# analytic reduction gave: LHS_corner ~ B0(q) * [∫_0^δ s^{2-2q} ds]*[∫ ρ^{2-2q}dρ]
# in c':  ∫ s^{3-2c'} ds  (q=c'-1/2). converges iff c'<2=T1.  verify the *radial* exponent numerically.

def corner_inner_frontintegral(s, q, N=200000):
    # ∫_{p,beta,gamma in [-1,1]} ((p+beta)^2 + beta^2 s^2 + gamma^2 s^2/(1+s^2))^(-q)
    p = rng.uniform(-1,1,N); be = rng.uniform(-1,1,N); ga = rng.uniform(-1,1,N)
    val = (p+be)**2 + be**2*s**2 + ga**2*s**2/(1+s**2)
    integ = val**(-q)
    return 8.0*np.mean(integ)   # box volume 2^3

def corner_F_scaling(q):
    # measure F(s) ~ s^{1-2q} slope for small s
    ss = np.array([0.2,0.1,0.05,0.025])
    Fs = np.array([corner_inner_frontintegral(s,q) for s in ss])
    # slope of log F vs log s
    A = np.polyfit(np.log(ss), np.log(Fs), 1)
    return A[0]

print("=== (A) corner front-integral F(s) small-s slope (predict 1-2q) ===")
for cprime in [1.6, 1.8, 1.9]:
    q = cprime-0.5
    slope = corner_F_scaling(q)
    print(f"  c'={cprime}  q={q:.2f}  measured F-slope={slope:+.3f}  predicted 1-2q={1-2*q:+.3f}")

# full corner radial: LHS_corner(c') integrand after A_cor(=t) polar s ds:
#   ∫_0^δ det^(-1/2) F(s) * s ds ,  det=(1+s^2) ~1 ; F(s)~ C s^{1-2q}; integrand ~ s^{2-2q}=s^{3-2c'}
print("\n=== (A) corner radial exponent (predict 3-2c') ===")
for cprime in [1.6,1.8,1.9]:
    q=cprime-0.5
    ss=np.array([0.2,0.1,0.05,0.025])
    g=np.array([ (1+s**2)**(-0.5)*corner_inner_frontintegral(s,q)*s for s in ss])
    A=np.polyfit(np.log(ss),np.log(g),1)
    print(f"  c'={cprime}: measured integrand-slope={A[0]:+.3f}  predicted 3-2c'={3-2*cprime:+.3f}  (converge iff >-1 i.e. c'<2)")

# ---------- (B) pivot-energy scaling for u=2: which conditioning governs? -----------
# E_top(P,B)=||P Qp + B Qb||_F^2 = || [P|B] hsQ ||_F^2, hsQ=(Qp;Qb).
# Question: does  Ipiv := ∫_{[P|B] in box} E_top^{-q}  scale like det(hsQ hsQ^T)^{-u/2}
#           (combined conditioning) or like something in Qp alone (sigma_min(Qp))?
def Ipiv_box(hsQ, u, q, N=400000):
    ub = hsQ.shape[0]  # u+b
    W = rng.uniform(-1,1,size=(N,u,ub))       # rows of [P|B]
    out = np.einsum('nij,jk->nik', W, hsQ)    # N x u x M2
    E = np.sum(out**2, axis=(1,2))
    return (2.0**(u*ub))*np.mean(E**(-q))

def make_hsQ(u,b,M2, sv_Qp, corank_covers_weak=True, seed=None):
    """build Qp (u x M2) with given singular values sv_Qp, Qb (b x M2).
       corank_covers_weak: Qb rowspace contains Qp's smallest right-sing direction (=> hsQ well-cond)."""
    r=np.random.default_rng(seed)
    # right singular vectors: pick orthonormal frame in R^M2
    Z=r.standard_normal((M2,M2)); Uu,_,_=svd(Z); Vr=Uu[:, :]  # cols orthonormal
    # Qp = Up * diag(sv) * Vr[:,:u]^T
    Up,_,_=svd(r.standard_normal((u,u)))
    Sig=np.zeros((u,M2));
    for i in range(u): Sig[i,i]=sv_Qp[i]
    Qp = Up @ Sig @ Vr.T
    # Qb: b rows. either aligned to cover Qp's weakest dir (Vr[:,u-1]) or generic
    if corank_covers_weak:
        base = Vr[:, u-1:u-1+b].T.copy()   # directions incl the weakest
        Qb = base + 0.15*r.standard_normal((b,M2))
    else:
        Qb = r.standard_normal((b,M2))
    hsQ=np.vstack([Qp,Qb])
    return Qp,Qb,hsQ

print("\n=== (B) pivot-integral scaling, u=2,b=1,M2=3, q fixed ===")
q=1.2
for s2 in [1.0,0.3,0.1,0.03]:   # Qp singular values (1.0, s2): cond=1/s2
    # case 1: Qb covers the weak Qp direction  => hsQ well-conditioned (sigma_min(hsQ)~O(1))
    Qp,Qb,hsQ=make_hsQ(2,1,3,[1.0,s2],corank_covers_weak=True,seed=1)
    svh=svd(hsQ,compute_uv=False)
    Ip=Ipiv_box(hsQ,2,q)
    frob=np.sum(Qp**2)
    detG=np.prod(svh[:2]**2)  # (hsQ hsQ^T) has u+b=3 rows but rank<=3; use top singulars
    print(f"  cond(Qp)={1/s2:6.1f} COVERED: sig_min(hsQ)={svh.min():.3f}  Ipiv={Ip:.4e}  frob(Qp)^-q={frob**(-q):.4e}  ratio Ipiv/frob^-q={Ip/frob**(-q):.4e}")
    # case 2: Qb generic (does NOT cover weak dir) => hsQ has small singular value ~ s2 (off-shell/higher flag)
    Qp,Qb,hsQ=make_hsQ(2,1,3,[1.0,s2],corank_covers_weak=False,seed=1)
    svh=svd(hsQ,compute_uv=False)
    Ip=Ipiv_box(hsQ,2,q); frob=np.sum(Qp**2)
    print(f"  cond(Qp)={1/s2:6.1f} GENERIC: sig_min(hsQ)={svh.min():.3f}  Ipiv={Ip:.4e}  frob(Qp)^-q={frob**(-q):.4e}  ratio={Ip/frob**(-q):.4e}")
