"""
brickdbuild's sharp crux: does incidence-locus codim -> Jacobian -> land q EXACTLY at 1/2*codim?
Corner M=(2,2,3): loss (dropping bounded det-Gram) L = xi^2 + |t|^2 |rho|^2,
  xi=p+beta (1-dim), rho=(beta,gamma) (2-dim front-soft), t=(t2,t3) (2-dim A_cor incidence).
Claim: {L=0} = {xi=0,t=0} U {xi=0,rho=0}, each codim 3; RLCT_q = 3/2 = codim/2 = T1_q.
Verify: (a) the exact iterated-polar value ~ 1/(3-2q)^2 (double pole, LHS alone);
        (b) codim 3 = C_{0,0} from the general formula;
        (c) radial: int r^{(codim-1)-2q} dr = int r^{2-2q} dr finite iff q<3/2 <=> int r^{3-2c'} dr, c'<2=T1.
Also: do det-Gram and transverse-Schur monomialize SIMULTANEOUSLY (minor chart separates det D from X)?
"""
import numpy as np
from scipy import integrate

# (a) exact iterated polar of int_{5d} (xi^2+|t|^2|rho|^2)^{-q}, boxes ~ [-1,1], predict ~1/(3-2q)^2
def corner5d(q, d=1.0):
    # int dxi int_0^d s ds int_0^d w dw (xi^2 + s^2 w^2)^{-q}, xi in [-d,d]
    def fiber(s,w):
        A=s*w
        if A<1e-12: return 0.0
        val,_=integrate.quad(lambda xi:(xi*xi+A*A)**(-q),-d,d,limit=80)
        return val
    val,_=integrate.dblquad(lambda w,s: s*w*fiber(s,w), 1e-4,d, 1e-4,d, epsabs=1e-8,epsrel=1e-6)
    return 2*np.pi*2*np.pi*val   # angular

print("=== (a) corner LHS (fixed z) ~ 1/(3-2q)^2 double pole; check (3-2q)^2 * I ~ const ===")
for q in [1.0,1.2,1.35,1.42]:
    I=corner5d(q)
    print(f"  q={q}: I={I:.4e}  (3-2q)^2 * I = {(3-2*q)**2 * I:.4e}  [const => double pole at q=3/2]")

# (b) codim = C_{0,0} = u*b + M0*u  for (2,2,3)@u=1
M0,M1,M2,u=2,2,3,1; a=M0-u; b=M1-u; d=M2-b
C00 = u*b + M0*0 + (M0-0)*(u-0-0) + 0*(d-0)
print(f"\n(b) C_00 for (2,2,3)@u=1 = u*b+M0*u = {u*b}+{M0*u} = {C00}  (= incidence-locus codim)")
print(f"    1/2*codim = {C00/2}  = T1_q = T1-ab/2 = {0.5*(min((M0-s)*(M1-s)+s*M2 for s in range(3)))-a*b/2}")

# (c) radial forms
print("\n(c) radial: int r^{(codim-1)-2q}dr = int r^{2-2q}dr, finite iff q<codim/2=3/2")
print("    equivalently int r^{3-2c'}dr (c'=q+1/2), finite iff c'<(codim+ab)/2 = (3+1)/2 = 2 = T1")
for cprime in [1.5,1.9,2.0,2.1]:
    e=3-2*cprime
    print(f"    c'={cprime}: r^{{{e:+.1f}}} -> {'finite' if e>-1 else 'DIVERGES'}")

# (d) simultaneous monomialization: minor chart Qb=D[I|X] separates det D (Gram) from X (incidence).
#     verify det(Qb Qb^T) = det(D)^2 * det(I+X X^T)  (so Gram singularity is |det D|, X-independent factor is a UNIT)
print("\n=== (d) minor chart: det(QbQb^T)=det(D)^2*det(I+XX^T) — Gram sing in |det D| only, separate from incidence X ===")
rng=np.random.default_rng(0)
for _ in range(3):
    b,dd=2,3
    D=rng.standard_normal((b,b)); X=rng.standard_normal((b,dd))
    Qb=D@np.hstack([np.eye(b),X])
    lhs=np.linalg.det(Qb@Qb.T)
    rhs=np.linalg.det(D)**2*np.linalg.det(np.eye(b)+X@X.T)
    print(f"    det(QbQb^T)={lhs:.6f}  det(D)^2 det(I+XX^T)={rhs:.6f}  match={np.isclose(lhs,rhs)}")
