import numpy as np
# Full RATIONAL SVD chart for A1 (s x z), s=2, z=3.
# U in O(2): tangent-half-angle (stereographic) tau.
# V in Stiefel V_2(R^3): v1 in S^2 via stereographic (p,q); v2 in S^1 within v1^perp via stereographic (r).
# Sigma = diag(sig1,sig2).  6 params -> A1 (6 entries).  Confirm Jacobian factorization.

def U2(tau):
    d=1+tau*tau
    cs=(1-tau*tau)/d; sn=2*tau/d
    return np.array([[cs,-sn],[sn,cs]])

def sphere2_stereo(p,q):   # S^2 minus north pole, stereographic from R^2
    d=1+p*p+q*q
    return np.array([2*p, 2*q, p*p+q*q-1])/d

def orthonormal_basis_of_perp(v1):
    # deterministic rational-ish complement (Gram-Schmidt of e-vectors); for Jacobian we only need smoothness
    # pick two vectors, GS against v1
    e=np.eye(3)
    # choose the axis least aligned
    k=np.argmin(np.abs(v1))
    a=e[k]-np.dot(e[k],v1)*v1; a/=np.linalg.norm(a)
    b=np.cross(v1,a); b/=np.linalg.norm(b)
    return a,b

def A1_of(params):
    tau,sig1,sig2,p,q,r=params
    U=U2(tau)
    v1=sphere2_stereo(p,q)
    a,b=orthonormal_basis_of_perp(v1)
    # v2 in circle spanned by (a,b), stereographic param r
    dr=1+r*r
    v2=((1-r*r)/dr)*a + (2*r/dr)*b
    V=np.column_stack([v1,v2])          # 3x2, orthonormal columns
    Sig=np.diag([sig1,sig2])
    A1=U@Sig@V.T                        # 2x3
    return A1.reshape(-1)

def numjac(f,x,h=1e-6):
    n=len(x); f0=f(x); m=len(f0); J=np.zeros((m,n))
    for i in range(n):
        xp=x.copy(); xm=x.copy(); xp[i]+=h; xm[i]-=h
        J[:,i]=(f(xp)-f(xm))/(2*h)
    return J

rng=np.random.default_rng(1)
print("Rectangular rational SVD chart (s=2,z=3): |detJ| vs  sig1*sig2*|sig1^2-sig2^2| * w(frame)")
print("If |detJ|/(sig1*sig2*|sig1^2-sig2^2|) depends ONLY on frame params (not on sig), factorization holds.")
for _ in range(6):
    tau=rng.normal(); sig1,sig2=sorted(rng.uniform(0.5,2,2),reverse=True); p,q,r=rng.normal(size=3)*0.6
    x=np.array([tau,sig1,sig2,p,q,r])
    dj=abs(np.linalg.det(numjac(A1_of,x)))
    charge=sig1*sig2*abs(sig1**2-sig2**2)      # sig^{z-s}=sig^1 each, times Vandermonde |s1^2-s2^2|
    print(f"  sig=({sig1:.3f},{sig2:.3f}) frame=({tau:+.2f},{p:+.2f},{q:+.2f},{r:+.2f})  |detJ|/charge={dj/charge:.5f}")

print("\nVary ONLY sig (fix frame): |detJ|/charge must be constant:")
tau,p,q,r=0.4,0.3,-0.2,0.5
for _ in range(5):
    sig1,sig2=sorted(rng.uniform(0.5,2.5,2),reverse=True)
    x=np.array([tau,sig1,sig2,p,q,r])
    dj=abs(np.linalg.det(numjac(A1_of,x)))
    charge=sig1*sig2*abs(sig1**2-sig2**2)
    print(f"  sig=({sig1:.3f},{sig2:.3f})  |detJ|/charge={dj/charge:.6f}")
