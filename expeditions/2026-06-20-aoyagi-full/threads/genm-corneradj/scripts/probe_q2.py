import numpy as np
rng = np.random.default_rng(777)

# Q2: honest COUPLED object.  Integrate over BOTH A_cor (b x n) and S (n x p) in boxes,
# plus a loss factor frobSq(Delta S)^{-c'} with Delta (m x n) also in a box.
# Test whether S-integration and/or the loss factor rescue the edge divergence.
#
# Edge params: b=2, a=2, rho=3.  Take n=p=3 so S is 3x3 (generically rank 3), A_cor 2x3.
# Loss: Delta is (say) 1x3, frobSq(Delta S) = |Delta S|^2, exponent c'.  Pick small c'.
#
# By Tonelli the integrand det((A S)(A S)^T)^{-a/2} * frobSq(Delta S)^{-c'} factors:
#   I = int_S [ int_A det(...)^{-a/2} dA ] * [ int_Delta frobSq(Delta S)^{-c'} dDelta ] dS
#     = int_S Ch(S) * Loss(S) dS.
# We probe the JOINT front  J = int_S int_A det((AS)(AS)^T)^{-a/2}  (dyadic-shell mass),
# and separately whether multiplying by Loss(S) (a bounded-ish positive weight) changes the octave scaling.

def joint_front_shells(b,a,n,p, N=8_000_000, kmax=24, with_loss=False, cprime=0.3, m=1):
    A = rng.uniform(-1,1,size=(N,b,n))
    S = rng.uniform(-1,1,size=(N,n,p))
    P = np.einsum('nij,njk->nik', A, S)          # A S : b x p
    G = np.einsum('nij,nkj->nik', P, P)          # Gram b x b
    det = np.maximum(np.linalg.det(G), 0.0)
    w = det**(-a/2.0)
    volA=(2.0)**(b*n); volS=(2.0)**(n*p)
    vol = volA*volS
    if with_loss:
        D = rng.uniform(-1,1,size=(N,m,n))
        DS = np.einsum('nij,njk->nik', D, S)     # m x p
        fro2 = np.sum(DS**2, axis=(1,2))
        fro2 = np.maximum(fro2, 1e-300)
        w = w * fro2**(-cprime)
        vol *= (2.0)**(m*n)
    masses=[]
    for k in range(kmax):
        hi=2.0**(-k); lo=2.0**(-(k+1))
        mask=(det>lo)&(det<=hi)
        if mask.sum()==0:
            masses.append((k,0.0,0)); continue
        mm=vol*w[mask].sum()/N
        masses.append((k,mm,int(mask.sum())))
    return masses

for (tag,kw) in [('JOINT FRONT b=2,a=2,n=p=3 (S free, no loss)', dict(b=2,a=2,n=3,p=3)),
                 ('JOINT FRONT+LOSS c=0.3', dict(b=2,a=2,n=3,p=3,with_loss=True,cprime=0.3)),
                 ('JOINT FRONT INTERIOR b=2,a=2,n=p=4 (predict converge)', dict(b=2,a=2,n=4,p=4))]:
    print('='*66); print(tag)
    ms=joint_front_shells(**kw)
    for (k,mm,ns) in ms:
        print(f'  k={k:>2}  shell-mass={mm:>12.4f}  nsamp={ns:>8}')
