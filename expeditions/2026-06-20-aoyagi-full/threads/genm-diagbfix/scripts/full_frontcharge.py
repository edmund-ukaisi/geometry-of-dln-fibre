import numpy as np
rng = np.random.default_rng(1)

# FULL frontChargeIntegrand for (4,4,4,4) @ u=3:  a=1,b=1,u=3, M2=M3=4.
# vars: A'0 (3x4), A2 (4x4)[deep], A_cor(1x4), P(3x3 invertible), B12(3x1), C(1x3). box [-1,1].
# Q_p = A'0 @ A2 (3x4); Q_b = A_cor @ A2 (1x4).
# E_top = || P@Q_p + B12@Q_b ||_F^2         (3x4)
# Pi_perp = I4 - Q_b^T (Q_b Q_b^T)^{-1} Q_b (4x4)
# Qtil = Q_p + Pinv@B12@Q_b ; E_tr = || (C@Qtil)@Pi_perp ||_F^2   (1x4)
# charge = ||Q_b||^{-1}   (a=b=1)
# integrand = charge * (E_top+E_tr)^{-q}

def sample_batch(N, q):
    A0 = rng.uniform(-1,1,(N,3,4))
    A2 = rng.uniform(-1,1,(N,4,4))
    Ac = rng.uniform(-1,1,(N,1,4))
    P  = rng.uniform(-1,1,(N,3,3))
    B12= rng.uniform(-1,1,(N,3,1))
    C  = rng.uniform(-1,1,(N,1,3))
    Qp = A0@A2                    # N,3,4
    Qb = Ac@A2                    # N,1,4
    detA2 = np.linalg.det(A2)     # N
    # charge
    nb = np.sqrt((Qb*Qb).sum(axis=(1,2)))   # ||Q_b||
    charge = np.where(nb>0, 1.0/nb, 0.0)
    # E_top
    Etopmat = P@Qp + B12@Qb       # N,3,4
    Etop = (Etopmat*Etopmat).sum(axis=(1,2))
    # Pi_perp (Q_b is 1x4 row): Pi = I - qb^T qb / ||qb||^2
    qb = Qb[:,0,:]                # N,4
    qq = (qb*qb).sum(axis=1)      # N
    # E_tr = || C Qtil Pi_perp ||^2, Qtil = Qp + Pinv B12 Qb
    Pinv = np.linalg.inv(P)       # N,3,3  (P generically invertible)
    Qtil = Qp + Pinv@B12@Qb       # N,3,4
    CQt = C@Qtil                  # N,1,4
    cqt = CQt[:,0,:]              # N,4
    proj = (cqt*qb).sum(axis=1)/np.where(qq>0,qq,1.0)  # N
    cqt_perp = cqt - proj[:,None]*qb                    # N,4  (C Qtil Pi_perp)
    Etr = (cqt_perp*cqt_perp).sum(axis=1)
    loss = Etop+Etr
    integ = charge * np.where(loss>0, loss**(-q), 0.0)
    return integ, np.abs(detA2)

# box volume factor is a constant; we track the MEAN integrand and the contribution binned by |det A2|.
for q in [0.5, 2.0, 4.9, 5.5]:
    tot=0.0; n=0
    # bin by log10|detA2|
    bins = np.array([-8,-3,-2.5,-2,-1.5,-1,-0.5,0,0.5,1.5])
    binsum=np.zeros(len(bins)-1); bincnt=np.zeros(len(bins)-1)
    for _ in range(40):
        integ,d = sample_batch(200000,q)
        tot+=integ.sum(); n+=len(integ)
        ld=np.log10(np.where(d>0,d,1e-30))
        idx=np.digitize(ld,bins)-1
        for k in range(len(bins)-1):
            m=idx==k; binsum[k]+=integ[m].sum(); bincnt[k]+=m.sum()
    mean=tot/n
    print(f"\nq={q}: mean integrand = {mean:.4e}  (finite mean => integrable; box vol const)")
    print("  |detA2| bin           mean-integrand-in-bin   (grows toward det->0 ?)")
    for k in range(len(bins)-1):
        if bincnt[k]>0:
            print(f"   1e{bins[k]:+.1f}..1e{bins[k+1]:+.1f}   {binsum[k]/bincnt[k]:.4e}   n={int(bincnt[k])}")
