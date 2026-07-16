import numpy as np
rng=np.random.default_rng(0)
# DECISIVE: is the HONEST inner charge integral J(Z)=∫_{A_cor∈box} det(Q_b Q_b^T)^{-a/2} dA_cor bounded as Z->rank-drop?
# Case (4,4,4,4), u=3, a=b=1: Z=A2 is 4x4 (M2=n=4), A_cor 1x4, Q_b=A_cor@A2 (1x4), charge=||A_cor A2||^{-1}.
# Compare well-conditioned A2 vs A2 with a small singular value s4=eps.  If J stays Theta(1) -> diagbfix right (my +inf WRONG).
def J(A2, N=2_000_000):
    v=rng.uniform(-1,1,size=(N,1,4))
    Qb=v@A2[None]                 # N x 1 x 4
    nrm=np.sqrt(np.sum(Qb*Qb,axis=(1,2)))
    vol=2.0**4
    return vol*np.mean(nrm**(-1.0))
# build A2 = U diag(s) V^T with controlled smallest singular value
U,_=np.linalg.qr(rng.standard_normal((4,4)))
V,_=np.linalg.qr(rng.standard_normal((4,4)))
print("J(A2) as smallest singular value s4 -> 0  (a=b=1, k=4):")
for s4 in [1.0,0.3,0.1,0.03,0.01,0.003,0.001]:
    S=np.diag([1.0,0.8,0.6,s4])
    A2=U@S@V.T
    print(f"  s4={s4:7.4f}  det+={np.prod([1,.8,.6,s4]):.6f}  residual det(A2A2^T)^-1/2={abs(np.linalg.det(A2))**-1:9.2f}   J(A2)={J(A2):8.4f}")
print()
print("If J stays ~O(1) while residual->inf, the shrinking pushforward box compensates -> inf L=0 -> my +inf lower bound INVALID.")
