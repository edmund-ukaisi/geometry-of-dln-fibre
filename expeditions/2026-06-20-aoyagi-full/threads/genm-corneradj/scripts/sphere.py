import numpy as np
rng=np.random.default_rng(2024)
# Verify edgebrick's sphere identity:  int_{S^{ab-1}} frobSq(Omega K)^{-ab/2} dOmega = omega * det(K K^T)^{-a/2}
# i.e. the polar-Gamma "angular charge" IS the divergent det^{-a/2}, NOT a new finite object.
def sphere_int(a,b,K,N=2_000_000):
    G=rng.standard_normal((N,a,b))              # sample Gaussian, project to sphere by normalizing
    fro=np.sqrt(np.sum(G**2,(1,2),keepdims=True))
    Om=G/fro                                    # uniform on S^{ab-1}
    OK=np.einsum('nij,jk->nik',Om,K)            # Omega K : a x q
    val=np.sum(OK**2,(1,2))**(-a*b/2.0)
    return np.mean(val)                          # = (1/|S|) int ... dOmega  (uniform measure)
for (a,b) in [(2,2),(2,3),(3,2)]:
    q=b+1
    K=rng.standard_normal((b,q))                # full row rank b
    detG=np.linalg.det(K@K.T)
    lhs=sphere_int(a,b,K)
    rhs_shape=detG**(-a/2.0)
    print(f"a={a} b={b}: E_Omega[frobSq(OmK)^(-ab/2)] = {lhs:.5f};  det(KK^T)^(-a/2) = {rhs_shape:.5f};  ratio omega = {lhs/rhs_shape:.5f}")
print("\n=> if ratio 'omega' is CONSTANT across different K (same a,b), identity CONFIRMED: angular charge = omega*det^{-a/2}")
# check omega constant across K for fixed (a,b)=(2,2):
a,b=2,2; q=3
for seed in range(4):
    r=np.random.default_rng(seed); K=r.standard_normal((b,q))
    lhs=sphere_int(a,b,K); rhs=np.linalg.det(K@K.T)**(-a/2.0)
    print(f"  (2,2) K#{seed}: omega=lhs/rhs = {lhs/rhs:.5f}")
