import numpy as np
rng=np.random.default_rng(9)
Zf3=rng.standard_normal((3,3))
# PART1: a=b=2, rho=4->3. S=diag(1,.9,.8,tau). Ch(S)=int_Acor det((A S)(A S)^T)^{-1}. rate as tau->0.
def Ch(tau,N=2_000_000):
    S=np.diag([1.0,.9,.8,tau])
    A=rng.uniform(-1,1,(N,2,4)); M=np.einsum('nij,jk->nik',A,S)
    Gr=np.einsum('nij,nkj->nik',M,M); det=np.maximum(np.linalg.det(Gr),0.0)
    return (2.0**8)*np.mean(det**(-1.0))
print("PART1: Ch(S) as tau=sigma_4->0 (interior a+b=rho=4, approach rank 3):")
print(f"{'tau':>9}{'ln(1/tau)':>10}{'Ch':>10}{'Ch/ln':>9}")
tot=0
for k in range(2,13):
    tau=2.0**(-k); ch=Ch(tau); lni=np.log(1/tau); band=ch*tau*np.log(2); tot+=band
    print(f"{tau:>9.2e}{lni:>10.2f}{ch:>10.2f}{ch/lni:>9.3f}   band(Ch*tau*ln2)={band:.4f}")
print("cumulative int_0 Ch dtau (S-measure~dtau) =",round(tot,4)," finite=>CONVERGES; Ch/ln~const=>LOG blowup")
