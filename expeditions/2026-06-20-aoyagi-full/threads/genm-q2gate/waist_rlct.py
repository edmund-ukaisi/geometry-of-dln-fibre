import numpy as np
rng=np.random.default_rng(1)
# (I) for (2,2,2,2) waist: integrand frobSq(P@z0@z1)^{-c'}, P,z0,z1 uniform [-1,1]^{2x2}, P invertible.
# Estimate the RLCT lambda = finiteness threshold of (I) via sublevel volume:
#   V(eps) = P(frobSq(P z0 z1) < eps) ~ C eps^{lambda} (log eps)^{m-1}.  lambda = slope.
# If lambda = 3/2 = minAdm/2, the sigma_max-shell exponent beta = 2*lambda = 3 = minAdm is TIGHT
# (Codex's shell argument reaches the true threshold). A lower lambda would mean an intermediate
# stratum lowers the threshold and the shell argument would NOT reach 3/2.
N=60_000_000
P=rng.uniform(-1,1,(N,2,2)); z0=rng.uniform(-1,1,(N,2,2)); z1=rng.uniform(-1,1,(N,2,2))
Y=np.einsum('nij,njk->nik',np.einsum('nij,njk->nik',P,z0),z1)
f=(Y**2).sum(axis=(1,2))
print("=== (2,2,2,2) waist sublevel volume V(eps)=P(frobSq<eps); slope=RLCT lambda ===")
epss=np.array([3e-2,1e-2,3e-3,1e-3,3e-4,1e-4,3e-5,1e-5])
V=np.array([(f<e).mean() for e in epss])
for e,v in zip(epss,V): print(f"  eps={e:.1e}  V={v:.3e}")
le=np.log(epss); lv=np.log(V)
# local slopes
print("  local slopes d log V / d log eps (-> lambda):")
for i in range(len(epss)-1):
    s=(lv[i]-lv[i+1])/(le[i]-le[i+1]); print(f"    [{epss[i]:.0e},{epss[i+1]:.0e}] slope={s:.3f}")
# overall fit on smallest 5
import numpy as _np
A=_np.polyfit(le[-5:],lv[-5:],1)
print(f"  fit lambda (smallest 5) = {A[0]:.3f}   (expect 3/2=1.5 for tight shell exponent)")
