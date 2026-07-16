import numpy as np
rng=np.random.default_rng(3)
# 3x3 product Y=P@Z, P,Z uniform [-1,1]^{3x3}. Probe density shape on rank-drop strata
# restricted to sigma_max(Y)~1 (the shell). Discriminator (same as Test3): conditional
# density of sigma_min as sigma_min->0 at sigma_max~1 => constant ADDITIVE increase per
# halving = LOG (alpha=0, escape ok); constant RATIO = power (alpha>0, escape at risk).
N=120_000_000
def prod3(N):
    P=rng.uniform(-1,1,(N,3,3)); Z=rng.uniform(-1,1,(N,3,3))
    return np.einsum('nij,njk->nik',P,Z)
# chunk to save memory
chunks=8; per=N//chunks
smin_all=[]; smid_all=[]; smax_all=[]
for _ in range(chunks):
    Y=prod3(per)
    s=np.linalg.svd(Y,compute_uv=False)  # (per,3) desc
    smax_all.append(s[:,0]); smid_all.append(s[:,1]); smin_all.append(s[:,2])
smax=np.concatenate(smax_all); smid=np.concatenate(smid_all); smin=np.concatenate(smin_all)
sel=(smax>0.9)&(smax<1.3)
print(f"=== 3x3 product: rank-2 stratum (sigma_min->0 at sigma_max~1), n_sel={sel.sum()} ===")
sm=smin[sel]
edges=np.array([0.002,0.004,0.008,0.016,0.032,0.064,0.128,0.256])
h,_=np.histogram(sm,bins=edges); w=np.diff(edges); mids=0.5*(edges[:-1]+edges[1:])
dens=h/w/sel.sum(); prev=None
for m,d in zip(mids,dens):
    r=(d/prev) if prev else float('nan'); add=(d-prev) if prev else float('nan')
    print(f"  sigma_min~{m:.4f}: dens~{d:7.3f}  ratio={r:.3f}  add_change={add:+.3f}")
    prev=d
print("  [LOG => add_change ~ const (>0, growing as smin->0); POWER => ratio ~ const >1]")

# rank-1 stratum (codim 4): both smid,smin -> 0 at smax~1. Probe density of smid at fixed
# smin small. Coarser (rarer). Check whether joint (smid,smin) small has power.
print("\n=== 3x3 product: rank-1 stratum proxy: P(sigma_2 < e AND sigma_3 < e | sigma_1~1) vs e ===")
base=sel
for e in [0.2,0.1,0.05,0.025,0.0125]:
    cnt=((smid<e)&(smin<e)&base).sum()
    frac=cnt/base.sum()
    print(f"  e={e:.4f}: P(rank<=1 within e)~{frac:.3e}   frac/e^4={frac/e**4:.3f}  frac/e^3={frac/e**3:.3f}")
print("  [codim-4 locus: if measure ~ e^4 * (poly log), the density there is integrable-mild;")
print("   frac/e^4 -> const (up to log) supports mild (no strong extra power).]")
