import numpy as np
rng=np.random.default_rng(7)
# Robust 2*lct estimator with more samples + wider eps window.
def est(sampler,N=8_000_000):
    d=sampler(N); d=d[d>1e-300]
    eps=np.array([1e-1,1e-2,1e-3,1e-4,1e-5,1e-6,1e-7,1e-8,1e-9,1e-10])
    fr=np.array([(d<e).mean() for e in eps]); ok=fr>200/len(d)
    if ok.sum()<4: return np.nan
    le,lf=np.log(eps[ok]),np.log(fr[ok])
    return 2*np.polyfit(le[-5:],lf[-5:],1)[0]
def prod2(b,m,q):
    def s(N):
        Y=rng.uniform(-1,1,(N,b,m)); A=rng.uniform(-1,1,(N,m,q))
        Q=np.einsum('nij,njk->nik',Y,A); G=np.einsum('nij,nkj->nik',Q,Q)
        return np.abs(np.linalg.det(G))
    return s
print("SCAN two-layer (b,m,q), b<=min(m,q): est 2lct vs min(m,q)-b+1 [=twist] vs q-b+1 [=free]")
print(f"{'(b,m,q)':>12} {'est':>7} {'twist':>6} {'free':>5}  {'m vs q':>8}  match-twist?")
for (b,m,q) in [(1,1,2),(1,1,3),(1,2,3),(1,2,4),(1,3,2),(1,4,2),
                (2,2,3),(2,2,4),(2,3,4),(2,4,3),(2,3,2),(1,2,2),(1,3,3)]:
    if b>min(m,q): continue
    e=est(prod2(b,m,q)); tw=min(m,q)-b+1; fr=q-b+1
    rel="m<q(twist)" if m<q else ("m=q" if m==q else "m>q(=free)")
    tag = "YES" if abs(e-tw)<0.35 else ("~" if abs(e-tw)<0.6 else "NO")
    print(f"{str((b,m,q)):>12} {e:7.3f} {tw:6d} {fr:5d}  {rel:>10}  {tag}")
print()
print("=> Uniform reading: composite threshold = min(m,q)-b+1.")
print("   m>=q: equals free q-b+1.   m<q: STRICTLY below free (twist).")
