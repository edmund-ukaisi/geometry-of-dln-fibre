#!/usr/bin/env python3
"""mixdegen_shell_mc.py -- NUMERICAL GUIDE ONLY (float; NOT load-bearing). Fast version."""
import numpy as np, sys
rng=np.random.default_rng(11); M0,M1,M2=3,3,7
def pr(*a): print(*a); sys.stdout.flush()

def lam_quantile(L, ps=(1e-1,3e-2,1e-2,3e-3,1e-3)):
    L=np.sort(np.asarray(L)); N=len(L)
    ts=[L[max(0,int(p*N)-1)] for p in ps]; xs=np.log(np.array(ts)); ys=np.log(np.array(ps))
    return [round((ys[i+1]-ys[i])/(xs[i+1]-xs[i]),3) for i in range(len(xs)-1)]

pr("=== (i) box-measure singular-value suppression of hsQ (3x7): P(sigma<t) ~ t^exp ===")
H=rng.uniform(-1,1,size=(1_500_000,M1,M2)); sv=np.linalg.svd(H,compute_uv=False)
for name,col,pred in [("sigma_min(3rd)",2,"~5 (=n-m+1=7-3+1)"),("sigma_2(2nd)",1,"")]:
    x=sv[:,col]; ts=(0.3,0.1,0.03,0.01); ps=[np.mean(x<t) for t in ts]
    sl=[round((np.log(ps[i+1])-np.log(ps[i]))/(np.log(ts[i+1])-np.log(ts[i])),2) for i in range(len(ts)-1) if ps[i]>0 and ps[i+1]>0]
    pr(f"  {name}: P(<t) {[round(p,5) for p in ps]} -> exponents {sl}  {pred}")

pr("\n=== (ii) integrated shell RLCT via rank-1 band (true box coords) ===")
def gen_shell(nwant, ratio, batch=1_500_000, maxbatch=12):
    keep=[]; tried=0
    for _ in range(maxbatch):
        Hh=rng.uniform(-1,1,size=(batch,M1,M2)); tried+=batch
        s=np.linalg.svd(Hh,compute_uv=False)
        m=(s[:,1]<ratio*s[:,0])&(s[:,2]<ratio*s[:,0])
        if m.any(): keep.append(Hh[m])
        if sum(x.shape[0] for x in keep)>=nwant: break
    return (np.concatenate(keep,0) if keep else np.zeros((0,M1,M2))), tried
for ratio in (0.5,0.4):
    hsQ,tried=gen_shell(4000, ratio)
    if hsQ.shape[0]<400: pr(f"  ratio {ratio}: too few ({hsQ.shape[0]})"); continue
    s=np.linalg.svd(hsQ,compute_uv=False); TperH=1000
    idx=rng.integers(0,hsQ.shape[0],size=hsQ.shape[0]*TperH); Hrep=hsQ[idx]
    T=rng.uniform(-1,1,size=(Hrep.shape[0],M0,M1)); q=np.einsum('nij,njk->nik',T,Hrep)
    L=np.sum(q*q,axis=(1,2)); L=L/np.mean(L)
    pr(f"  ratio {ratio}: kept {hsQ.shape[0]} (accept {hsQ.shape[0]/tried:.1e}), med sig2/sig1 {np.median(s[:,1]/s[:,0]):.2f} sig3/sig1 {np.median(s[:,2]/s[:,0]):.2f}")
    pr(f"     integrated shell slopes(->lambda): {lam_quantile(L)}   (brief~3, absorption~4.5)")

Hoff=rng.uniform(-1,1,size=(3_000_000,M1,M2)); Toff=rng.uniform(-1,1,size=(3_000_000,M0,M1))
q=np.einsum('nij,njk->nik',Toff,Hoff); Lo=np.sum(q*q,axis=(1,2)); Lo=Lo/np.mean(Lo)
pr(f"  OFF-SHELL control slopes(->lambda): {lam_quantile(Lo)}  (expect ~4.5)")
