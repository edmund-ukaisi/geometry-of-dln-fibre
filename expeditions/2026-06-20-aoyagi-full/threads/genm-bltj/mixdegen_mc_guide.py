#!/usr/bin/env python3
"""
mixdegen_mc_guide.py  --  NUMERICAL GUIDE ONLY (float; NOT load-bearing).

RLCT lambda via small-loss-volume law  P(L<t) ~ C t^lambda  =>  slope of log(quantile-prob) vs log(quantile-t).
Uses empirical quantiles p in {1e-1..1e-4} (adaptive, reaches the small-t regime for moderate codim).
int L^{-c'} converges iff c' < lambda.

M=(3,3,7), u=2, j=2, b=1.
  (B) pointwise inner at corank-1 hsQ (sigma_min(Qp)->0): expect lambda ~ 3   (= M0(M1-1)/2) -- brief's pointwise '3'
  (C) pointwise inner at full-rank hsQ                   : expect lambda ~ 4.5 (= M0 M1 /2)
  (E) reduced joint decorated loss F=||H~||^2+||Y W||^2  : expect lambda_q ~ 4  (=> c'=4.5=T1), integrated off-shell
  (F) same F but W CONSTRAINED near rank<=1 (shell forces sigma_min(Qp)->0): does lambda_q stay ~4 (absorbed)
      or drop toward 5/2 (brief)?  This directly tests the b<j absorption.
"""
import numpy as np
rng = np.random.default_rng(20260715)

def lam_quantile(L, ps=(1e-1,3e-2,1e-2,3e-3,1e-3,3e-4,1e-4)):
    L=np.sort(np.asarray(L)); N=len(L)
    ts=[L[max(0,int(p*N)-1)] for p in ps]
    xs=np.log(np.array(ts)); ys=np.log(np.array(ps))
    slopes=[(ys[i+1]-ys[i])/(xs[i+1]-xs[i]) for i in range(len(xs)-1)]
    return slopes

M0,M1,M2=3,3,7; u=2; b=M1-u; a=M0-u; d=M2-b; ub=u*b

def inner_L(hsQ_fixed, N):
    T = rng.uniform(-1,1,size=(N,M0,M1))
    prod = np.einsum('nij,jk->nik', T, hsQ_fixed)
    L = np.sum(prod*prod, axis=(1,2)); return L/np.mean(L)

print("=== (B) pointwise inner at corank-1 hsQ (Qp rank1, Qb generic) ===")
uu=rng.standard_normal((2,1)); vv=rng.standard_normal((1,7))
hsQ_c1=np.vstack([uu@vv, rng.standard_normal((1,7))])
print("  rank(hsQ)=",np.linalg.matrix_rank(hsQ_c1)," singvals=",np.round(np.linalg.svd(hsQ_c1,compute_uv=False),3))
print("  slopes(->lambda):",[round(s,3) for s in lam_quantile(inner_L(hsQ_c1,6_000_000))]," expect ~3.0")

print("\n=== (C) pointwise inner at full-rank hsQ ===")
hsQ_full=rng.standard_normal((3,7))
print("  slopes(->lambda):",[round(s,3) for s in lam_quantile(inner_L(hsQ_full,6_000_000))]," expect ~4.5")

print("\n=== (E) reduced joint decorated loss F=||H~||^2+||Y.W||^2, all free (off-shell) ===")
# H~ in R^{ub}=R^2, Y in R^{M0 x u}=R^{3x2}, W in R^{u x d}=R^{2x6}
N=8_000_000
Ht=rng.uniform(-1,1,size=(N,ub))
Y =rng.uniform(-1,1,size=(N,M0,u))
W =rng.uniform(-1,1,size=(N,u,d))
YW=np.einsum('nij,njk->nik',Y,W)
F = np.sum(Ht*Ht,axis=1) + np.sum(YW*YW,axis=(1,2)); F=F/np.mean(F)
print("  slopes(->lambda_q):",[round(s,3) for s in lam_quantile(F)]," expect ~4.0 (=> c'=4.5=T1)")

print("\n=== (F) reduced joint loss F but W forced near rank<=1 (thin shell sliver) ===")
# W = rank1 base + small full perturbation  (mirrors shell forcing sigma_min(Qp)->0)
N=8_000_000
Ht=rng.uniform(-1,1,size=(N,ub))
Y =rng.uniform(-1,1,size=(N,M0,u))
w1=rng.standard_normal((N,u,1)); wv=rng.standard_normal((N,1,d))
Wbase=w1@wv                                  # rank 1
eps=rng.uniform(0,0.15,size=(N,1,1))
W = Wbase + eps*rng.standard_normal((N,u,d))
sv=np.linalg.svd(W,compute_uv=False)         # (N,2)
onshell = sv[:,1] < 0.2*sv[:,0]              # 2nd SV small => near rank 1
Ht,Y,W = Ht[onshell],Y[onshell],W[onshell]
print(f"  near-rank1 W kept: {W.shape[0]}/{N}")
YW=np.einsum('nij,njk->nik',Y,W)
F=np.sum(Ht*Ht,axis=1)+np.sum(YW*YW,axis=(1,2)); F=F/np.mean(F)
print("  slopes(->lambda_q):",[round(s,3) for s in lam_quantile(F)]," brief~2.5(=>c'=3); absorption~>=4(=>c'>=4.5)")
