#!/usr/bin/env python3
"""Numeric RLCT sanity check (GUIDE ONLY, not a proof).

Confirm two things for a few 3-width waists:
  (a) the DIRECT zero-product loss ||A0 A1||^2 has sublevel-volume threshold ~ minAdm
      (so RLCT = 1/2 minAdm as cited); AND
  (b) the SVD MODEL loss  sum_j sigma_j^2 ||X_j||^2  (X_j in R^x, sigma_j sing vals of A1)
      reproduces the SAME sublevel scaling  -- i.e. the CoV identity ||A0 A1||^2 = sum sig^2||A0 u_j||^2
      is faithful.

Method: Vol{loss < eps} ~ eps^lambda * |log eps|^{mult-1};  slope of log Vol vs log eps -> lambda.
Use a large uniform sample in a box; estimate the exponent from a small-eps window.
"""
import numpy as np

rng = np.random.default_rng(0)

def loss_direct(x, s, z, N, T=1.0):
    A0 = rng.uniform(-T, T, size=(N, x, s))
    A1 = rng.uniform(-T, T, size=(N, s, z))
    P = np.einsum('nij,njk->nik', A0, A1)           # x x z
    return np.sum(P**2, axis=(1, 2))

def loss_svd_model(x, s, z, N, T=1.0):
    # sample A1, take its singular values sigma_j (s of them) and left sing vectors u_j;
    # X_j = A0 u_j.  loss_model = sum_j sigma_j^2 ||X_j||^2 = ||A0 A1||^2 exactly (identity check).
    A0 = rng.uniform(-T, T, size=(N, x, s))
    A1 = rng.uniform(-T, T, size=(N, s, z))
    # SVD of A1 (s x z, s<=z): A1 = U (s x s) Sig V^T
    U, sig, _ = np.linalg.svd(A1, full_matrices=False)   # U: N x s x s, sig: N x s
    Xj = np.einsum('nxs,nsj->nxj', A0, U)  # N x x x s   (column j = A0 u_j)
    normX2 = np.sum(Xj**2, axis=1)         # N x s
    return np.sum((sig**2) * normX2, axis=1)

def est_lambda(loss_vals, eps_list):
    logeps, logvol = [], []
    Ntot = len(loss_vals)
    for eps in eps_list:
        v = np.mean(loss_vals < eps)
        if v > 0:
            logeps.append(np.log(eps)); logvol.append(np.log(v))
    logeps, logvol = np.array(logeps), np.array(logvol)
    k = len(logeps)
    if k < 3:   # MC could not reach the (high-codim) sublevel set
        return float('nan'), None
    sl = np.polyfit(logeps[k//2:], logvol[k//2:], 1)[0]
    return sl, None

def minAdm3(x,s,z): return min((x-t)*(s-t)+t*z for t in range(0,min(x,s)+1))

cases = [(2,1,2),(3,1,3),(3,2,3),(4,3,4)]
N = 4_000_000
eps_list = [3e-2,1e-2,3e-3,1e-3,3e-4,1e-4,3e-5,1e-5]
print("case   minAdm  1/2minAdm | lambda(direct)  lambda(svd-model)   ||identity max rel err||")
for (x,s,z) in cases:
    ld = loss_direct(x,s,z,N)
    lm = loss_svd_model(x,s,z,N)
    # identity check on a fresh small sample
    A0 = rng.uniform(-1,1,size=(2000,x,s)); A1=rng.uniform(-1,1,size=(2000,s,z))
    Pdir = np.sum(np.einsum('nij,njk->nik',A0,A1)**2,axis=(1,2))
    U,sig,_ = np.linalg.svd(A1,full_matrices=False)
    Xj = np.einsum('nxs,nsj->nxj',A0,U); Pmod = np.sum((sig**2)*np.sum(Xj**2,axis=1),axis=1)
    relerr = np.max(np.abs(Pdir-Pmod)/(Pdir+1e-12))
    lam_d,_ = est_lambda(ld, eps_list)
    lam_m,_ = est_lambda(lm, eps_list)
    ma = minAdm3(x,s,z)
    print(f"({x},{s},{z})  {ma:3d}    {ma/2:5.2f}   |  {lam_d:6.3f}         {lam_m:6.3f}          {relerr:.2e}")
print("\n(NUMERIC GUIDE ONLY. lambda ~ 1/2 minAdm expected; sublevel slope biased low by the |log eps|^{m-1}")
print(" multiplicity factor, so lambda_est slightly UNDER 1/2 minAdm is normal. Identity err ~ 0 is the")
print(" load-bearing check: the SVD model loss EQUALS the direct loss.)")
