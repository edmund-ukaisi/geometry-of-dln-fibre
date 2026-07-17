"""
DECORRELATED verification, part 5 -- the DECISIVE adversarial test of the P-invertibility claim.

The single-factor argument for the a=0 WIDE POWER front-collapse: F is FULL row rank t on the
dominant-minor chart, so the product W = F.A1 rank-drop is governed by the SINGLE matrix A1
(surjective pullback), NOT a 2-matrix product-corank. Concern: in POWER (M2>b) F is coupled
(not integrated separately) and ill-conditioned near rank-deficiency -- does F's VARIATION add a
product-corank singularity?

DECISIVE TEST: compare rlct( ||F.A1||^2 ) with F VARYING over the full-rank box vs F FIXED generic
full-rank (only A1 varies). If EQUAL -> F's variation contributes no extra rank-drop singularity ->
single-factor confirmed. If the varying-F rlct is LARGER (F's rank-drop boundary contributing) ->
product-corank suspected.

We restrict F to the dominant-minor chart numerically by REJECTING F whose leading t x t minor is not
dominant (|det(leading)| >= |det| of every other t x t minor) AND bounded away from 0 by the chart.
"""
import numpy as np
rng = np.random.default_rng(7)
N = 6_000_000

def slope(fvals, eps_grid, lo=2e-4, hi=5e-2):
    fr = np.array([np.mean(fvals < e) for e in eps_grid])
    lg=np.log(eps_grid); lv=np.log(np.maximum(fr,1e-12))
    m=(fr>lo)&(fr<hi)
    if m.sum()<3: m=(fr>1e-4)&(fr<1e-1)
    A=np.vstack([lg[m],np.ones(m.sum())]).T
    s,_=np.linalg.lstsq(A,lv[m],rcond=None)[0]
    return s, fr

eps=np.exp(np.linspace(np.log(1e-6),np.log(1e-1),22))

# Case M=(2,3,3): F 2x3, A1 3x3.  b=M1-M0=1, M2=3 > b  => POWER.
M0,M1,M2=2,3,3
# (i) F FIXED generic full-rank; only A1 varies -> definitively single-matrix in A1
Ffix = rng.standard_normal((M0,M1)); 
A1 = rng.uniform(-1,1,size=(N,M1,M2))
W = np.einsum('ij,njk->nik', Ffix, A1)
f_fix = np.sum(W**2,axis=(1,2))
s_fix,_ = slope(f_fix, eps)
print(f"M=(2,3,3) POWER: rlct(||F.A1||^2), F FIXED generic full-rank : slope ~ {s_fix:.3f}")

# (ii) F VARYING over full-rank box (leading 2x2 minor invertible, |det|>=0.1 chart) + A1 varying
F = rng.uniform(-1,1,size=(N,M0,M1))
lead = F[:,:, :M0]                    # leading 2x2 block
detlead = lead[:,0,0]*lead[:,1,1]-lead[:,0,1]*lead[:,1,0]
chart = np.abs(detlead) >= 0.10       # dominant-minor chart proxy: bounded away from 0
Fc = F[chart]; A1c = rng.uniform(-1,1,size=(Fc.shape[0],M1,M2))
Wc = np.einsum('nij,njk->nik', Fc, A1c)
f_var = np.sum(Wc**2,axis=(1,2))
s_var,_ = slope(f_var, eps)
print(f"M=(2,3,3) POWER: rlct(||F.A1||^2), F VARYING on dom-minor chart: slope ~ {s_var:.3f}  (n={Fc.shape[0]})")

# (iii) CONTROL: F VARYING over FULL box INCLUDING rank-deficient F (no chart) -> would let rank(F)<2
Ffull = rng.uniform(-1,1,size=(N,M0,M1))
A1f = rng.uniform(-1,1,size=(N,M1,M2))
Wf = np.einsum('nij,njk->nik', Ffull, A1f)
f_full = np.sum(Wf**2,axis=(1,2))
s_full,_ = slope(f_full, eps)
print(f"M=(2,3,3) POWER: rlct(||F.A1||^2), F over FULL box (rank drops allowed): slope ~ {s_full:.3f}")
print()
print("PREDICTION (single-factor): (i) FIXED and (ii) CHART-VARYING agree (F full-rank contributes no")
print("rank-drop singularity); the no-chart control (iii) may differ (rank(F)<2 tube would be a 2-matrix")
print("product-corank -- but that tube is EXCLUDED by the dominant-minor chart).")
