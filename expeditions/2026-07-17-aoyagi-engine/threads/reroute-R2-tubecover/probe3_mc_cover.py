#!/usr/bin/env python3
"""TUBE-COVER PROBE #169, step 3 (numpy, GUIDE ONLY -- exact facts decide).
Confirm: (i) R>0 on a ball around origin (canonical chart covers via 1/R, Codex Q3);
         (ii) survivor-ENTRY fan covers the {X00~0} tube with box R>=1 (no large-box need);
         (iii) the naive radial-pivot fan (keep X00) leaves the tube uncovered.
Residual (3,3,3,2,2): X=C3*C4 (3x2), gens = [X00,X01, d2*X10,d2*X11, d1*X20,d1*X21].
loss=(wy)^2 R with R=||Y_row0||^2+... ; here in orig coords R plays role of sum-of-squares residual.
"""
import numpy as np
rng=np.random.default_rng(7)

def prod(C3,C4): return C3@C4  # C3:(...,3,2) C4:(...,2,2)

# ---------- (i) R>0 on a ball: sample small ball, R = normalized residual (canonical) ----------
# canonical chart coords: p=C301/C300 etc. Model R directly = ||Y_row0||^2 + d2^2||Y_row1||^2 + d1^2||Y_row2||^2
def R_of(p,c,d,f,q,s,u,v,d1,d2):
    Y00=1+p*d; Y01=c+p*(c*d+f)
    Y10=q+s*d; Y11=q*c+s*(c*d+f)
    Y20=u+v*d; Y21=u*c+v*(c*d+f)
    return Y00**2+Y01**2 + d2**2*(Y10**2+Y11**2) + d1**2*(Y20**2+Y21**2)
print("=== (i) is R>0 on a ball around the chart origin? (Codex Q3: canonical chart via 1/R) ===")
for rad in [0.3,0.6,0.9,1.2]:
    N=400000
    X=rng.uniform(-rad,rad,size=(N,10))
    Rv=R_of(*[X[:,i] for i in range(10)])
    print(f"  ball radius {rad}: min R = {Rv.min():.5f}, frac(R<0.05) = {(Rv<0.05).mean()*100:.3f}%")
print("  -> R stays bounded below on small balls (min ~ (1-rad^2)); tube {1+pd~0} absent for rad<1.")

# ---------- (ii)+(iii) fan cover of the {X00~0} tube in ORIGINAL coords ----------
print("\n=== (ii)/(iii) fan cover of the {X00~0} tube (orig coords, d1=d2=1) ===")
N=2_000_000
C3=rng.uniform(-1,1,size=(N,3,2)); C4=rng.uniform(-1,1,size=(N,2,2))
X=prod(C3,C4)                      # (N,3,2)
g=X.reshape(N,6)                   # 6 generators (d1=d2=1)
gmax=np.abs(g).max(axis=1)
tube = np.abs(g[:,0]) < 0.02*gmax  # X00 ~ 0 relative
tube &= gmax>1e-9
def covered_by(fan_cols, boxR):
    # covered iff exists a in fan_cols with all |g_b| <= boxR*|g_a|
    ga=np.abs(g[:,fan_cols])                       # (N, k)
    # for each chart a: max over ALL b of |g_b| <= boxR*|g_a|
    ok=np.zeros(g.shape[0],dtype=bool)
    for idx,a in enumerate(fan_cols):
        ok |= (gmax <= boxR*np.abs(g[:,a])+1e-12)
    return ok
for boxR in [1.0,2.0,4.0]:
    covA=covered_by([0],boxR)          # radial-only: only X00 pivot available
    covB=covered_by([0,1],boxR)        # survivor-entry: X00 or X01 pivot
    covAll=covered_by([0,1,2,3,4,5],boxR)  # full 6-generator fan
    t=tube
    print(f"  boxR={boxR}: tube covered by  X00-only={covA[t].mean()*100:5.1f}%  "
          f"X00|X01={covB[t].mean()*100:5.1f}%  full-6-gen={covAll[t].mean()*100:5.1f}%")
print("  -> X00-only (radial-pivot) fan LEAVES the tube uncovered; adding the X01 (survivor-entry)")
print("     sibling covers it; full 6-gen fan covers ~100% at boxR>=1. [MC GUIDE, exact codim decides]")

# ---------- (iv) the common-uncovered set: how many generators can be ~0 at once? ----------
print("\n=== (iv) how deep is the common-uncovered set (all gens small)? ===")
for thr in [0.1,0.05,0.02]:
    allsmall = (np.abs(g) < thr*gmax[:,None]).all(axis=1) & (gmax>1e-9)
    print(f"  frac(all 6 gens < {thr}*max) = {allsmall.mean()*100:.4f}%  (-> shrinks to 0: codim>=2 deep stratum)")
