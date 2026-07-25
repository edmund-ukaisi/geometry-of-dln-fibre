"""Reconcile decomp-5b (100% MC cover, 903-box) vs sector-count (escape cone).
Decisive point: the escape is at the OUTER sigmaPiv level. A valid chart (pivot p in V={0,1,2,3,20})
requires |x_j| <= R|x_p| for all j in the sigmaPiv center {0..7,20}. The shear-slot witness
x = t*e_4 + eps*(others) has x_4=t but x_p<=eps for all p in V, so |x_4/x_p| = t/eps > R once
eps < t/R. So NO valid chart (any box R) covers it. MC misses it because the escape region has
solid angle ~ (1/R)^{|V|}, astronomically tiny for R=903."""
from fractions import Fraction as F
V=[0,1,2,3,20]; W=[4,5,6,7]; center={0,1,2,3,4,5,6,7,20}
R=903
def covered_by_valid_at_sigmaPiv(x, R):
    """Is x in some valid sigmaPiv chart's image with source box radius R? (outer-level necessary cond:
    exists p in V with |x_j|<=R|x_p| for all j in center\{p}, and |x_p|<=R.)"""
    for p in V:
        if abs(x[p])>R: continue
        if all(abs(x[j])<=R*abs(x[p]) for j in center if j!=p):
            return True, p
    return False, None
def covered_by_any_at_sigmaPiv(x, R):
    for p in sorted(center):
        if abs(x[p])>R: continue
        if all(abs(x[j])<=R*abs(x[j2 if False else p]) for j in center if j!=p):
            # simpler: |x_j|<=R|x_p|
            pass
        if all(abs(x[j])<=R*abs(x[p]) for j in center if j!=p):
            return True, p
    return False, None

print(f"Box radius R = {R} (decomp-5b's 903-box).")
for eps_den in [10, 1000, 100000, 10**7]:
    x={k:F(0) for k in range(21)}
    x[4]=F(1,2)                      # x_4 = 1/2 (a shear-slot coord dominates)
    eps=F(1,eps_den)
    for p in [0,1,2,3,20]: x[p]=eps  # tiny valid coords
    vc,vp = covered_by_valid_at_sigmaPiv(x, R)
    ac,ap = covered_by_any_at_sigmaPiv(x, R)
    ratio = abs(x[4]/x[0]) if x[0]!=0 else 'inf'
    print(f"  eps=1/{eps_den:<8}: x_4/x_V = {ratio}  covered-by-VALID({{0,1,2,3,20}})={vc}  covered-by-ANY(incl 4,5,6,7)={ac} via pivot {ap}")
print()
# solid-angle of the escape region within ball: fraction of directions with max_W > R*max_V
import random; random.seed(1); N=2_000_000; esc=0
for _ in range(N):
    xv=[random.gauss(0,1) for _ in range(9)]  # coords for {0,1,2,3,4,5,6,7,20}: idx 0-3->V part,4-7->W,8->20
    maxV=max(abs(xv[0]),abs(xv[1]),abs(xv[2]),abs(xv[3]),abs(xv[8]))
    maxW=max(abs(xv[4]),abs(xv[5]),abs(xv[6]),abs(xv[7]))
    if maxW> R*maxV: esc+=1
print(f"MC estimate of escape-cone solid-angle fraction (max_W > {R}*max_V), N={N}: {esc/N:.2e}")
print("  -> astronomically tiny for R=903: a finite-sample MC (10^4-10^6) NEVER hits it -> false 100%.")
print("  BUT the cone is scale-invariant + nonempty (exact witness above) -> the valid subset does NOT cover.")
