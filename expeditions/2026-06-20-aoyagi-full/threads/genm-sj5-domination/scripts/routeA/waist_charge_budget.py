#!/usr/bin/env python3
"""Route-A waist charge-budget: EXACT verification.

Model (proven CoV, see cert): for a 3-width chain (x,s,z) with s<=z, SVD the deep layer
A1 = U Sigma V^T (s singular values sigma_j). Then
    loss = ||A0 A1||_F^2 = sum_{j=1}^s sigma_j^2 * ||X_j||^2 ,   X_j := A0 u_j in R^x .
On the ordered chamber sigma_1>=...>=sigma_s, the SVD Jacobian is a MONOMIAL:
    dA1 ~ prod_{i<j}|sigma_i^2-sigma_j^2| * prod_j sigma_j^{z-s} d(sigma) dU dV
        ~ prod_j sigma_j^{ h_j },   h_j = (z-s) + 2*(s-j) = z+s-2j   (on ordered chamber).
Each block j: radial sigma_j (power h_j) + Morse deep block X_j in R^x.
Weighted-AM-GM (qPeel) threshold: c'_max = (1/2) * sum_j min(x, h_j+1).
The gate (banked qPeel hyp h_i<=m_i=x-1) is h_j+1<=x; when it fails the block caps at x
(monomial domination sigma^h <= sigma^{x-1} on [0,1]).

CLAIM (load-bearing): sum_{j=1}^s min(x, z+s+1-2j) = minAdm(x,s,z)  for ALL 3-width chains.
"""

def minAdm3(x, s, z):
    return min((x - t) * (s - t) + t * z for t in range(0, min(x, s) + 1))

def routeA_threshold_charge(x, s, z):
    """sum_j min(x, h_j+1), h_j = z+s-2j, j=1..s.  (= 2*c'_max)"""
    return sum(min(x, z + s + 1 - 2 * j) for j in range(1, s + 1))

def h_powers(x, s, z):
    return [(j, z + s - 2 * j, min(x, z + s + 1 - 2 * j)) for j in range(1, s + 1)]

# ---- 1. Exhaustive identity check ----
fails = []
maxw = 9
for x in range(1, maxw + 1):
    for s in range(1, maxw + 1):
        for z in range(s, maxw + 1):   # s<=z (SVD on A1)
            lhs = routeA_threshold_charge(x, s, z)
            rhs = minAdm3(x, s, z)
            if lhs != rhs:
                fails.append((x, s, z, lhs, rhs))
print(f"[1] identity  sum_j min(x, z+s+1-2j) == minAdm(x,s,z)  for s<=z, widths 1..{maxw}")
print(f"    checked {sum(1 for x in range(1,maxw+1) for s in range(1,maxw+1) for z in range(s,maxw+1))} chains, "
      f"violations: {len(fails)}")
if fails:
    for f in fails[:20]:
        print("    FAIL", f)

# ---- 2. Gate analysis on WAISTS (s<min(x,z)) ----
print("\n[2] WAIST per-block gate (h_j+1<=x?) and cap; ordered-chamber single qPeel")
waists = [(x, s, z) for x in range(2, 7) for s in range(1, 6) for z in range(s + 1, 7)
          if s < min(x, z)]
for (x, s, z) in waists:
    hp = h_powers(x, s, z)
    thr2 = routeA_threshold_charge(x, s, z)
    ma = minAdm3(x, s, z)
    gate_fail = [(j, hj) for (j, hj, cap) in hp if hj + 1 > x]
    tag = "CLOSES(=minAdm)" if thr2 == ma else "MISMATCH!!"
    print(f"  ({x},{s},{z}) minAdm={ma:2d}  sum_min={thr2:2d}  {tag}"
          f"  h_j+1={[hj+1 for (_,hj,_) in hp]}  cap={[c for (_,_,c) in hp]}"
          f"  gate_fail_blocks(j,h)={gate_fail}")

# ---- 3. Per-shell (k large sing vals) threshold >= minAdm ? ----
def shell_threshold_charge(x, s, z, k):
    """Shell k: sigma_1..k large (Morse charge x each, no radial sing),
       sigma_{k+1}..s small radial with power h_j=z+s-2j on ordered chamber.
       2*c'_max(shell k) = k*x + sum_{j>k} min(x, h_j+1)."""
    return k * x + sum(min(x, z + s + 1 - 2 * j) for j in range(k + 1, s + 1))

print("\n[3] per-shell 2*c'_max(shell k) >= minAdm for ALL k in 0..s (WAISTS)?")
allok = True
for (x, s, z) in waists:
    ma = minAdm3(x, s, z)
    shells = [shell_threshold_charge(x, s, z, k) for k in range(0, s + 1)]
    ok = all(v >= ma for v in shells)
    binding = [k for k in range(0, s + 1) if shells[k] == ma]
    allok &= ok
    print(f"  ({x},{s},{z}) minAdm={ma:2d} shells(k=0..s)={shells} "
          f"{'OK' if ok else 'SHELL<minAdm!!'} binding_k={binding}")
print(f"  all shells >= minAdm on all tested waists: {allok}")
