#!/usr/bin/env python3
"""
EXACT check that the disjoint-sum recursion threshold equals 1/2*minAdm at the binding corank-r core.

Per the spec, the corank-(r) core frobSq(R*S) (R r x r, S r x p) has resolution threshold
   lambda(r,p) = min( r^2/2 ,  min_{1<=j<=r} ( j*p/2 + lambda(r-j, p) ) ),   lambda(0,p)=0.
Term meanings:
 - r^2/2 : the radial a-axis divisor (|a|^{r^2-1} blow-up, finite iff c' < r^2/2).
 - j*p/2 : the Morse-top block frobSq(M11*P) (full-rank j x p block -> j*p free Morse coords, threshold jp/2).
 - lambda(r-j,p) : recurse on the Schur core frobSq(Sc*Q), corank r-j.

The headline value the upper leg must MATCH (so cover_le gives rlctAtOn >= 1/2*minAdm) is 1/2*minAdm(r,r,p)
for the binding RRR core (n=n=r, p), where minAdm of the depth-2 (r,r,p) core is the t-minimised Mval:
   Mval(t) = (r - t)^2 + p*t,  t in 0..r  (the diag(b) integer program for an (r,r,p) RRR core),
   minAdm = min_t Mval(t),  and the headline threshold is 1/2 * minAdm.
We confirm lambda(r,p) == 1/2 * minAdm(r,r,p) over a grid (the cert claimed 10/10).
"""
from functools import lru_cache
from fractions import Fraction as F

@lru_cache(None)
def lam(r, p):
    if r == 0:
        return F(0)
    best = F(r*r, 2)                       # radial a-axis term r^2/2
    for j in range(1, r+1):
        cand = F(j*p, 2) + lam(r-j, p)     # Morse-top jp/2 + recurse corank r-j
        if cand < best:
            best = cand
    return best

def minAdm_RRR(n, p):
    """depth-2 (n,n,p) RRR core: Mval(t) = (n-t)^2 + p*t, t in 0..n; minAdm = min_t."""
    return min((n - t)**2 + p*t for t in range(0, n+1))

print("="*70)
print("recursion threshold lambda(r,p) vs 1/2*minAdm(r,r,p)  (binding RRR core)")
print("="*70)
print(f"{'(r,p)':>10} {'lambda(r,p)':>14} {'1/2*minAdm':>14} {'match':>7}")
hits = 0; tot = 0
for r in range(2, 7):
    for p in range(2, 8):
        L = lam(r, p)
        M = F(minAdm_RRR(r, p), 2)
        tot += 1; ok = (L == M); hits += ok
        if r in (2,3,4) and p in (2,3,4):
            print(f"{f'({r},{p})':>10} {str(L):>14} {str(M):>14} {str(ok):>7}")
print(f"\n  match rate over r in 2..6, p in 2..7: {hits}/{tot}")
print()
# Spotlight the (3,3,4) binding case
print("(3,3,4): minAdm =", minAdm_RRR(3,4), "-> 1/2*minAdm =", F(minAdm_RRR(3,4),2),
      "; lambda(2,4)[corank-2 core] =", lam(2,4), " (core threshold), and the depth-2 (3,3,4) =",
      "T-block rlct 2 (p=4 Morse) + lambda(2,4) =", F(2) + lam(2,4))
print()
print("INTERPRETATION: the threshold the disjoint-sum recursion produces matches 1/2*minAdm wherever it")
print("matches the VALUE lane's separately-proven inf. The upper leg only needs FINITENESS strictly below")
print("this; the binding term is the MINIMUM over (radial, sum-of-Morse-and-recurse).")
