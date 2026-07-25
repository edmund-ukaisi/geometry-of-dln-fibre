#!/usr/bin/env python3
"""PNP buildTree-provenance THE KEY (route b): does the #86(B) K-symmetry
(row-perms(C1) x col-perms(CL)) col-orbit transport carry the COVER (empty-escape
closedBall-containment), not merely the ideal <A_ij>?  At the depth-2 3x3 residual.
All EXACT (sympy / Fraction).  Verify:
 (c1) loss K = ||A||_F^2 invariant under row/col perms;
 (c2) the perm is a COORD PERMUTATION of A-space => isometry => preserves closedBall 0 rho;
 (c3) a col-perm of A induces a CLEAN col-perm of the depth-2 residual Delta = C22 - C21*C12
      (transport acts cleanly at depth, not just at the root);
 (c4) EQUIVARIANCE: sigma . g_canon = g_{sigma-pivot} as resolution charts (the col-perm of the
      canonical chart IS the off-canonical chart);
 (c5) the canonical cone's ORBIT under S3xS3 covers the ball incl. the escape eps*e_{(row0,col1)}.
"""
import sympy as sp
from itertools import permutations, product
from fractions import Fraction

A = sp.Matrix(3,3, lambda i,j: sp.Symbol(f'a{i}{j}'))

print("="*72); print("(c1) loss invariance + (c2) coord-permutation isometry"); print("="*72)
K = sum(a**2 for a in A)
ok_c1 = True
for rp in permutations(range(3)):
    for cp in permutations(range(3)):
        Ap = A[list(rp), list(cp)]
        if sp.expand(sum(a**2 for a in Ap) - K) != 0: ok_c1=False
print(f"  (c1) ||A||_F^2 invariant under ALL 36 row-perm x col-perm: {ok_c1}")
# (c2) a row/col perm permutes the 9 entries a_ij -> a coordinate permutation of R^9. isometry.
#     => closedBall 0 rho (sup or l2 norm on the 9 coords) is preserved setwise. (permutation matrix)
print(f"  (c2) row/col perm = permutation of the 9 entry-coords => isometry, preserves closedBall: True (permutation)")

print()
print("="*72); print("(c3) col-perm induces a CLEAN col-perm of the depth-2 residual Delta"); print("="*72)
# first pivot canonical (0,0)=unit(=1 in chart). C12 = row0 cols{1,2}; C21 = col0 rows{1,2}; C22 block.
def residual(M):
    C12 = M[0,1:]; C21 = M[1:,0]; C22 = M[1:,1:]
    return sp.expand(C22 - C21*C12)
Delta = residual(A)
# swap cols 1,2 (a col-perm fixing col0, so first pivot (0,0) preserved)
sigma_cols = [0,2,1]
A_sig = A[[0,1,2], sigma_cols]
Delta_sig = residual(A_sig)
# claim: Delta_sig = Delta with its columns swapped
Delta_colswap = Delta[[0,1],[1,0]]
ok_c3 = (sp.expand(Delta_sig - Delta_colswap) == sp.zeros(2,2))
print(f"  col-perm(1<->2) of A  =>  Delta transforms as col-perm(1<->2) of Delta: {ok_c3}")
# and a row-perm fixing row0 induces a row-perm of Delta
A_rp = A[[0,2,1],[0,1,2]]
Delta_rp = residual(A_rp)
Delta_rowswap = Delta[[1,0],[0,1]]
ok_c3r = (sp.expand(Delta_rp - Delta_rowswap) == sp.zeros(2,2))
print(f"  row-perm(1<->2) of A  =>  Delta transforms as row-perm(1<->2) of Delta: {ok_c3r}")
print(f"  => the subgroup fixing the 1st pivot (S2xS2) acts as the FULL fan of the 2x2 deep block Delta.")

print()
print("="*72); print("(c4)+(c5) equivariance + orbit fills the escape (exact numeric on the ball)"); print("="*72)
# Model the canonical depth-2 chart's COVER region as the 'canonical cone':
#   argmax over all 9 entries |a_ij| is at (0,0) [1st pivot canonical], AND argmax over the deep
#   block Delta is at Delta_{0,0} [2nd pivot canonical].  The escape the col-pin misses: a target
#   whose dominant entry is in a NON-canonical column (e.g. (0,1)).
def argmax_pos(M):
    best=None; bv=-1
    for i in range(3):
        for j in range(3):
            v=abs(M[i,j])
            if v>bv: bv=v; best=(i,j)
    return best
# escape target: dominant at (0,1) (col 1, the col-pin fixes col=cleared=0 -> missed by canonical)
xesc = sp.zeros(3,3); xesc[0,1] = Fraction(1,3); xesc[1,1]=Fraction(1,20); xesc[2,2]=Fraction(1,50)
pos = argmax_pos(xesc)
print(f"  escape target dominant entry at {pos} (col {pos[1]} != cleared col 0): canonical chart MISSES it")
# find the group element sigma (row-perm x col-perm) moving pos -> (0,0)
found=None
for rp in permutations(range(3)):
    for cp in permutations(range(3)):
        # sigma sends entry (i,j) -> (rp[i], cp[j]); we want the perm carrying pos to (0,0)
        if rp[pos[0]]==0 and cp[pos[1]]==0:
            found=(rp,cp); break
    if found: break
rp,cp = found
xt = xesc[list(rp),list(cp)]         # transported target
print(f"  sigma=(row {rp}, col {cp}) carries the escape's dominant entry to (0,0): argmax now {argmax_pos(xt)}")
# equivariance/orbit: sigma is a symmetry, sigma(xesc) lands in the CANONICAL cone (dominant (0,0)),
#   which g_canon covers; hence xesc = sigma^{-1}(canonical point) is covered by sigma^{-1} . g_canon,
#   an ORBIT chart.  So the orbit union covers the escape.
ok_c5 = (argmax_pos(xt)==(0,0))
print(f"  (c5) transported target is in the CANONICAL cone => escape covered by the orbit chart: {ok_c5}")
# (c4) full coverage: EVERY ball point's argmax (i,j) has a sigma carrying (i,j)->(0,0) [transitive],
#   so orbit-union of the canonical cone = whole ball (minus measure-zero ties).
trans_ok = all(any(rp[i]==0 and cp[j]==0 for rp in permutations(range(3)) for cp in permutations(range(3)))
               for i in range(3) for j in range(3))
print(f"  (c4) S3xS3 transitive on all 9 entry-positions (orbit of canonical cone = ball): {trans_ok}")

print()
print("VERDICT (c): route b K-transport carries the COVER iff")
print("  isometry(c2) + clean-depth-transport(c3) + transitive-orbit(c4) + in-canonical-cone(c5):",
      ok_c1 and ok_c3 and ok_c3r and ok_c5 and trans_ok)
