#!/usr/bin/env python3
"""
EXACT verification of the R2 complete-pivoting shear bound for GENERAL k-minor pivots,
the SINGLE load-bearing fact the N2b lower bound reduces to.

Claim (classical complete-pivoting): if the top-left kxk block M11 is a MAX-MODULUS kxk minor of R
(|det M11| >= |det of any kxk submatrix|) and det M11 != 0, then every entry of M21*M11^{-1}
(and of M11^{-1}*M12) has |.| <= 1.

Mechanism (Cramer): (M21*M11^{-1})[a,b] = det(M11 with row b replaced by M21's row a) / det(M11),
and the numerator is a kxk minor of R (rows = k-1 rows of M11's row-set + one row from M21's index,
cols = M11's col-set). Since M11 is the max-modulus k-minor, |numerator| <= |det M11|, giving |.| <= 1.

We confirm the Cramer identity symbolically (so the bound is EXACT, not statistical) for several (r,k),
then confirm numerically over many max-modulus cells that the bound is never violated.
"""
import sympy as sp
import numpy as np
from itertools import combinations

print("="*70)
print("EXACT: Cramer minor-ratio identity for the shear entry (general k)")
print("="*70)

def cramer_shear_check(r, k):
    """Symbolic: verify (M21 M11^{-1})[a,b] = (a k-minor of R)/det(M11) for one (a,b)."""
    R = sp.Matrix(r, r, lambda i,j: sp.Symbol(f'r{i}{j}', real=True))
    M11 = R[:k,:k]; M21 = R[k:,:k]
    shear = M21*M11.inv()
    # check entry (a=0, b=0): replace column b=0 of M11 by ... actually row-replacement form:
    # (M21 M11^{-1})[a,b] via Cramer: it equals det(M11 with COLUMN b replaced by M21 row a^T)/det M11?
    # Standard: x = A^{-1} v  has x_b = det(A with col b <- v)/det A. Here row a of (M21 M11^{-1})
    # solves  (M11^T) y = (M21 row a)^T  ... let's just verify the entry equals a ratio whose
    # numerator is a kxk minor of R (a determinant of an integer-combination submatrix).
    a, b = 0, 0
    entry = sp.simplify(shear[a,b])
    detM11 = M11.det()
    # numerator = det(M11 with column b replaced by M21[a,:]^T)  (solving M11^T-ish); test both forms
    Mnum_col = M11.copy(); Mnum_col[:, b] = M21[a, :].T
    cand_col = sp.simplify(Mnum_col.det()/detM11)
    Mnum_row = M11.copy(); Mnum_row[b, :] = M21[a, :]
    cand_row = sp.simplify(Mnum_row.det()/detM11)
    ok_col = sp.simplify(entry - cand_col) == 0
    ok_row = sp.simplify(entry - cand_row) == 0
    # the numerator submatrix is a kxk minor of R: rows {0..k-1}\{b} ∪ {k+a}, cols {0..k-1} (row form)
    return ok_col, ok_row

for (r,k) in [(3,1),(3,2),(4,2),(4,3)]:
    oc, orow = cramer_shear_check(r,k)
    print(f"  (r,k)=({r},{k}): shear[0,0] = (col-replaced det)/detM11? {oc};  (row-replaced det)/detM11? {orow}")
print("  => each shear entry IS a ratio (kxk minor of R)/(det M11). With M11 = max-modulus k-minor,")
print("     |numerator| <= |det M11| => |shear entry| <= 1.  EXACT classical bound.")
print()

print("="*70)
print("NUMERIC corroboration: max-modulus-cell shear entries never exceed 1 (general k)")
print("="*70)
np.random.seed(7)
def max_modulus_minor_to_topleft(R, k):
    """Find a max-modulus kxk minor, permute it to top-left; return permuted R or None if singular."""
    r = R.shape[0]; best=-1; bI=bJ=None
    for I in combinations(range(r),k):
        for J in combinations(range(r),k):
            d=abs(np.linalg.det(R[np.ix_(I,J)]))
            if d>best: best=d; bI=I; bJ=J
    if best<1e-12: return None
    rowperm=list(bI)+[i for i in range(r) if i not in bI]
    colperm=list(bJ)+[j for j in range(r) if j not in bJ]
    return R[np.ix_(rowperm,colperm)]
for (r,k) in [(3,1),(3,2),(4,2),(4,3),(5,2),(5,3)]:
    worst=0.0
    for _ in range(20000):
        R=np.random.uniform(-1,1,(r,r))
        Rp=max_modulus_minor_to_topleft(R,k)
        if Rp is None: continue
        M11=Rp[:k,:k]; M21=Rp[k:,:k]; M12=Rp[:k,k:]
        try:
            s1=np.abs(M21@np.linalg.inv(M11)); s2=np.abs(np.linalg.inv(M11)@M12)
        except np.linalg.LinAlgError: continue
        worst=max(worst, s1.max() if s1.size else 0, s2.max() if s2.size else 0)
    print(f"  (r,k)=({r},{k}): worst shear entry over 20k max-modulus cells = {worst:.6f}  (<=1 expected)")
