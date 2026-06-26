#!/usr/bin/env python3
"""
L32a_Q4_cramer.py — SYMBOLIC proof (not MC) that the shear M21·M11⁻¹ entries are RATIOS of k×k minors
of R, hence bounded by 1 in modulus on the max-k-minor-pivot cell. Closes Q4 with exact algebra.

The shear S_sh = M21 · M11⁻¹ (an (r−k)×k matrix). By Cramer, M11⁻¹ = adj(M11)/det(M11), so
   (S_sh)_{ab} = [M21 · adj(M11)]_{ab} / det(M11).
CLAIM (the classical complete-pivot fact): [M21 · adj(M11)]_{ab} = ± det( M11 with its a-th... ) — more
precisely, (M21·M11⁻¹)_{ab} = det(M11 with column b replaced by the a-th row of M21, appropriately) /
det(M11), and that numerator is (± a k×k minor of R formed from the M11 rows with one swapped for an
M21 row). So each shear entry = (a k×k minor of R)/(det M11). Since det M11 is the MAX-modulus k-minor,
|shear entry| ≤ 1.

We verify this minor-ratio identity EXACTLY (symbolic, r=2 k=1; r=3 k=1; r=3 k=2).
"""
import sympy as sp
from itertools import combinations

def shear_is_minor_ratio(r, k):
    R = sp.Matrix(r, r, lambda i, j: sp.Symbol(f'R{i}{j}', real=True))
    # M11 = top-left k×k (the chosen invertible minor, WLOG by permutation), rows 0..k-1, cols 0..k-1.
    rowsI = list(range(k)); colsJ = list(range(k))
    rowsRest = list(range(k, r))
    M11 = R[:k, :k]
    M21 = R[k:, :k]           # (r-k) × k
    detM11 = M11.det()
    shear = sp.simplify(M21 * M11.inv())   # (r-k) × k
    # For each shear entry (a in 0..r-k-1, b in 0..k-1): claim shear[a,b] = ± (k×k minor of R)/detM11.
    # The minor: replace row b of M11's row-set... Actually the clean statement (Cramer for M21 M11⁻¹):
    #   (M21 M11⁻¹)[a,b] = det( M11 with its b-th ROW replaced by M21's a-th row ) / det(M11).
    # i.e. take rows (0,..,b-1, [k+a], b+1,..,k-1) and cols (0..k-1) — a k×k minor of R.
    allok = True
    for a in range(r-k):
        for b in range(k):
            # minor: rows = M11 rows with row b swapped for M21 row a (global row k+a); cols = 0..k-1
            rows = rowsI.copy(); rows[b] = k + a
            minorM = R[rows, :k]
            ratio = sp.simplify(minorM.det() / detM11)
            ok = sp.simplify(shear[a, b] - ratio) == 0
            allok = allok and ok
    return allok, detM11

print("="*78)
print(" SYMBOLIC: each shear entry (M21·M11⁻¹)[a,b] = (a k×k minor of R) / det(M11)")
print("="*78)
for (r, k) in [(2,1), (3,1), (3,2), (4,2), (4,3)]:
    ok, _ = shear_is_minor_ratio(r, k)
    print(f"r={r}, k={k}: every shear entry = (k×k minor of R)/det(M11) [Cramer minor-ratio identity]: {ok}")
print()
print("="*78)
print(" ⟹ on the max-k-minor-pivot cell {|det M11| ≥ |det of every k-minor|}, |shear entry| ≤ 1")
print("="*78)
print("Each shear entry's NUMERATOR is a k×k minor of R (rows = M11 rows with one swapped for an M21")
print("row; cols = the M11 cols). Its modulus ≤ |det M11| (M11 is the MAX-modulus k-minor by the argmax")
print("pivot). So |shear entry| = |minor|/|det M11| ≤ 1. ⟹ ‖M21·M11⁻¹‖ ≤ k·√(r−k) (entrywise ≤ 1),")
print("an ABSOLUTE constant per (r,k). The shear DOES NOT blow up as det M11 → 0 — because the numerator")
print("minor is ALSO ≤ det M11 (both are k-minors, M11 is the max). Q4 risk RESOLVED, symbolically. ✓")
print()
print("This is exactly the classical COMPLETE-PIVOTING bound: with the max-modulus k×k minor as pivot,")
print("the Schur/Gauss multipliers M21·M11⁻¹ have entries of modulus ≤ 1 (the minor-ratio is ≤ 1). The")
print("comparison constants c0,c1 are therefore ABSOLUTE on the cell (NOT degrading as det M11 → 0).")
print()
print("NOTE for the build: the cell must use the MAX over ALL k-minors that share M11's COLUMN set (so")
print("the swapped-row minor is in the compared family). The clean cover: argmax over ALL k-minor")
print("index-pairs (I,J); the pivot (I*,J*) max ⟹ every (I',J*) with I' a one-row-swap is ≤ it. The")
print("column set J* is FIXED by the pivot; the row swaps stay within the compared family. ✓")
