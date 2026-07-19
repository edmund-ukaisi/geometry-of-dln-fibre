#!/usr/bin/env python3
# KILL-CONDITION PROBE: does the geometric BIRTH pivot cell (cNodeOf n (offset+p), possibly
# off-diagonal) have to coincide with the divisor's DIAGONAL birth corner (divBirthCoord, used by
# descendant case-1 u-pivots) for the fold-Jacobian = ledger-monomial identity to hold?
#
# Setup: node n0 (root, case-2) blows up a 2x2 residual block with cells {d00,d01,d10,d11}.
# A fan-out copy births divisor D at pivot cell p_birth (we try DIAGONAL d00 and OFF-DIAGONAL d11).
# Child n1 (case-1(1)) merges INTO D. Per uCornerSel, n1's u-pivot is D's divBirthCoord = DIAGONAL
# d00 (fixed by the ledger, independent of the geometric birth pivot). n1's d-block = {e}.
# Ledger (finding-3, per-pivot divCoord): D.divCoord = p_birth ; D.divExp = 4(birth)+1(merge)=5.
# => ledger monomial = z_{p_birth}^{5-1} = z_{p_birth}^4.
import sympy as sp

def chart(point, center, pivot):
    piv = point[pivot]
    out = dict(point)
    for c in center:
        out[c] = piv if c == pivot else piv * point[c]
    return out

def compose(path, cells):
    src = {c: sp.Symbol('z_'+c, real=True) for c in cells}
    pt = dict(src)
    for (center, pivot) in reversed(path):   # deepest first, root last
        pt = chart(pt, center, pivot)
    return src, pt

def jac_det(path, cells):
    src, pt = compose(path, cells)
    order = list(cells)
    J = sp.Matrix([[sp.diff(pt[r], src[c]) for c in order] for r in order])
    return sp.factor(J.det())

cells = ['d00','d01','d10','d11','e']

for p_birth in ['d00','d11']:
    # root case-2, pivot = p_birth (the fan-out copy's blow-up cell)
    # child case-1(1): u-pivot = DIAGONAL d00 (divBirthCoord), d-block {e}; center {d00,e}, pivot d00
    path = [ (['d00','d01','d10','d11'], p_birth),
             (['d00','e'], 'd00') ]
    d = jac_det(path, cells)
    ledger = sp.Symbol('z_'+p_birth, real=True)**4
    match = sp.simplify(d - ledger) == 0
    print(f"birth pivot = {p_birth:4s} (diagonal={p_birth=='d00'}):")
    print(f"    |det D composite| = {d}")
    print(f"    ledger z_{p_birth}^4  MATCH = {match}")
    print()
