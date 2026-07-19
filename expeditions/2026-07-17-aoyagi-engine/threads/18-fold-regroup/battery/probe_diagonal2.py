#!/usr/bin/env python3
# Confirm the diagonal scoped-condition sharply:
#  (P1) TERMINAL off-diagonal birth (no descendant touches it) -> identity HOLDS (clean).
#  (P2) case-1(2) off-diagonal birth then a descendant SPLIT of it -> identity FAILS unless diagonal.
#  (P3) the exact failure shape: exponent SPLITS between the diagonal corner (touched by descendant)
#       and the off-diagonal birth pivot.
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
    for (center, pivot) in reversed(path):
        pt = chart(pt, center, pivot)
    return src, pt

def jac_det(path, cells):
    src, pt = compose(path, cells)
    order = list(cells)
    J = sp.Matrix([[sp.diff(pt[r], src[c]) for c in order] for r in order])
    return sp.factor(J.det())

print("P1: TERMINAL off-diagonal birth (case-2 births D at off-diagonal d11, NO descendant merge)")
cells = ['d00','d01','d10','d11']
path = [ (['d00','d01','d10','d11'], 'd11') ]     # single case-2 node, off-diagonal pivot, leaf below
d = jac_det(path, cells)
print(f"    |det| = {d} ; ledger z_d11^3 MATCH = {sp.simplify(d - sp.Symbol('z_d11',real=True)**3)==0}")
print("    => terminal off-diagonal is FINE (nothing scales it).")
print()

print("P2: case-1(2) OFF-DIAGONAL birth, then descendant case-1(1) merge into it via DIAGONAL corner")
# n0 (root) case-1: u-corner = existing divisor U (diagonal uU), d-block {dd01,dd10,dd11} (a 1x3 say)
# case-1(2) edge births new divisor at an off-diagonal d-block cell (dd11). Its divBirthCoord = its
# node's (layer,cleared) DIAGONAL = call it g00. But the geometric pivot is dd11. A descendant merges
# into it via g00 (diagonal). Model minimally: births at pivot p in {g00(diag),dd11(offdiag)}; child
# merges into it at g00.
cells2 = ['uU','g00','dd11','f']
for p in ['g00','dd11']:
    path2 = [ (['uU','g00','dd11'], p),   # n0: births new divisor at p (case-1(2)); uU is u-corner
              (['g00','f'], 'g00') ]      # child: case-1(1) merge into new divisor via its diagonal g00
    d2 = jac_det(path2, cells2)
    # ledger (finding-3 per-pivot): new divisor divCoord=p; born via case-1(2) so divExp = divExp(uU)+2
    #   here treat divExp(uU)=1 (uU exp on this path irrelevant/terminal) so new divExp = 1+... ; but
    #   simplest: check whether ALL exponent lands on z_p (single cell) -> monomial is a power of z_p.
    is_single = (len(d2.free_symbols) == 1 and list(d2.free_symbols)[0] == sp.Symbol('z_'+p,real=True))
    print(f"    birth pivot={p:5s} diag={p=='g00'}: |det|={d2} ; single-cell power of z_{p}? {is_single}")
print("    => only the DIAGONAL birth keeps the exponent on one cell; off-diagonal SPLITS it.")
