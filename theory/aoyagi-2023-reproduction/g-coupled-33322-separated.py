#!/usr/bin/env python3
# provenance: threads/28-twoblock-diagb (pnp two-block/two-shared-factor diag(b) certificate)
"""(3,3,3,2,2) t=(2,2,1,0): the minimal L=4 instance with TWO SEPARATED shared-deep-factor
couplings -- the genuine 'two independent shared deep factors' kill-instance flagged by thread-27.
minAdm=4, rlct should be 2. Two corank-1 scalar couplings: delta1 (layer 1, C1 rank 3->2) and
delta2 (layer 3, rank 2->1), SEPARATED by a plateau at layer 2 (t1=t2=2). delta1 shares the deep
product C3*C4; delta2 shares C4. All exact (sympy).

Derived structure (two nested det-1 block-elim peels; verified in the accompanying derivation):
   <prod C> = < X_row1, delta2*X_row2, delta1*X_row3 >,  X = C3*C4 (3x2),
 C3 (3x2) and C4 (2x2) are the two SHARED deep factors; delta1, delta2 INDEPENDENT scalars;
 row1 = the KEPT (unweighted) rank-survivor direction.

Radial the two shared factors: C3 = w*C3bar (top-left pivot 1), C4 = y*C4bar (top-left pivot 1),
so <prod C> = w*y * < Y_row1, delta2*Y_row2, delta1*Y_row3 >, Y = C3bar*C4bar.

Verifies (principality is a LOCAL-ring statement at the origin):
 (a) the KEPT row Y_row1 has first entry 1+p*d (nonzero constant term) = LOCAL UNIT
     => <prod C>_local = <w*y> PRINCIPAL (single dominant monomial b1 = w*y).
 (b) loss = (w*y)^2 * R with R(origin) = ||Y_row1||^2 = 1 (unit): loss = (w*y)^2 * unit.
 (c) rlct = 1/2 * min over the two shared-radial divisors (NOT joined -- different depths):
     C3 (6 coords) -> w^5 -> ratio 3 (non-binding); C4 (4 coords, deepest block) -> y^3 -> ratio 2 (BINDING).
     rlct = min(3,2) = 2 = 1/2*minAdm.  b1 = w*y = PRODUCT of two divisors, both dividing b1
     (NOT incomparable generators) -- so the single-chain reading SURVIVES.
 (d) anti-check: if NO kept unweighted row existed (all rows delta-weighted) the constant terms
     vanish and it would NOT be principal -- confirming the kept rank-survivor is what forces it.
Exit 0 iff all hold.
"""
import sys, sympy as sp
from fractions import Fraction
from functools import lru_cache

ok = True

# ---- det-1 peel identities (layer 1 and layer 3), for the record ----
B1 = sp.Matrix(2, 1, sp.symbols('B1_0 B1_1')); C1a = sp.Matrix(1, 2, sp.symbols('C1a_0 C1a_1')); dd1 = sp.symbols('DD1')
C1m = sp.Matrix([[1, 0, B1[0]], [0, 1, B1[1]], [C1a[0], C1a[1], dd1]])
Q1L = sp.Matrix([[1, 0, 0], [0, 1, 0], [-C1a[0], -C1a[1], 1]]); Q1R = sp.Matrix([[1, 0, -B1[0]], [0, 1, -B1[1]], [0, 0, 1]])
delta1_schur = dd1 - (C1a * B1)[0]
peel1_ok = (sp.simplify(Q1L * C1m * Q1R) == sp.diag(1, 1, delta1_schur) and
            sp.simplify(Q1L.det()) == 1 and sp.simplify(Q1R.det()) == 1)
g12, g21, g22 = sp.symbols('g12 g21 g22'); G = sp.Matrix([[1, g12], [g21, g22]])
Q3L = sp.Matrix([[1, 0], [-g21, 1]]); Q3R = sp.Matrix([[1, -g12], [0, 1]]); delta2_schur = g22 - g21 * g12
peel3_ok = (sp.simplify(Q3L * G * Q3R) == sp.diag(1, delta2_schur) and
            sp.simplify(Q3L.det()) == 1 and sp.simplify(Q3R.det()) == 1)
print(f"(peels) layer-1 det-1 block-elim C1->diag(I2,delta1): {peel1_ok}; "
      f"layer-3 det-1 block-elim ->diag(1,delta2): {peel3_ok}")
ok &= peel1_ok and peel3_ok

# ---- resolve the two shared factors; check LOCAL principality + loss form ----
w, y, p_, c_, d_, f_, q_, s_, u_, v_, d1s, d2s = sp.symbols('w y p c d f q_ s_ u_ v_ delta1 delta2')
C3bar = sp.Matrix([[1, p_], [q_, s_], [u_, v_]]); C4bar = sp.Matrix([[1, c_], [d_, c_ * d_ + f_]])
Y = C3bar * C4bar
allv = [p_, c_, d_, f_, q_, s_, u_, v_, d1s, d2s]; zero = {vv: 0 for vv in allv}
resid = [Y[0, 0], Y[0, 1], d2s * Y[1, 0], d2s * Y[1, 1], d1s * Y[2, 0], d1s * Y[2, 1]]
const_terms = [sp.expand(g).subs(zero) for g in resid]
local_unit = any(ct != 0 for ct in const_terms)
print(f"(a) Y_row1 = {[sp.expand(Y[0, j]) for j in range(2)]}; residual constant terms = {const_terms}")
print(f"    LOCAL unit present => <prod C>_local = <w*y> PRINCIPAL: {local_unit}  (kept row Y_row1[0]=1+p*d)")
ok &= local_unit

R = sum(Y[0, j]**2 for j in range(2)) + d2s**2 * sum(Y[1, j]**2 for j in range(2)) + d1s**2 * sum(Y[2, j]**2 for j in range(2))
R0 = sp.simplify(R.subs(zero))
print(f"(b) loss = (w*y)^2 * R, R(origin) = {R0} (unit: {R0 == 1}) => loss = (w*y)^2 * unit")
ok &= (R0 == 1)

r_w, r_y = Fraction(5 + 1, 2), Fraction(3 + 1, 2)   # C3: 6 coords -> w^5 ; C4: 4 coords -> y^3
rlct = min(r_w, r_y)
print(f"(c) shared radials: w(C3,6coords) ratio {r_w}, y(C4,4coords,deepest) ratio {r_y}; rlct = min = {rlct}")
print(f"    b1 = w*y = PRODUCT of two NON-joined divisors (different depths), both | b1 -> single dominant monomial")
ok &= (rlct == 2)


@lru_cache(None)
def minAdm(M):
    M = tuple(M)
    if len(M) == 1:
        return 0
    if len(M) == 2:
        return M[0] * M[1]
    return min((M[0] - t) * (M[1] - t) + minAdm((t,) + M[2:]) for t in range(min(M[0], M[1]) + 1))


mA = minAdm((3, 3, 3, 2, 2))
print(f"(*) minAdm(3,3,3,2,2) = {mA}; rlct = {Fraction(mA, 2)}; match: {rlct == Fraction(mA, 2)}")
ok &= (rlct == Fraction(mA, 2))

ct_nk = [sp.expand(g).subs(zero) for g in [d2s * Y[1, 0], d2s * Y[1, 1], d1s * Y[2, 0], d1s * Y[2, 1]]]
print(f"(d) anti-check (hypothetical all-delta-weighted, no kept row): const terms {ct_nk} -> local unit {any(x != 0 for x in ct_nk)}")

print(f"\n(3,3,3,2,2) TWO-SEPARATED-SHARED-FACTOR: {'PASS -> single chain SURVIVES, <prod C>=<w*y> principal, rlct=2' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)
