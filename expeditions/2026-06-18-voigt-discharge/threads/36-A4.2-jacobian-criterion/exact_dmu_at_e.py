#!/usr/bin/env python3
"""
EXACT certificate that  dmu_M at the identity = delta0 = deformationδ M M  (A4.3 crux).

mu_M : G=(GL2)^3 -> Rep,  P |-> (P_{i+1} M_i P_i^{-1})_i.
The orbit-pullback genericOrbitCoord sends X<i,r,c> to the (r,c) entry of P_{i+1} M_i P_i^{-1}.
Its differential at the identity, in tangent direction phi = (phi_0,phi_1,phi_2) (phi_v in Mat_{d_v}),
is computed by writing P_v = I + t phi_v and reading the O(t) coefficient of P_{i+1} M_i P_i^{-1}:

    d/dt[ (I+t phi_{i+1}) M_i (I+t phi_i)^{-1} ]|_{t=0}
      = phi_{i+1} M_i  -  M_i phi_i          (since (I+t phi)^{-1} = I - t phi + O(t^2))
      = (deformationδ M M)(phi)_i.

We verify this EXACTLY and SYMBOLICALLY (phi entries are free symbols; t a formal infinitesimal):
for every (2,2,2) orbit, the O(t) coefficient matrix equals phi_{i+1} M_i - M_i phi_i identically.
This is the identification  dmu_e = delta0  that makes "generic Jacobian rank = finrank(range delta0)"
land on the concrete linear-algebra quantity. (Pure algebra; char-free at THIS step -- homogeneity, not
char 0, is what later upgrades identity-rank to generic-rank.)
"""
import sympy as sp

Nv = 3
t = sp.Symbol('t')

def interval_arrow(a, b, i):
    src = 1 if a <= i <= b else 0
    tgt = 1 if a <= i + 1 <= b else 0
    if src and tgt:
        return sp.Matrix([[1]])
    return sp.zeros(tgt, src)

def directsum_tuple(intervals):
    d = [0]*Nv
    for (a, b) in intervals:
        for w in range(Nv):
            if a <= w <= b:
                d[w] += 1
    M = []
    for i in range(Nv-1):
        blocks = [interval_arrow(a, b, i) for (a, b) in intervals]
        rows = sum(b.rows for b in blocks); cols = sum(b.cols for b in blocks)
        Mi = sp.zeros(rows, cols); r = c = 0
        for blk in blocks:
            Mi[r:r+blk.rows, c:c+blk.cols] = blk; r += blk.rows; c += blk.cols
        M.append(Mi)
    return d, M

def check(name, intervals):
    d, M = directsum_tuple(intervals)
    phi = []
    for v in range(Nv):
        n = d[v]
        phi.append(sp.Matrix(n, n, lambda r, c: sp.Symbol(f"ph{v}_{r}_{c}")))
    ok = True
    for i in range(Nv-1):
        Pi   = sp.eye(d[i])   + t*phi[i]
        Pip1 = sp.eye(d[i+1]) + t*phi[i+1]
        prod = Pip1 * M[i] * Pi.inv()
        # O(t) coefficient, entrywise, exact
        diff_coeff = prod.applyfunc(lambda e: sp.diff(sp.series(e, t, 0, 2).removeO(), t).subs(t, 0))
        commutator = phi[i+1]*M[i] - M[i]*phi[i]
        if sp.simplify(diff_coeff - commutator) != sp.zeros(d[i+1], d[i]):
            ok = False
            print(f"  MISMATCH at arrow {i}: {sp.simplify(diff_coeff - commutator)}")
    print(f"{name}: d={d}  ->  dmu_e == (phi_{{i+1}} M_i - M_i phi_i) = deformationδ identically: {ok}  [EXACT symbolic]")

if __name__ == "__main__":
    check("(1,1)-orbit", [(0,0),(0,1),(1,2),(2,2)])
    check("zero-product", [(0,0),(0,0),(1,2),(1,2)])
    # also a generic full M (no special structure) to confirm the identity is structural, not lucky
    check("generic-full (sanity)", None) if False else None
    # generic full: replace M by free symbols
    d = [2,2,2]
    M = [sp.Matrix(2,2,lambda r,c: sp.Symbol(f"m{i}_{r}_{c}")) for i in range(2)]
    phi=[sp.Matrix(2,2,lambda r,c: sp.Symbol(f"ph{v}_{r}_{c}")) for v in range(3)]
    ok=True
    for i in range(2):
        Pi=sp.eye(2)+t*phi[i]; Pip1=sp.eye(2)+t*phi[i+1]
        prod=Pip1*M[i]*Pi.inv()
        dc=prod.applyfunc(lambda e: sp.diff(sp.series(e,t,0,2).removeO(),t).subs(t,0))
        comm=phi[i+1]*M[i]-M[i]*phi[i]
        if sp.simplify(dc-comm)!=sp.zeros(2,2): ok=False
    print(f"generic-full M (free symbols): dmu_e == commutator identically: {ok}  [EXACT symbolic -- structural, not data-specific]")
