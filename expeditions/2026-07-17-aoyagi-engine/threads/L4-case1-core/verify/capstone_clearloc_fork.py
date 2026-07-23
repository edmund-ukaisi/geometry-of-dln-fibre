"""
CLEAR-LOCATION FORK (pnp-transport, top-priority #82). IsRealBranch rule (b) (MonumentAtlas:1050-1056):
case12/case2 pivot is FREE within the center; shearφ = canonNormalizationOf(...pivot) at that fan pivot.
So the FOLD clears at the STORED fan pivot. FORK: couplingCoords keys the clear on
 (i)  the STORED fan pivot's column {(L,r,b): r>a}  [current def], OR
 (ii) the DIAGONAL cleared column = canonPivotOf {(L,r,J): r>J}.
On canonical branches stored=diagonal ⟹ coincide (all prior verifications valid).

*** CONFOUNDED — NOT the arbiter (kept as a negative record). *** This script overrides ONLY the first
fan pivot and keeps the downstream centers/pivots/case11-e2 at their canonical (diagonal) values. That is
NOT a coherent real branch: Aoyagi's next residual D_1 excludes the chosen pivot's ROW AND COLUMN, so an
off-diagonal first pivot (0,0,1) forces the SECOND clear onto column 0 (pivot (0,1,0)) and reindexes the
case11 center — none of which a single-edge override does. The result below (BOTH rules fail S1; the
surviving coord (0,1,0) is the diagonal-complement of the un-reindexed downstream, not a genuine coupling)
is an artifact of that incoherence, uninformative for the fork. The CLEAN arbiter is the single-edge
fold-clear-location check (capstone_clearloc_singleedge.py): the fold's δ=1 clear normalizes the FAN PIVOT
and its shear reads the fan pivot's column ⟹ reading (i). A coherent multi-edge off-diagonal S1 would need
the whole downstream reindexed to track the fan choice (the oracle's fan-generation machinery).
"""
import sympy as sp
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, Phi_p, coreGen, blockCoords, wmu, cornerToFlat

def center_case2(d, S, J):
    return {(S, r, c) for r in range(d[S + 1]) for c in range(d[S]) if r >= J and J <= c < wmu(d, S)}

def build_offdiag_branch(d, fan_pivot):
    """(2,2,2,2)-type: FIRST case2 uses fan_pivot (off-diagonal, ∈ center); rest canonical to the case11."""
    N, u = dims_coords(d)
    edges, meta = oracle_edges(d)
    idx = next(i for i, e in enumerate(edges) if e[0] == "case11")
    br = list(edges[:idx + 1])
    # override the FIRST case2 edge's stored pivot to the fan choice (center unchanged; canonNormalizationOf(pivot))
    e0 = br[0]
    assert e0[0] == "case2" and e0[1] == 0 and e0[2] == 0
    br[0] = ("case2", 0, 0, fan_pivot, e0[4], e0[5])
    return N, u, br, br[idx][3], br[idx][4]   # N,u,branch, case11 e2, case11 center

def couplingClear(u, d, edges, rule):
    """rule='stored': below the STORED pivot col; rule='diag': below the DIAGONAL cornerToFlat(S,J) col."""
    w = dict(u)
    for (case, sL, sC, piv, cen, delta) in edges:
        if case not in ("case2", "case12"):
            continue
        if rule == "stored":
            a, b = piv[1], piv[2]
        else:  # diag
            dg = cornerToFlat(d, sL, sC); a, b = dg[1], dg[2]
        for (L, r, c) in list(w.keys()):
            if L == sL and c == b and r > a:
                w[(L, r, c)] = sp.Integer(0)
    return w

def in_ideal(f, gens, allv):
    f = sp.expand(f)
    if f == 0: return True
    nz = [sp.expand(g) for g in gens if sp.expand(g) != 0]
    if not nz: return False
    return sp.expand(sp.groebner(nz, *allv, order='grevlex').reduce(f)[1]) == 0

def test(d, fan_pivot):
    print("=" * 84)
    N, u, br, e2, center = build_offdiag_branch(d, fan_pivot)
    allv = list(u.values())
    S = br[-1][1]; support = blockCoords(d, S); part = support & center; extra = support - center
    print(f"d={d} FAN first pivot={fan_pivot} (diagonal would be (0,0,0)); case11 e2={e2}, center={sorted(center)}")
    # raw obstruction: coreGen(Phi_p(u)) at the case11 node — locate surviving coupling
    raw = [sp.expand(f) for f in coreGen(Phi_p(u, d, br, True), d)]
    # Deg1SupportedOn ed.center on raw? and which layer-0 coord is the coupling?
    zero_center = {u[c]: 0 for c in center}
    raw_defect = [sp.expand(f.subs(zero_center)) for f in raw]
    couplings = set()
    for f in raw_defect:
        for k in u:
            if k[0] == 0 and u[k] in f.free_symbols:
                couplings.add(k)
    print(f"  raw obstruction (slots on center=0) reads layer-0 coords: {sorted(couplings)}")
    fan_col = fan_pivot[2]; diag_col = 0
    print(f"    fan pivot col = {fan_col}; diagonal col = {diag_col}")
    for rule in ("stored", "diag"):
        clr = couplingClear(u, d, br, rule)
        src = [sp.expand(f) for f in coreGen(Phi_p(clr, d, br, True), d)]
        cg = [u[c] for c in center]
        s1 = all(in_ideal(f, cg, allv) for f in src)
        print(f"  couplingClear rule={rule:6s}: cleared StepInv S1 (src ∈ ⟨ed.center⟩): {s1}")

if __name__ == "__main__":
    test((2, 2, 2, 2), (0, 0, 1))   # off-diagonal fan pivot col 1
