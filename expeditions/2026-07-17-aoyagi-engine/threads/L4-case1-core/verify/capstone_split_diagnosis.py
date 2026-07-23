"""
CAPSTONE SPLIT — DIAGNOSIS (pnp-transport, task #68).

FINDING under test (exact-rational Gröbner, not a guess):
On the real canonical (2,2,2,2) case11 branch, with the FULL 3-branch canonNormalizationOf render,
foldResid(parent):
  (I)  IS degree-1 supported on supportAt(=all layer-1) — the CARRIED invariant holds;
  (II) is NOT in the ideal ⟨ed.center⟩ = ⟨e₂,run-block⟩ — so Deg1SupportedOn(foldResid p) ed.center
       FAILS, hence MergeBoostSplit with e₂=canonPivotOf FAILS;
  (III) the obstruction is A_0's UN-ROW-CLEARED below-pivot entries (0,1,j) (j = output column):
       the fold's shear does the interior Schur + ±γ recoords but NOT the pivot row/col clear
       (r4Clear is a boostReady device, not in the fold), so the input layer couples the extra
       block into the residual with an output-column-dependent factor (0,1,j), not the single e₂.
  (IV) HYPOTHESIS PROBE: if we FIRST row-clear A_0 (zero the pivot rows/cols so A_0 cols are unit),
       does the split with single e₂ hold?  (Tests whether the gap = "r4Clear must be folded in".)

All ideal tests are exact (sympy groebner / reduced).  This script REPORTS; it does not assert the
certificate.
"""
import sympy as sp
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_split_oracle import (dims_coords, oracle_edges, foldResid_parent,
                                    supportAt, canonNormalizationOf, coreGen, apply_edge)

def ideal_member(f, gens, allvars):
    """exact: is f in ideal <gens>? via reduced Groebner remainder."""
    f = sp.expand(f)
    if f == 0:
        return True
    G = sp.groebner(gens, *allvars, order='grevlex')
    return sp.expand(G.reduce(f)[1]) == 0

def run(d):
    print("=" * 84)
    print(f"d = {d}")
    N, u = dims_coords(d)
    edges, meta = oracle_edges(d)
    idx = next((i for i, e in enumerate(edges) if e[0] == "case11"), None)
    if idx is None:
        print("  no case11"); return
    ce = edges[idx]; parent = edges[:idx]
    S, J = ce[1], ce[2]; e2 = ce[3]; center = ce[4]
    support = supportAt(d, S, J); part = support & center; extra = support - center
    fr = foldResid_parent(u, d, parent, scoped=True)
    allvars = list(u.values())
    center_gens = [u[c] for c in center]
    support_gens = [u[c] for c in support]

    print(f"  e₂={e2}  center={sorted(center)}  support={sorted(support)}")
    print(f"  part={sorted(part)}  extra={sorted(extra)}")
    print("\n  (I) each slot ∈ ⟨supportAt⟩ (carried invariant)?")
    inv_ok = all(ideal_member(f, support_gens, allvars) for f in fr)
    print(f"      ALL slots ∈ ⟨support⟩: {inv_ok}")
    print("\n  (II) each slot ∈ ⟨ed.center⟩ (what Deg1SupportedOn ed.center requires)?")
    for j, f in enumerate(fr):
        fe = sp.expand(f)
        if fe in (0, 1):
            continue
        m = ideal_member(fe, center_gens, allvars)
        print(f"      slot {j} ∈ ⟨center⟩: {m}")
    center_ok = all(ideal_member(f, center_gens, allvars) for f in fr)
    print(f"      => Deg1SupportedOn(foldResid p) ed.center HOLDS: {center_ok}")

    # (III) the obstruction coords: single coords g s.t. every slot ∈ ⟨center ∪ {g}⟩,
    #       restricted to g among layer-<S (input-side) coords
    print("\n  (III) which extra INPUT coord repairs membership? test ⟨center ∪ {g}⟩ for g in layer<S:")
    for g in sorted(k for k in u if k[0] < S):
        gens2 = center_gens + [u[g]]
        if all(ideal_member(f, gens2, allvars) for f in fr):
            print(f"      ⟨center ∪ {{{g}}}⟩ CONTAINS all slots  (obstruction coord)")

    # (IV) HYPOTHESIS PROBE: row-clear A_0 first (zero pivot rows/cols of the FIRST clear), then split
    print("\n  (IV) PROBE — apply the missing pivot row/col clear to the input layer, then re-test split:")
    fr2 = foldResid_rowcleared(u, d, parent)
    # single-e₂ divisibility on the row-cleared residual
    ok_single = single_e2_holds(fr2, u, d, support, part, extra, e2)
    print(f"      after row-clear: single-e₂(={e2}) split holds: {ok_single}")

def foldResid_rowcleared(u, d, parent):
    """Same fold, but at each δ=1 clear ALSO zero the pivot's row & column in the SAME layer
       (the Lemma-1 regular transform Q that the fold defers to r4Clear)."""
    v = dict(u)
    for e in reversed(parent):
        case, sL, sC, piv, cen, delta = e
        v = apply_edge(v, d, case, sL, sC, piv, cen, delta, True)
        if case == "case2" and delta == 1:
            a, b = piv[1], piv[2]
            for (L, r, c) in list(v.keys()):
                if L == sL and ((r == a and c != b) or (c == b and r != a)):
                    v[(L, r, c)] = sp.Integer(0)
    return coreGen(v, d)

def single_e2_holds(fr, u, d, support, part, extra, e2):
    ue2 = u[e2]; ok = True
    for f in fr:
        fe = sp.expand(f)
        if fe in (0, 1):
            continue
        for i in extra:
            ci = sp.expand(fe.coeff(u[i], 1))
            if ci != 0 and sp.expand(ci.subs(ue2, 0)) != 0:
                ok = False
    return ok

if __name__ == "__main__":
    for d in [(2, 2, 2, 2), (3, 3, 2, 2)]:
        run(d)
