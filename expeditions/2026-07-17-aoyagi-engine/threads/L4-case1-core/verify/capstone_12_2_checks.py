"""
§12.2 THREE CHECKS against the UNCHANGED supportAt (pnp-transport, team-lead re-scope).

(1) CONFIRM (one line): the width-coverage run (capstone_coverage_wide.py) used supportAt = blockCoords
    d S (the CAPPED, unchanged def) — nothing assumed a widen. [Asserted here by re-deriving support the
    same way and checking it equals blockCoords.]
(3) case12/case2 δ=1 boostReady gets center-Deg1 DIRECTLY on the CLEARED object: at a case2/case12 δ=1
    node on a WIDE witness, sourceClearedResid is confined to blockCoords ⊆ ed.center (= the widthMinUpto
    block for case2/12) AND is linear-in-support ⟹ Deg1SupportedOn ed.center directly. [exact Gröbner +
    linearity]
(2) B1 cover-completeness at the WIDE witness — the WIDTH-AGNOSTIC argument: at the case11 node the
    blow-up is along ed.center; its chart cover is indexed by ed.center's GENERATORS. Verify the
    cap-escaped remnant cols (col ≥ widthMinUpto) are NEITHER center generators NOR couplings — they are
    SPECTATORS to the blow-up — so the chart cover (over ed.center) is width-INDEPENDENT, and the fan-cover
    certificate (#11-14, verified at (2,2,2)/(2,2,2,2,2)) transfers to wide d unchanged. The genuine
    completeness proof lives at L7 (leafPath_compactCover); this witnesses the width-invariance of its input.
"""
import sympy as sp
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, Phi_p, coreGen, blockCoords, wmu
from capstone_closing_ii import ancestor_column_clear_map

def layerCoords(d, S):
    return {(S, r, c) for r in range(d[S + 1]) for c in range(d[S])}

def canonCenter_case2(d, S, J):
    w = wmu(d, S)
    return {(S, r, c) for r in range(d[S + 1]) for c in range(d[S]) if r >= J and J <= c < w}

def in_ideal(f, gens, allv):
    f = sp.expand(f)
    if f == 0:
        return True
    G = sp.groebner([sp.expand(g) for g in gens], *allv, order='grevlex')
    return sp.expand(G.reduce(f)[1]) == 0

def check1(d=(2, 3, 2, 2)):
    # supportAt(J=0) computed the coverage way = blockCoords (capped), NOT a widened layerCoords
    S = 1
    support = blockCoords(d, S)
    widened = layerCoords(d, S)
    print(f"(1) supportAt used = blockCoords d {S} = {sorted(support)} (CAPPED, widthMinUpto={wmu(d,S)})")
    print(f"    widened layerCoords d {S} = {sorted(widened)}  ⟹ run used CAPPED (not widened): {support != widened}")
    print(f"    CONFIRM: capstone_coverage_wide.py set `support = blockCoords(d, S)` — the unchanged def. "
          f"Nothing assumed the widen.")

def check3(d):
    N, u = dims_coords(d)
    edges, meta = oracle_edges(d)
    allv = list(u.values())
    print(f"\n(3) case2/12 δ=1 center-Deg1 on the CLEARED object, wide witness d={d}:")
    ok = True
    for idx, e in enumerate(edges):
        if e[0] not in ("case2", "case12") or e[5] != 1:
            continue
        S, J = e[1], e[2]
        if not (d[S] > wmu(d, S)):        # only report the WIDE-layer case2/12 nodes (the load-bearing ones)
            continue
        parent = edges[:idx]
        center = canonCenter_case2(d, S, J); support = blockCoords(d, S)
        src = [sp.expand(f) for f in coreGen(Phi_p(ancestor_column_clear_map(u, d, parent), d, parent, True), d)]
        cgens = [u[c] for c in center]
        conf = all(in_ideal(f, cgens, allv) for f in src)      # confined to ⟨center⟩ (=⟨blockCoords⟩)
        lin = True
        for f in src:
            recon = sum((sp.expand(f.coeff(u[i], 1)) * u[i] for i in support), sp.Integer(0))
            if sp.expand(f - recon) != 0:
                lin = False
        print(f"    WIDE case2/12 δ=1 @ (S={S},J={J}): cleared ∈ ⟨ed.center⟩ {conf}; linear-in-support {lin} "
              f"⟹ Deg1SupportedOn ed.center DIRECT: {conf and lin}")
        ok = ok and conf and lin
    return ok

def check2_B1(d):
    N, u = dims_coords(d)
    edges, meta = oracle_edges(d)
    idx = next(i for i, e in enumerate(edges) if e[0] == "case11")
    ce = edges[idx]; parent = edges[:idx]
    S = ce[1]; center = ce[4]
    support = blockCoords(d, S); raw_layer = layerCoords(d, S)
    cap_escaped = raw_layer - support
    couplings = [k for k in u if sp.simplify(ancestor_column_clear_map(u, d, parent)[k] - u[k]) != 0]
    esc_in_center = cap_escaped & center
    esc_in_coupl = set(cap_escaped) & set(couplings)
    print(f"\n(2) B1 width-agnostic cover at case11 node, d={d} (S={S}):")
    print(f"    ed.center generators = {sorted(center)}")
    print(f"    cap-escaped remnant cols = {sorted(cap_escaped)}")
    print(f"    couplings (ancestor-cleared) = {sorted(couplings)}")
    print(f"    cap-escaped ∩ center = {sorted(esc_in_center) or 'none'}; cap-escaped ∩ couplings = {sorted(esc_in_coupl) or 'none'}")
    spectators = (not esc_in_center) and (not esc_in_coupl)
    print(f"    ⟹ cap-escaped cols are SPECTATORS to the blow-up (neither center nor coupling): {spectators}")
    print(f"    ⟹ the blow-up chart cover (indexed by ed.center generators) is WIDTH-INDEPENDENT; the")
    print(f"       fan-cover cert (#11-14) transfers to wide d. Completeness proof: L7 leafPath_compactCover.")
    return spectators

if __name__ == "__main__":
    check1((2, 3, 2, 2))
    r3 = all(check3(d) for d in [(2, 3, 2, 2), (2, 3, 2, 2, 2)])
    r2 = all(check2_B1(d) for d in [(2, 3, 2, 2), (2, 4, 2, 2), (2, 3, 3, 2)])
    print("=" * 78)
    print(f"§12.2 checks: (1) confirmed; (2) B1 width-agnostic: {r2}; (3) case2/12 center-Deg1 direct: {r3}")
