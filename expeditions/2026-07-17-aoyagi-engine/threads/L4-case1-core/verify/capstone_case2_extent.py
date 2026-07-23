"""
§12.1 role-split DECISIVE CHECK (pnp-transport, team-lead): does case12/case2's RAW residual EXCEED
⟨ed.center⟩ on wide d the way case11's did? Decides FULL §7 extension vs case11-only.

At every case12/case2 δ=1 edge (parent.cleared = 0) on a width-increasing witness, check:
 (1) raw foldResid(parent) ∈ ⟨ed.center⟩ ? (exact Gröbner) — does the ancestor-coupling inject
     out-of-center dependence (like case11), or is case2/12 already ⊆ its center?
 (2) sourceClearedResid(parent) support ⊆ blockCoords d S ⊆ ed.center ?

For case2/case12, canonCenterOf = the layer-S widthMinUpto block = blockCoords d S = supportAt(J=0),
so `ed.center = supportAt` and `extra = ∅` (degenerate split). The question reduces to: is the raw
residual in the ideal of the CURRENT-layer block, or does an ANCESTOR coupling escape it?

MECHANISM (team-lead): case2/12 clears its OWN (current-edge) pivot (fresh exceptional); case11 REUSES
an ANCESTOR's birth corner — the escaping coupling is the ancestor's below-pivot column. Whether a
case2/12 δ=1 node has accumulated ancestor couplings that escape ITS current-layer center is what this
decides. Witnesses: (2,3,2,2) [case2(1,0) δ=1 has layer-0 clears + a case11 as ancestors], plus a deeper
(2,2,3,2) and (2,3,2,2,2) for case2 δ=1 at a later layer with more ancestors.
"""
import sympy as sp
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, Phi_p, coreGen, blockCoords, wmu

def canonCenter_case2(d, S, J):
    w = wmu(d, S)
    return {(S, r, c) for r in range(d[S + 1]) for c in range(d[S]) if r >= J and J <= c < w}

def ancestor_clear(u, d, parent):
    from capstone_closing_ii import ancestor_column_clear_map
    return ancestor_column_clear_map(u, d, parent)

def in_ideal(f, gens, allv):
    f = sp.expand(f)
    if f == 0:
        return True
    if not gens:
        return False
    G = sp.groebner([sp.expand(g) for g in gens], *allv, order='grevlex')
    return sp.expand(G.reduce(f)[1]) == 0

def run(d):
    print("=" * 88)
    N, u = dims_coords(d)
    edges, meta = oracle_edges(d)
    allv = list(u.values())
    print(f"d={d}  branch={[(e[0], e[1], e[2]) for e in edges]}")
    any_escape = False
    for idx, e in enumerate(edges):
        if e[0] not in ("case2", "case12"):
            continue
        S, J = e[1], e[2]
        delta = e[5]
        if delta != 1:                       # only δ=1 (parent cleared=0) — the boostReady case
            continue
        parent = edges[:idx]
        center = canonCenter_case2(d, S, J)
        support = blockCoords(d, S)
        # ancestors present?
        anc = [(pe[0], pe[1], pe[2]) for pe in parent if pe[0] in ("case2", "case12", "case11")]
        raw = [sp.expand(f) for f in coreGen(Phi_p(u, d, parent, True), d)]
        src = [sp.expand(f) for f in coreGen(Phi_p(ancestor_clear(u, d, parent), d, parent, True), d)]
        cgens = [u[c] for c in center]
        raw_in = all(in_ideal(f, cgens, allv) for f in raw)
        # sourceCleared support in layer S vs blockCoords
        def layerS_supp(fs):
            s = set()
            for f in fs:
                for k in u:
                    if k[0] == S and u[k] in f.free_symbols:
                        s.add(k)
            return s
        src_supp = layerS_supp(src)
        src_in = all(in_ideal(f, cgens, allv) for f in src)
        esc = src_supp - support
        print(f"  case2/12 δ=1 edge @ (S={S},J={J}) pivot{e[3]}; ancestors={anc}")
        print(f"    (1) RAW residual ∈ ⟨ed.center⟩: {raw_in}  {'(⊆ center — NO escape)' if raw_in else '(EXCEEDS center — ESCAPE like case11)'}")
        print(f"    (2) sourceClearedResid ∈ ⟨ed.center⟩: {src_in}; layer-{S} support escapes blockCoords: {sorted(esc) if esc else 'none'}")
        if not raw_in:
            any_escape = True
    print(f"  ⟹ some case2/12 δ=1 raw residual EXCEEDS its center on this witness: {any_escape}")
    return any_escape

if __name__ == "__main__":
    results = {}
    for d in [(2, 3, 2, 2), (2, 2, 3, 2), (2, 3, 2, 2, 2)]:
        results[d] = run(d)
    print("=" * 88)
    print("VERDICT — case2/case2 δ=1 raw residual exceeds ⟨center⟩ (ESCAPE like case11)?")
    for d, r in results.items():
        print(f"  {d}: {'YES (escape)' if r else 'NO (⊆ center)'}")
    print("  FORK: any YES ⟹ FULL §7 extension (all boostReady reads cleared object);"
          "\n        all NO ⟹ lighter world (case11-only; case2/12 clears its OWN pivot, no ancestor escape).")
