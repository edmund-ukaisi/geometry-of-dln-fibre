"""
CLOSING CONTRACT (ii) — IDEAL-EQUALITY (pnp-transport, #68/#69 ruled object).

Ruled object: sourceClearedResid := foldResid ∘ (ancestor-column-clear), the det-0 verified repair,
recursion untouched. Certify ⟨sourceClearedResid slots⟩ = ⟨foldResid slots⟩ at the case11 parent node
(the "column-clear is regular / Lemma-1-neutral" claim). Exact Gröbner, three witnesses.

ALSO reports the two things that decide whether a FALSE ideal-equality is fatal or benign:
  * the COUPLING REMAINDER  r_j := foldResid_j − sourceCleared_j  (=2·u₀₁₀·(…) on (2,2,2,2)); is it
    in ⟨sourceCleared slots⟩ (⟹ ⟨raw⟩=⟨src⟩) or in ⟨ed.center⟩ (⟹ the decomposition (b) route)?
  * whether the clear preserves the loss's RLCT-relevant object — the product ⟨coreGen⟩ (∏C) at the
    ROOT, restricted along the branch — vs merely the residual slot ideal at the node.
Reports; asserts nothing.
"""
import sympy as sp
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import (dims_coords, oracle_edges, Phi_p, coreGen, blockCoords)

def ancestor_column_clear_map(u, d, parent_edges):
    """the single precompose map: zero the below-pivot entries of every ancestor-cleared column."""
    w = dict(u)
    for (case, sL, sC, piv, cen, delta) in parent_edges:
        if case in ("case2", "case12"):
            a, b = piv[1], piv[2]
            for (L, r, c) in list(w.keys()):
                if L == sL and c == b and r > a:
                    w[(L, r, c)] = sp.Integer(0)
    return w

def in_ideal(f, gens, allv):
    f = sp.expand(f)
    if f == 0:
        return True
    G = sp.groebner([sp.expand(g) for g in gens], *allv, order='grevlex')
    return sp.expand(G.reduce(f)[1]) == 0

def run(d):
    print("=" * 88)
    print(f"d = {d}")
    N, u = dims_coords(d)
    edges, meta = oracle_edges(d)
    idx = next(i for i, e in enumerate(edges) if e[0] == "case11")
    ce = edges[idx]; parent = edges[:idx]
    S, J = ce[1], ce[2]; center = ce[4]
    allv = list(u.values())
    # raw foldResid(p)
    raw = coreGen(Phi_p(u, d, parent, True), d)
    # sourceClearedResid = foldResid ∘ ancestor-column-clear  (precompose the clear on raw input)
    cleared_input = ancestor_column_clear_map(u, d, parent)
    # Phi_p expects a dict keyed by coord; compose: run Phi_p on the cleared input
    src = coreGen(Phi_p(cleared_input, d, parent, True), d)
    raw = [sp.expand(x) for x in raw]; src = [sp.expand(x) for x in src]
    # (ii) ideal-equality both directions
    raw_in_src = all(in_ideal(f, src, allv) for f in raw)
    src_in_raw = all(in_ideal(f, raw, allv) for f in src)
    print(f"  (ii) ⟨raw⟩ ⊆ ⟨src⟩: {raw_in_src}    ⟨src⟩ ⊆ ⟨raw⟩: {src_in_raw}")
    print(f"       ⟨sourceClearedResid⟩ = ⟨foldResid⟩ : {raw_in_src and src_in_raw}")
    # coupling remainder analysis
    center_gens = [u[c] for c in center]
    rem_in_src, rem_in_center, rem_in_pivot = True, True, True
    pivot = ce[3]
    for a, b in zip(raw, src):
        r = sp.expand(a - b)
        if r == 0:
            continue
        rem_in_src = rem_in_src and in_ideal(r, src, allv)
        rem_in_center = rem_in_center and in_ideal(r, center_gens, allv)
        rem_in_pivot = rem_in_pivot and in_ideal(r, [u[pivot]], allv)
    print(f"  coupling remainder (raw−src): ∈⟨src⟩={rem_in_src}  ∈⟨ed.center⟩={rem_in_center}  ∈⟨pivot⟩={rem_in_pivot}")
    # RLCT-relevant: does the clear preserve the ROOT product ⟨coreGen⟩? (clear is on ancestor cols)
    core = [sp.expand(x) for x in coreGen(u, d)]
    core_cleared = [sp.expand(x) for x in coreGen(ancestor_column_clear_map(u, d, parent), d)]
    core_eq = (all(in_ideal(f, core_cleared, allv) for f in core)
               and all(in_ideal(f, core, allv) for f in core_cleared))
    print(f"  ⟨coreGen⟩ preserved by the clear (∏C product ideal): {core_eq}")

if __name__ == "__main__":
    for d in [(2, 2, 2, 2), (3, 3, 2, 2), (3, 3, 3, 2)]:
        run(d)
