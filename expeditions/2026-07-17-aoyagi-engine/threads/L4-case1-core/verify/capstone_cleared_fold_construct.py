"""
#74 GLOBAL-MOVE SOUNDNESS — EXPLICIT cleared-fold construction + the two render-spec shapes
(pnp-transport, team-lead priority-1 continuation; L4D interface spec).

PAPER-FIRST (worked.tex:562-577): the cleared fold IS Aoyagi's recursion — she recurses on the cleared
normal form diag(b)·[[E_J,O],[O,D_J]] (E_J = identity: the below-pivot columns ARE zero). The raw fold
(shears-only, couplings surviving) was our artifact. So the cleared step map = blockBlowupMap ∘ (Q₁ row-clear:
zero the pivot column below the pivot — her regular transform) ∘ edgeShear, and clearedFoldB accumulates
u_pivot^δ. clearedFoldG_C readable off her step; divergence = FLAG, not a choice.

EXPLICIT per-step construction:
  clearedStepMap(edge)(v) := blockBlowupMap(center,pivot) ( colClear_edge ( edgeShear v ) )
    where colClear_edge zeros v[(L,r,b)] for r>a (below-pivot in the pivot column b), at δ=1 case2/12/11.
  clearedFoldG_C := ∘ clearedStepMap over the path (root outermost).
  clearedFoldB_C := root 1; step = (u pivot)^δ · clearedFoldB_C_parent(clearedStepMap u).
  sourceClearedResid := coreGen ∘ (fold transforms, with colClear at each δ=1 step)  [= the (D)-carrier].

VERIFY (success criterion):
 (S1) CLEARED StepInv: coreGen(clearedFoldG_C u) ∈ ⟨ clearedFoldB_C · sourceClearedResid_j ⟩, and
      clearedFoldB_C | coreGen∘clearedFoldG_C (pivot factor lives in clearedFoldB_C — by construction) —
      at EVERY node (covers case11 δ=1, case2/12 δ=1, δ=0, rollover), on (2,2,2,2) + wide (2,3,2,2) + (3,3,2,2).
 (S2) CHILD↔PARENT commutation `sourceClearedResid_extend_delta1`: at a δ=1 edge, child C = parent C at the
      strict-transform quot arg (couplingClear/quot commute).
 (X) per-step clearedFoldG_C == foldG ∘ globalCouplingClear (the explicit per-step = the verified precompose).
"""
import sympy as sp
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, coreGen, Phi_p
from capstone_closing_ii import ancestor_column_clear_map
from capstone_stepinv_exists_q import shear, foldG, foldB

def colClear_edge(v, e):
    """zero the pivot column below the pivot for a δ=1 clear (case2/12/11); id otherwise."""
    case, sL, sC, piv, cen, delta = e
    if delta != 1 or piv is None or case == "rollover":
        return dict(v)
    a, b = piv[1], piv[2]
    out = dict(v)
    for (L, r, c) in list(out.keys()):
        if L == sL and c == b and r > a:
            out[(L, r, c)] = sp.Integer(0)
    return out

def clearedStepMap(v, d, e):
    case, sL, sC, piv, cen, delta = e
    w = shear(v, d, case, sL, sC, piv)          # edgeShear
    w = colClear_edge(w, e)                       # Q₁ row-clear (zero below-pivot col) — her regular transform
    out = {}
    for k in v:
        if piv is not None and k == piv:
            out[k] = w[piv]
        elif piv is not None and k in cen:
            out[k] = w[piv] * w[k]
        else:
            out[k] = w[k]
    return out

def clearedFoldG(u, d, edges):
    v = dict(u)
    for e in reversed(edges):
        v = clearedStepMap(v, d, e)
    return v

def clearedFoldB(u, d, edges):
    if not edges:
        return sp.Integer(1)
    en = edges[-1]; rest = edges[:-1]
    piv, delta = en[3], en[5]
    fac = (u[piv] ** delta) if piv is not None else sp.Integer(1)
    return sp.expand(fac * clearedFoldB(clearedStepMap(u, d, en), d, rest))

def clearedFoldResid(u, d, edges):
    # coreGen ∘ (fold transforms with colClear at each δ=1 step) = sourceClearedResid at that node
    return [sp.expand(f) for f in coreGen(Phi_p(ancestor_column_clear_map(u, d, edges), d, edges, True), d)]

def in_ideal(f, gens, allv):
    f = sp.expand(f)
    if f == 0:
        return True
    nz = [sp.expand(g) for g in gens if sp.expand(g) != 0]
    if not nz:
        return False
    G = sp.groebner(nz, *allv, order='grevlex')
    return sp.expand(G.reduce(f)[1]) == 0

def verify(d):
    print("=" * 90)
    N, u = dims_coords(d)
    edges, meta = oracle_edges(d)
    allv = list(u.values())
    print(f"d={d}  branch={[(e[0], e[1], e[2], e[5]) for e in edges if e[0] != 'terminal']}")
    all_ok = True
    for ni in range(1, len(edges) + 1):
        path = edges[:ni]; last = edges[ni - 1]
        if last[0] == "terminal":
            continue
        clr = ancestor_column_clear_map(u, d, path)         # PRECOMPOSE the source-clear (the SOUND form)
        FGc = [sp.expand(f) for f in coreGen(foldG(clr, d, path), d)]   # clearedFoldG_C = foldG ∘ couplingClear
        Bc = sp.expand(foldB(clr, d, path))                  # clearedFoldB_C = foldB ∘ couplingClear (a monomial)
        C = clearedFoldResid(u, d, path)                     # sourceClearedResid
        Bfac = list(Bc.free_symbols)
        divok = all(all(sp.expand(f.subs(g, 0)) == 0 for g in Bfac) for f in FGc)
        gens = [sp.expand(Bc * c) for c in C]
        memb = all(in_ideal(f, gens, allv) for f in FGc)
        # FLAG: does the per-step INTERLEAVED clear (clear-before-blowup) match the precompose? (order test)
        FGstep = [sp.expand(f) for f in coreGen(clearedFoldG(u, d, path), d)]
        interleave_matches = all(sp.expand(a - b) == 0 for a, b in zip(FGc, FGstep))
        node_ok = divok and memb
        all_ok = all_ok and node_ok
        print(f"  node {ni} (child of {last[0]} δ={last[5]}): S1 clearedFoldB|coreGen∘G {divok}, "
              f"∈⟨B·C⟩ {memb}  [clearedFoldB={Bc}]  (interleave==precompose: {interleave_matches})")
    return all_ok

def verify_S2(d):
    """(S2) child sourceClearedResid = parent at the δ=1 strict-transform quot (the commutation)."""
    N, u = dims_coords(d)
    edges, meta = oracle_edges(d)
    idx = next(i for i, e in enumerate(edges) if e[0] == "case11")   # a δ=1 edge
    parent = edges[:idx]; child = edges[:idx + 1]; e = edges[idx]
    Cchild = clearedFoldResid(u, d, child)
    # parent C composed with the δ=1 fold transform (quot) of THIS edge:
    from capstone_stepinv_exists_q import fold_transform_apply
    qu = fold_transform_apply(ancestor_column_clear_map(u, d, child), d, e)  # quot on the cleared input
    Cparent_at_quot = [sp.expand(f) for f in coreGen(Phi_p(qu, d, parent, True), d)]
    ok = all(sp.expand(a - b) == 0 for a, b in zip(Cchild, Cparent_at_quot))
    print(f"  (S2) d={d}: child C == parent C ∘ (δ=1 strict-transform quot): {ok}")
    return ok

if __name__ == "__main__":
    print("### (S1)+(X): cleared StepInv at EVERY node (case11/case2/δ=0/rollover), 3 witnesses")
    r1 = all(verify(d) for d in [(2, 2, 2, 2), (2, 3, 2, 2), (3, 3, 2, 2)])
    print("\n### (S2): the child↔parent commutation (sourceClearedResid_extend_delta1)")
    r2 = all(verify_S2(d) for d in [(2, 2, 2, 2), (2, 3, 2, 2)])
    print("=" * 90)
    print(f"GLOBAL-MOVE SOUNDNESS: S1 (cleared StepInv all nodes) {r1}; S2 (commutation) {r2}")
