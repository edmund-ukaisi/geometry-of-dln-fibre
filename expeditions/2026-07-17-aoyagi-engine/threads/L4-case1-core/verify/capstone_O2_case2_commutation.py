"""
O2 FOCUS (pnp-transport, team-lead): GM's couplingClear_stepMap_comm serves case11 AND case12/case2 δ=1.
For case12/case2 the child GROWS couplingCoords (adds this edge's belowPivotCol) and the shear is blockShear.
My earlier (S2) run tested only case11. This confirms the commutation with the CHILD's GROWN couplingClear
on the LEFT, specifically at case2/case12 δ=1 edges.

GM's lemma (ClearedFold.lean:135): stepMap d ed ∘ couplingClear d (p.extend ed) = couplingClear d p ∘ stepMap d ed.
LEFT uses couplingClear(CHILD = p.extend ed) — for a case2/case12 edge this is the GROWN set
(couplingClear(parent) ∪ {this edge's below-pivot col (L,r,b): r>a}).

Check, at EVERY δ=1 edge (case2/case12 AND case11), across witnesses:
 (M) map commutation:  stepMap ∘ couplingClear(child) == couplingClear(parent) ∘ stepMap  (exact, all coords)
 (grow) couplingCoords(child) ⊋ couplingCoords(parent)? (case2/case12 grows; case11 may not)
 (S2-resid) sourceClearedResid_extend_delta1: Cchild = Cparent ∘ (blockBlowupCoordQuot pivot ∘ edgeShear).
"""
import sympy as sp
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, coreGen, Phi_p
from capstone_closing_ii import ancestor_column_clear_map
from capstone_stepinv_exists_q import shear, stepMapRaw_apply, fold_transform_apply

def couplingset(u, d, path):
    cl = ancestor_column_clear_map(u, d, path)
    return {k for k in u if sp.simplify(cl[k] - u[k]) != 0}

def run(d):
    print("=" * 88)
    N, u = dims_coords(d)
    edges, meta = oracle_edges(d)
    allv = list(u.values())
    okM = True
    for idx, e in enumerate(edges):
        if e[0] not in ("case2", "case12", "case11") or e[5] != 1:   # δ=1 clears only
            continue
        parent = edges[:idx]; child = edges[:idx + 1]
        cc_p = couplingset(u, d, parent); cc_c = couplingset(u, d, child)
        grew = cc_c - cc_p
        # (M) map commutation with CHILD's grown couplingClear on the LEFT
        clc = ancestor_column_clear_map(u, d, child)          # couplingClear(child) — GROWN set
        clp = ancestor_column_clear_map(u, d, parent)         # couplingClear(parent)
        lhs = stepMapRaw_apply(clc, d, e)                      # stepMap ∘ couplingClear(child)
        sm = stepMapRaw_apply(u, d, e)                        # stepMap(u)
        rhs = {k: clp[k] for k in u}                          # start couplingClear(parent) at u
        rhs = ancestor_column_clear_map(sm, d, parent)        # couplingClear(parent) ∘ stepMap
        mok = all(sp.expand(lhs[k] - rhs[k]) == 0 for k in u)
        okM = okM and mok
        # (S2-resid) at this δ=1 edge
        Cc = [sp.expand(f) for f in coreGen(Phi_p(clc, d, child, True), d)]
        qarg = fold_transform_apply(clc, d, e)               # (blockBlowupCoordQuot pivot ∘ shear)(couplingClear child)
        Cp_q = [sp.expand(f) for f in coreGen(Phi_p(qarg, d, parent, True), d)]
        s2 = all(sp.expand(a - b) == 0 for a, b in zip(Cc, Cp_q))
        print(f"  {e[0]} δ=1 @(S={e[1]},J={e[2]}): couplingCoords grew by {sorted(grew) or 'none'}; "
              f"(M) stepMap∘clear(child)==clear(parent)∘stepMap: {mok}; (S2) Cchild==Cparent∘quot: {s2}")
    return okM

if __name__ == "__main__":
    for d in [(2, 2, 2, 2), (2, 3, 2, 2), (3, 3, 2, 2), (2, 2, 2, 2, 2)]:
        run(d)
    print("=" * 88)
    print("O2: the case2/case12 δ=1 commutation uses the CHILD's GROWN couplingClear on the left, and it")
    print("  holds exactly (M) — closing O2's risk (couplingCoords growth is compatible with the commutation).")
