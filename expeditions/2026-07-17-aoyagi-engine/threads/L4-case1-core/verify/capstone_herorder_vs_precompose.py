"""
HER-ORDER vs PRECOMPOSE (pnp-transport, team-lead commission).

Q: does Aoyagi's LITERAL per-step order — BLOW UP then CLEAR (Q,P on the post-blow-up residual D_J'') —
equal the precompose cleared fold (foldG ∘ globalCouplingClear)?  Decides:
 (1) DESIGN: may seat-GM use a per-step recursion in HER order, or must it precompose?
 (2) FIDELITY: which object is sourceClearedResid relative to her carried diag(b)·[E_J|D_J]?

SOURCE for her step order — theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex:613-629:
 "Blow up {d_ij=0, u_{s,k}=0}" (:613 Case1, :622 Case2) THEN "regular transforms Q,P reduce D_J'' to
 [[1,O],[O,D_{J+1}]]" (:619 Case1(2), :628 Case2).  Order = blow-up → clear, clear acts on the POST-blow-up
 residual D_J''.

HER-ORDER per-step map: herStep(v) = [clear pivot col below-pivot IN THE BLOWN-UP coords] ∘ blockBlowupMap ∘ shear.
Compare coreGen∘(∘ herStep) vs coreGen∘(foldG ∘ globalCouplingClear) per-node, exact.
(Also compare the two RESIDUALS: her-order fold-residual vs sourceClearedResid.)
"""
import sympy as sp
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, coreGen, Phi_p
from capstone_closing_ii import ancestor_column_clear_map
from capstone_stepinv_exists_q import shear, foldG

def herStepMap(v, d, e):
    """blow-up THEN clear (her order): blockBlowupMap∘shear, then zero pivot col below-pivot in blown-up coords."""
    case, sL, sC, piv, cen, delta = e
    w = shear(v, d, case, sL, sC, piv)
    bu = {}
    for k in v:
        if piv is not None and k == piv:
            bu[k] = w[piv]
        elif piv is not None and k in cen:
            bu[k] = w[piv] * w[k]
        else:
            bu[k] = w[k]
    if delta == 1 and piv is not None and case != "rollover":
        a, b = piv[1], piv[2]
        for (L, r, c) in list(bu.keys()):
            if L == sL and c == b and r > a:       # Q,P clear on the POST-blow-up residual
                bu[(L, r, c)] = sp.Integer(0)
    return bu

def herFoldG(u, d, edges):
    v = dict(u)
    for e in reversed(edges):
        v = herStepMap(v, d, e)
    return v

def run(d):
    print("=" * 88)
    N, u = dims_coords(d)
    edges, meta = oracle_edges(d)
    print(f"d={d}")
    all_match_G = True; all_match_R = True
    for ni in range(1, len(edges) + 1):
        path = edges[:ni]; last = edges[ni - 1]
        if last[0] == "terminal":
            continue
        clr = ancestor_column_clear_map(u, d, path)
        # coreGen∘foldG: her-order vs precompose
        FGher = [sp.expand(f) for f in coreGen(herFoldG(u, d, path), d)]
        FGpre = [sp.expand(f) for f in coreGen(foldG(clr, d, path), d)]
        mg = all(sp.expand(a - b) == 0 for a, b in zip(FGher, FGpre))
        all_match_G = all_match_G and mg
        print(f"  node {ni} (child of {last[0]} δ={last[5]}): coreGen∘foldG her-order == precompose: {mg}")
    return all_match_G

if __name__ == "__main__":
    res = {d: run(d) for d in [(2, 2, 2, 2), (2, 3, 2, 2), (3, 3, 2, 2)]}
    print("=" * 88)
    print("HER-ORDER (blow-up→clear) == PRECOMPOSE (global-clear→blow-up), per coreGen∘foldG:")
    for d, v in res.items():
        print(f"  {d}: {'EQUAL' if v else 'DIFFERENT'}")
    print("EQUAL ⟹ seat-GM may use her per-step order (= precompose, both sound); DIFFERENT ⟹ they are"
          "\n  distinct objects — report which sourceClearedResid is relative to (fidelity → elder).")
