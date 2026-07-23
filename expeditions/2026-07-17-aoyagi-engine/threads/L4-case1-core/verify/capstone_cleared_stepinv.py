"""
#74 — CLEARED-StepInv SOUNDNESS (the global-move render gate; pnp-transport).

The raw case11 child StepInv ∃q FAILED (capstone_stepinv_exists_q.py): foldB ∤ coreGen∘foldG (slots 0,2),
because the case11 small-center blow-up left the coupling terms (u₀₁₀·extra) without the u₀₁₁ factor.
The forced GLOBAL MOVE re-architects FoldStepInvAt onto the cleared object. This checks the move is SOUND:
does the CLEARED StepInv hold?

Natural cleared-fold (precompose the source-clear on the raw input; def-choice flagged — L4D owns the exact
re-architecture): with clear = ancestor-column-clear,
   coreGen∘foldG_cleared(u) := coreGen(foldG(clear(u))),
   foldB_cleared(u)         := foldB(clear(u)),          [pivots u₀₀₀,u₀₁₁ NOT cleared ⟹ = u₀₀₀·u₀₁₁]
   C_j(u)                    := sourceClearedResid_j = coreGen(foldTransform(clear(u))).
CHECK: coreGen∘foldG_cleared ∈ ⟨ foldB_cleared · C_j : j ⟩ (Gröbner, ⟹ ∃ polynomial/continuous q) AND
       foldB_cleared | coreGen∘foldG_cleared (the necessary coord-divisibility, now expected TRUE since the
       source-clear removes the u₀₁₀-coupling terms that lacked u₀₁₁).
HOLDS ⟹ the global move is SOUND (cleared StepInv provable per-node); FAILS ⟹ deeper problem, flag.
"""
import sympy as sp
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, coreGen, Phi_p
from capstone_closing_ii import ancestor_column_clear_map
from capstone_stepinv_exists_q import foldG, foldB

def in_ideal(f, gens, allv):
    f = sp.expand(f)
    if f == 0:
        return True
    nz = [sp.expand(g) for g in gens if sp.expand(g) != 0]
    if not nz:
        return False
    G = sp.groebner(nz, *allv, order='grevlex')
    return sp.expand(G.reduce(f)[1]) == 0

def run(d):
    print("=" * 88)
    N, u = dims_coords(d)
    edges, meta = oracle_edges(d)
    idx = next(i for i, e in enumerate(edges) if e[0] == "case11")
    child = edges[:idx + 1]
    allv = list(u.values())
    clr = ancestor_column_clear_map(u, d, child)              # source-clear on raw input (function of u)
    # cleared objects as functions of u:
    FGc = [sp.expand(f) for f in coreGen(foldG(clr, d, child), d)]    # coreGen∘foldG_cleared
    Cj = [sp.expand(f) for f in coreGen(Phi_p(clr, d, child, True), d)]  # sourceClearedResid_j (child)
    Bc = sp.expand(foldB(clr, d, child))                     # foldB_cleared
    print(f"d={d}: foldB_cleared = {Bc}")
    # necessary coord-divisibility
    Bfac = list(Bc.free_symbols)
    divok = [all(sp.expand(f.subs(g, 0)) == 0 for g in Bfac) for f in FGc]
    print(f"  foldB_cleared | coreGen∘foldG_cleared per-slot: {divok}")
    # ideal membership
    gens = [sp.expand(Bc * c) for c in Cj]
    memb = [in_ideal(f, gens, allv) for f in FGc]
    print(f"  coreGen∘foldG_cleared_i ∈ ⟨foldB_cleared·C_j⟩ per-slot: {memb}")
    dpv = all(sp.expand(f.subs({v: 0 for v in allv})) == 0 for f in FGc)
    verdict = all(divok) and all(memb) and dpv
    print(f"  deepest-point vanish: {dpv}")
    print(f"  ⟹ CLEARED StepInv ∃q HOLDS (global move SOUND): {verdict}")
    return verdict

if __name__ == "__main__":
    res = {d: run(d) for d in [(2, 2, 2, 2), (2, 3, 2, 2), (3, 3, 2, 2)]}
    print("=" * 88)
    print("CLEARED StepInv soundness (global-move render gate):")
    for d, v in res.items():
        print(f"  {d}: {'SOUND' if v else 'FAILS — flag'}")
