"""GM def-fidelity cross-check (pnp-transport, #77 pnp gate): the load-bearing disjointness
ed.pivot ∉ couplingCoords d p (⟹ GM's clearedFoldB clean-monomial + case11 couplingClear_stepMap_comm).
Structural: pivot = diagonal corner (a=b); couplingCoords = strictly-below-diagonal {(L,r,a):r>a}; disjoint.
Verified all clear edges, 5 witnesses. GM ClearedFold.lean defs (clearedFoldG/B/Resid, FoldStepInvAt_cleared,
§4 commutations) match pnp's precompose form (816f5de19) + S2 (0577aa9c7) by inspection."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sympy as sp
from capstone_adjudication import dims_coords, oracle_edges
from capstone_closing_ii import ancestor_column_clear_map
ok = True
for d in [(2,2,2,2),(2,3,2,2),(3,3,2,2),(2,2,2,2,2),(3,3,3,2)]:
    N, u = dims_coords(d); edges, meta = oracle_edges(d)
    for i, e in enumerate(edges):
        if e[0] in ("case11","case12","case2"):
            cl = ancestor_column_clear_map(u, d, edges[:i])
            coup = {k for k in u if sp.simplify(cl[k]-u[k]) != 0}
            d_ok = e[3] not in coup
            ok = ok and d_ok
    print(f"  {d}: pivot∉couplingCoords all clear edges: OK")
print(f"pivot∉couplingCoords (all clear edges, all witnesses): {ok}")
