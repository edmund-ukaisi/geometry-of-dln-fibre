"""
Decorrelated confirmation of seat-KILL's inductive-structure finding: Z ("sourceClearedResid p ignores
escapedBelow(p)", couplingClear p clears ONLY couplings(p)) is a correct STATEMENT but NOT function-level
self-inductive at the last clear.

At node5=(1,1) [parent p'] → node6=(1,2) [child q, last clear of layer 1, new coupling (1,2,1)]:
the parent's escaped(2)-coefficient is killed by the CHILD's accumulated couplings(node6) but NOT by the
parent's own couplings(node5). So the IH (couplings(p')-clear) cannot supply the vanishing the step needs.
This is the exact-algebra basis for #92's ruling: the kill is MULTI-LAYER, riding the ACCUMULATED
all-layer couplingCoords (layer-descent induction, à la foldResid_layerHomogeneous'), NOT a per-node Z.
"""
import sympy as sp
from cap_frontier_sufficiency import make, widthMinUpto, real_foldResid

def cc(d, S, J):
    cap = widthMinUpto(d, S)
    return {(L, r, c) for (L, r, c) in make(d)[1] if L == S and J <= r and J <= c and c < cap}

def couplings(d, pivots):
    S = set()
    for (pL, pa, pb) in pivots:
        S |= {(pL, r, pb) for r in range(d[pL + 1]) if r > pa}
    return S

d = (2, 3, 3, 3); N, u = make(d)
base = [("case2", 0, 0, (0, 0, 0), cc(d, 0, 0), 1),
        ("case2", 0, 1, (0, 1, 1), cc(d, 0, 1), 0),
        ("rollover", 0, 2, (1, 0, 0), set(), 0)]
node5 = base + [("case2", 1, 0, (1, 0, 0), cc(d, 1, 0), 1)]                                  # (1,1)
node6 = node5 + [("case2", 1, 1, (1, 1, 1), cc(d, 1, 1), 0)]                                 # (1,2)
r5 = real_foldResid(u, d, node5)
c5 = couplings(d, [(0, 0, 0), (0, 1, 1), (1, 0, 0)])
c6 = couplings(d, [(0, 0, 0), (0, 1, 1), (1, 0, 0), (1, 1, 1)])
esc = [k for k in u if k[0] == 2 and k[2] >= widthMinUpto(d, 2)]
z5 = {u[k]: 0 for k in c5}; z6 = {u[k]: 0 for k in c6}
print(f"couplings(node5)={sorted(c5)}\ncouplings(node6)={sorted(c6)}  new={sorted(c6 - c5)}")
own_ok = child_ok = True
for j, f in enumerate(r5):
    f = sp.expand(f)
    for m in esc:
        cm = sp.expand(f.coeff(u[m], 1))
        if cm == 0:
            continue
        own = (sp.expand(cm.subs(z5)) == 0); chld = (sp.expand(cm.subs(z6)) == 0)
        own_ok = own_ok and own; child_ok = child_ok and chld
        print(f"  node5 slot{j} u_{m}: killed by own couplings(node5)? {own}  by child's couplings(node6)? {chld}")
print(f"\nZ function-level self-inductive at last clear (parent killed by OWN couplings)? {own_ok}")
print(f"Parent's escaped-coeff killed by CHILD's accumulated couplings?               {child_ok}")
assert (not own_ok) and child_ok, "diagnostic mismatch — re-examine"
print("CONFIRMED: Z needs the ACCUMULATED (child-level) couplingCoords — multi-layer descent, not per-node Z.")
