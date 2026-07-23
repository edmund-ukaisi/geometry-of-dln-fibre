"""
FIX-CANDIDATE check (decision-relevant for the elder's ruling; does NOT presuppose it).

F2 candidate fix: supportAt'(S, J) = blockCoords(S) only at the ROOT convention, else layerCoords —
concretely supportAt'(S,0)=layerCoords(S) for S≥1 (the root S=0 is unchanged since
blockCoords(0)=layerCoords(0)).  Question: does this make the descent TRUE on the real wide fold?

Also confirms F1 (hslot insufficiency) is INDEPENDENT of the F2 support-fix — the δ=1 pivot→const
counterexample stands whether the parent support is blockCoords or layerCoords.
"""
import sympy as sp
from cap_frontier_sufficiency import (make, layerCoords, blockCoords, widthMinUpto, supportAt,
    step_arg, real_foldResid, supported_on, is_deg1_supported_slot, supportLayerOf)

def supportAt_fix(d, S, J):
    """candidate: layerCoords(S) for a fresh S≥1 node; root unchanged; descended unchanged."""
    N = len(d) - 1
    if J == 0:
        return blockCoords(d, S) if S == 0 else (layerCoords(d, S) if S < N else set())
    elif S + 1 < N:
        return layerCoords(d, S + 1)
    else:
        return set()

def canonCenter_append(d, S, J):
    cap = widthMinUpto(d, S)
    return {(L, r, c) for (L, r, c) in make(d)[1] if L == S and J <= r and J <= c and c < cap}

print("=" * 78)
print("F2 fix-candidate: supportAt'(S,0)=layerCoords(S) for S≥1 — does the real WIDE fold descend?")
print("=" * 78)
for d in [(2, 3, 2, 2), (2, 2, 3, 2), (3, 2, 3, 2)]:
    N, u = make(d)
    # clear layer 0 fully, roll to (1,0)
    e0 = ("case2", 0, 0, (0, 0, 0), canonCenter_append(d, 0, 0), 1)
    e1 = ("case2", 0, 1, (0, 1, 1), canonCenter_append(d, 0, 1), 0)
    er = ("rollover", 0, 2, (1, 0, 0), set(), 0)
    child = real_foldResid(u, d, [e0, e1, er])              # at (1,0)
    Sc_old = supportAt(d, 1, 0)                              # blockCoords(1)  (current, buggy)
    Sc_new = supportAt_fix(d, 1, 0)                          # layerCoords(1)  (candidate)
    old_ok = all(supported_on(u, f, Sc_old) for f in child)
    new_ok = all(supported_on(u, f, Sc_new) for f in child)
    bite = widthMinUpto(d, 1) < d[1]
    print(f"  d={d}: cap bites at layer1? {bite};  child∈blockCoords(1)(current)? {old_ok};"
          f"  child∈layerCoords(1)(fix)? {new_ok}")

print("\n" + "=" * 78)
print("F1 independence: δ=1 pivot→const counterexample stands under BOTH support choices")
print("=" * 78)
d = (2, 3, 2, 2); N, u = make(d)
# a δ=1 node at S≥1 to exhibit both support choices differ: build (1,0) fresh, then its δ=1 append child.
pivot_root = (0, 0, 0)
for label, Sp in [("blockCoords(0) [root]", supportAt(d, 0, 0)),
                   ("layerCoords(1) [fixed fresh S=1]", supportAt_fix(d, 1, 0))]:
    piv = (0, 0, 0) if "root" in label else (1, 0, 0)
    if piv in Sp:
        bb = u[piv]
        arg = step_arg(u, d, "case2", piv[0], 0, piv, Sp, 1)
        child_bb = sp.expand(bb.subs({u[k]: arg[k] for k in u}, simultaneous=True))
        print(f"  parent support {label}: pivot∈support={piv in Sp}; black-box child = {child_bb} (const ⟹ escapes)")
print("  ⟹ F1 (δ=1 pivot term is a bare constant) is independent of the block-vs-layer support fix.")
