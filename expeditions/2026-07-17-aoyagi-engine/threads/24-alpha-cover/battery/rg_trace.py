#!/usr/bin/env python3
# pnp-rg (thread 24): the WRITE TRACE (part c). For the completed alpha (Aoyagi fwd: pivot-col Lg
# in-layer + pivot-row Rg forward -> C^{(S+1)}), log which C^{(S+1)} cells each node writes, and show
# the overlap structure: (i) consecutive SAME-LAYER edges write DISJOINT rows of C^{(S+1)} (row c per
# pivot c) but with a READ-WRITE chain; (ii) the layer-S Rg writes C^{(S+1)} which the DEEPER
# layer-(S+1) nodes ALSO read/write as their own layer matrix -> ancestor/descendant overlap.
import sympy as sp
from rg_shape import init_params, spine, beta_blowup, alpha_Lg, alpha_Rg_crosslayer

def node_completed_logged(P, M, S, c):
    w_layerS = set(); w_next = set()
    p = P[(S, c, c)]
    # Lg (pivot-col, in-layer)
    P, _ = alpha_Lg(P, M, S, c)
    # Rg (pivot-row) cross-layer, log separately
    f = {j: P[(S, c, j)] / p for j in range(c+1, M[S+1])}
    newP = dict(P)
    for j in range(c+1, M[S+1]):
        for i in range(M[S]):
            newP[(S, i, j)] = P[(S, i, j)] - f[j] * P[(S, i, c)]
            w_layerS.add((S, i, j))
    if S + 1 < len(M) - 1:
        for k in range(M[S+2]):
            newP[(S+1, c, k)] = P[(S+1, c, k)] + sum(f[j] * P[(S+1, j, k)] for j in range(c+1, M[S+1]))
            w_next.add((S+1, c, k))
    P = newP
    P, _ = beta_blowup(P, M, S, c)
    return P, w_layerS, w_next

def trace(M):
    print("=" * 88)
    print(f"M = {tuple(M)}   spine (root->leaf) = {spine(M)}")
    print(f"  leaf-first eval order (applied to source): {list(reversed(spine(M)))}")
    print("=" * 88)
    # run in leaf-first (tree) order, logging Rg cross-layer writes per node
    P = init_params(M)
    rg_writes = {}
    for (S, c) in reversed(spine(M)):
        P, wS, wN = node_completed_logged(P, M, S, c)
        rg_writes[(S, c)] = {"layerS_row_cleared": sorted(wS), "C^{S+1}_writes": sorted(wN)}
    print("\n-- per-node cross-layer Rg writes into C^{(S+1)} (cell = (layer, i, j)) --")
    for node in spine(M):
        wN = rg_writes[node]["C^{S+1}_writes"]
        if wN:
            print(f"  node {node}:  Rg writes C^(S+1) cells {wN}")
        else:
            print(f"  node {node}:  (last layer -- Rg in-layer, no C^(S+1))")
    # overlap analyses
    print("\n-- (i) SAME-LAYER consecutive edges: do their C^{(S+1)} write-cells overlap? --")
    L = len(M) - 1
    def wmin(n): return min(M[:n+1])
    for S in range(L):
        rows = {}
        for c in range(wmin(S+1)):
            wN = set(rg_writes[(S, c)]["C^{S+1}_writes"])
            rows[c] = wN
        for c in range(wmin(S+1)):
            for c2 in range(c+1, wmin(S+1)):
                inter = rows[c] & rows[c2]
                print(f"   layer {S}: node (S,{c}) writes {sorted(rows[c])}")
                print(f"            node (S,{c2}) writes {sorted(rows[c2])}  -> WRITE overlap: {sorted(inter) if inter else 'DISJOINT'}")
    print("\n-- (ii) ANCESTOR layer-S Rg vs DESCENDANT layer-(S+1) node's OWN layer matrix --")
    # layer-(S+1) nodes operate on C^{(S+1)} (their own layer). Do the cells overlap the layer-S Rg writes?
    for S in range(L - 1):
        anc = set()
        for c in range(wmin(S+1)):
            anc |= set(rg_writes[(S, c)]["C^{S+1}_writes"])
        # descendant layer-(S+1) nodes' own-layer cells = all cells of layer S+1 (they blow up / Schur it)
        desc_layer = {(S+1, i, j) for i in range(M[S+1]) for j in range(M[S+2])}
        inter = anc & desc_layer
        print(f"   layer {S} Rg writes into C^({S+1}): {sorted(anc)}")
        print(f"   layer {S+1} nodes' own matrix C^({S+1}) cells: (all {M[S+1]}x{M[S+2]})")
        print(f"   -> OVERLAP (ancestor writes cells the descendant layer reads/writes): {sorted(inter) if inter else 'NONE'}")
        print(f"      In leaf-first eval, layer {S+1} (descendant) is applied BEFORE layer {S} (ancestor),")
        print(f"      so the Rg write lands AFTER layer {S+1} already consumed C^({S+1}) -> reduction cannot complete.")

if __name__ == "__main__":
    trace([2, 2, 2])
    trace([2, 2, 2, 2])
