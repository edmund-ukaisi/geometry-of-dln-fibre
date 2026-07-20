#!/usr/bin/env python3
# pnp-rg (thread 24): WHERE does the cross-layer Rg go? Map the placement space in the TREE's
# leaf-first composition (deepest node applied FIRST to source; root = layer-0 pivot-0 applied LAST,
# per GeoAlphaGauge tGeoG: chartMap = C_root o ... o C_deepest). Compare against Aoyagi's faithful
# diagonal (root-first = reduction order). Exact symbolic. Builds on rg_shape.py primitives.
import sympy as sp
from rg_shape import (init_params, prod_of, is_diag, offdiag, spine,
                      beta_blowup, alpha_Lg, alpha_Rg_crosslayer)

def alpha_Rg_inlayer(P, M, s, c):
    """clear layer-s pivot row IN PLACE (pnp-diag full_QP style, no cross-layer)."""
    newP = dict(P); writ = set()
    p = P[(s, c, c)]
    f = {j: P[(s, c, j)] / p for j in range(c+1, M[s+1])}
    for j in range(c+1, M[s+1]):
        for i in range(M[s]):
            newP[(s, i, j)] = P[(s, i, j)] - f[j] * P[(s, i, c)]
            writ.add((s, i, j))
    return newP, writ

def node_crosslayer(P, M, S, c):
    P, _ = alpha_Lg(P, M, S, c)
    P, _ = alpha_Rg_crosslayer(P, M, S, c)
    P, _ = beta_blowup(P, M, S, c)
    return P

def node_inlayer(P, M, S, c):
    P, _ = alpha_Lg(P, M, S, c)
    P, _ = alpha_Rg_inlayer(P, M, S, c)
    P, _ = beta_blowup(P, M, S, c)
    return P

def build(M, node_fn, order_mode):
    P = init_params(M)
    order = list(reversed(spine(M))) if order_mode == "leaf_first" else list(spine(M))
    for (S, c) in order:
        P = node_fn(P, M, S, c)
    return P

def report(M, tag, node_fn, order_mode):
    Pr = prod_of(build(M, node_fn, order_mode), M)
    d = is_diag(Pr)
    diag = [sp.factor(Pr[i, i]) for i in range(min(Pr.shape))] if d else None
    if d:
        print(f"  [{tag:26s}] [{order_mode:10s}] diagonal? True   diag = {diag}")
    else:
        od = offdiag(Pr)
        print(f"  [{tag:26s}] [{order_mode:10s}] diagonal? False  (#offdiag={len(od)})")
    return d, diag

if __name__ == "__main__":
    for M in [[2, 2, 2], [2, 2, 2, 2]]:
        print("=" * 96); print(f"M = {tuple(M)}   spine = {spine(M)}"); print("=" * 96)
        dA, diagA = report(M, "cross-layer Rg (Aoyagi)", node_crosslayer, "root_first")
        report(M, "cross-layer Rg (Aoyagi)", node_crosslayer, "leaf_first")
        dB1, diagB1 = report(M, "in-layer full_QP", node_inlayer, "leaf_first")
        dB2, diagB2 = report(M, "in-layer full_QP", node_inlayer, "root_first")
        # do in-layer and Aoyagi agree on the diagonal (VALUE fidelity)?
        if dA and dB1:
            same = all(sp.simplify(a - b) == 0 for a, b in zip(diagA, diagB1))
            print(f"  >> in-layer(leaf) diag == Aoyagi diag ? {same}   "
                  f"(if False, in-layer is a DIFFERENT reduction / wrong b-chain)")
