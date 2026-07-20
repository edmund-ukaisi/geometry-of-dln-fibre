#!/usr/bin/env python3
# pnp-rg (thread 24): is the leaf-first FAILURE of the cross-layer Rg a fundamental ORIENTATION
# mismatch, or a fixable sign/coupling-direction? Search completions x orders. Exact symbolic.
# The tree composes LEAF-FIRST (deepest node applied first; root=layer-0). Aoyagi's reduction is
# root-first (layer 0 first). A BACKWARD coupling (layer S+1's transform -> layer S) matches the
# leaf-first deepest-first processing of the TRANSPOSE reduction (process layers right-to-left).
import sympy as sp
from rg_shape import init_params, prod_of, is_diag, offdiag, spine, beta_blowup

def alpha_Lg(P, M, s, c, sign=-1):
    newP = dict(P); p = P[(s, c, c)]
    for i in range(c+1, M[s]):
        f = P[(s, i, c)] / p
        for j in range(c, M[s+1]):
            newP[(s, i, j)] = P[(s, i, j)] + sign * f * P[(s, c, j)]
    return newP

def alpha_Rg_fwd(P, M, s, c):
    """clear layer-s pivot ROW (col op) + compensate layer s+1 (row op, forward S->S+1)."""
    newP = dict(P); p = P[(s, c, c)]
    f = {j: P[(s, c, j)] / p for j in range(c+1, M[s+1])}
    for j in range(c+1, M[s+1]):
        for i in range(M[s]):
            newP[(s, i, j)] = P[(s, i, j)] - f[j] * P[(s, i, c)]
    if s + 1 < len(M) - 1:
        for k in range(M[s+2]):
            newP[(s+1, c, k)] = P[(s+1, c, k)] + sum(f[j] * P[(s+1, j, k)] for j in range(c+1, M[s+1]))
    return newP

def alpha_Lg_bwd(P, M, s, c):
    """clear layer-s pivot COLUMN (row op) + compensate layer s-1 (col op, backward S->S-1).
       Transpose of Rg_fwd. row_i -= (a[i,c]/p) row_c (i>c); layer s-1 col c += sum_{i>c} f_i col_i."""
    newP = dict(P); p = P[(s, c, c)]
    f = {i: P[(s, i, c)] / p for i in range(c+1, M[s])}
    for i in range(c+1, M[s]):
        for j in range(M[s+1]):
            newP[(s, i, j)] = P[(s, i, j)] - f[i] * P[(s, c, j)]
    if s - 1 >= 0:
        for k in range(M[s-1]):
            newP[(s-1, k, c)] = P[(s-1, k, c)] + sum(f[i] * P[(s-1, k, i)] for i in range(c+1, M[s]))
    return newP

def alpha_Rg_inlayer(P, M, s, c):
    newP = dict(P); p = P[(s, c, c)]
    f = {j: P[(s, c, j)] / p for j in range(c+1, M[s+1])}
    for j in range(c+1, M[s+1]):
        for i in range(M[s]):
            newP[(s, i, j)] = P[(s, i, j)] - f[j] * P[(s, i, c)]
    return newP

# node variants (each: apply cleared alpha pieces then beta)
def make_node(pieces):
    def node(P, M, S, c):
        for pf in pieces:
            P = pf(P, M, S, c)
        P, _ = beta_blowup(P, M, S, c)
        return P
    return node

NODES = {
    "fwd: Lg(in) + Rg(fwd->S+1)":  make_node([alpha_Lg, alpha_Rg_fwd]),
    "bwd: Rg(in) + Lg(bwd->S-1)":  make_node([alpha_Rg_inlayer, alpha_Lg_bwd]),
    "in-layer full_QP":            make_node([alpha_Lg, alpha_Rg_inlayer]),
}

def build(M, node, order):
    P = init_params(M)
    seq = list(reversed(spine(M))) if order == "leaf_first" else list(spine(M))
    for (S, c) in seq:
        P = node(P, M, S, c)
    return P

if __name__ == "__main__":
    for M in [[2, 2, 2], [2, 2, 2, 2]]:
        print("=" * 92); print(f"M = {tuple(M)}"); print("=" * 92)
        for name, node in NODES.items():
            for order in ["leaf_first", "root_first"]:
                Pr = prod_of(build(M, node, order), M)
                d = is_diag(Pr)
                extra = ""
                if not d:
                    extra = f"  (#offdiag={len(offdiag(Pr))})"
                print(f"  [{name:32s}] [{order:10s}] diagonal? {d}{extra}")
