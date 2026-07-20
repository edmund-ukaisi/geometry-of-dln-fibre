#!/usr/bin/env python3
# pnp-rg (thread 24): EXHAUSTIVE search -- is there ANY completed-alpha config that gives a CLEAN
# (polynomial, no denominators) monomialization matching Aoyagi's b-chain, in the TREE's LEAF-FIRST
# composition order? Vary interior/Lg/Rg sign and coupling (in-layer / forward S+1 / backward S-1).
# Reference "correct" = fwd-root-first (Aoyagi) diagonal. Exact symbolic.
import sympy as sp
from rg_shape import init_params, prod_of, is_diag, spine, beta_blowup

def piv_col_clear(P, M, s, c, sign, couple):
    """clear pivot COLUMN of layer s (row op, rows i>c). couple in {'in','bwd'}: 'bwd' compensates
       layer s-1 col c."""
    newP = dict(P); p = P[(s, c, c)]
    fdict = {i: P[(s, i, c)] / p for i in range(c+1, M[s])}
    for i in range(c+1, M[s]):
        for j in range(M[s+1]):
            newP[(s, i, j)] = P[(s, i, j)] + sign * fdict[i] * P[(s, c, j)]
    if couple == 'bwd' and s - 1 >= 0:
        for k in range(M[s-1]):
            newP[(s-1, k, c)] = P[(s-1, k, c)] - sign * sum(fdict[i] * P[(s-1, k, i)] for i in range(c+1, M[s]))
    return newP

def piv_row_clear(P, M, s, c, sign, couple):
    """clear pivot ROW of layer s (col op, cols j>c). couple in {'in','fwd'}: 'fwd' compensates
       layer s+1 row c."""
    newP = dict(P); p = P[(s, c, c)]
    fdict = {j: P[(s, c, j)] / p for j in range(c+1, M[s+1])}
    for j in range(c+1, M[s+1]):
        for i in range(M[s]):
            newP[(s, i, j)] = P[(s, i, j)] + sign * fdict[j] * P[(s, i, c)]
    if couple == 'fwd' and s + 1 < len(M) - 1:
        for k in range(M[s+2]):
            newP[(s+1, c, k)] = P[(s+1, c, k)] - sign * sum(fdict[j] * P[(s+1, j, k)] for j in range(c+1, M[s+1]))
    return newP

def make_node(col_sign, col_couple, row_sign, row_couple, beta_first=False):
    def node(P, M, S, c):
        if beta_first:
            P, _ = beta_blowup(P, M, S, c)
        P = piv_col_clear(P, M, S, c, col_sign, col_couple)
        P = piv_row_clear(P, M, S, c, row_sign, row_couple)
        if not beta_first:
            P, _ = beta_blowup(P, M, S, c)
        return P
    return node

def build(M, node, order):
    P = init_params(M)
    seq = list(reversed(spine(M))) if order == "leaf_first" else list(spine(M))
    for (S, c) in seq:
        P = node(P, M, S, c)
    return P

def is_poly_diag(Pr):
    """diagonal, all diagonal entries polynomial (no free-symbol denominators)."""
    if not is_diag(Pr):
        return False, None
    diag = [sp.together(sp.simplify(Pr[i, i])) for i in range(min(Pr.shape))]
    poly = all(sp.denom(sp.cancel(d)).free_symbols == set() for d in diag)
    return poly, [sp.factor(d) for d in diag]

if __name__ == "__main__":
    M = [2, 2, 2]
    # reference: Aoyagi fwd-root diagonal (clean)
    ref_node = make_node(-1, 'in', -1, 'fwd')
    refPr = prod_of(build(M, ref_node, "root_first"), M)
    _, refdiag = is_poly_diag(refPr)
    refset = set(sp.factor(x) for x in refdiag)
    print("Aoyagi reference (fwd, root_first) diag:", refdiag)
    print("=" * 90)
    hits = []
    for cs in (-1, 1):
      for cc in ('in', 'bwd'):
        for rs in (-1, 1):
          for rc in ('in', 'fwd'):
            for bf in (False, True):
                node = make_node(cs, cc, rs, rc, bf)
                for order in ("leaf_first", "root_first"):
                    Pr = prod_of(build(M, node, order), M)
                    poly, diag = is_poly_diag(Pr)
                    if poly:
                        match = set(sp.factor(x) for x in diag) == refset
                        tag = f"col(sign={cs:+d},{cc}) row(sign={rs:+d},{rc}) beta_first={bf} [{order}]"
                        flag = "  <== CLEAN+CORRECT" if match else "  (clean, DIFFERENT b-chain)"
                        if order == "leaf_first" or match:
                            print(f"{tag}{flag}")
                        if match and order == "leaf_first":
                            hits.append(tag)
    print("=" * 90)
    print("LEAF-FIRST configs that are CLEAN + CORRECT (Aoyagi b-chain):", hits if hits else "NONE")
