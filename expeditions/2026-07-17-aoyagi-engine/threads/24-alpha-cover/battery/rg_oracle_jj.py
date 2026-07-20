#!/usr/bin/env python3
# pnp-rg (thread 24): (1) confirm the completed-alpha leaf == clear_pivot ORACLE (loss-t15) incl.
# DROPPED rows zeroed on a width-drop M; (2) the (J,J)-fixed check per factor (interior/Lg/Rg/beta);
# (3) disambiguate Lg cells (in-layer vs cross-cell -> S-1) by matching the oracle. Exact sympy.
import sympy as sp
import importlib.util, os

# import clear_pivot oracle from loss-t15
_spec = importlib.util.spec_from_file_location("cwt", os.path.join(
    os.path.dirname(__file__), "..", "..", "19-loss-factorization", "battery", "clearedof_walk_trace.py"))
cwt = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(cwt)

from rg_shape import init_params, layer_mat, prod_of, is_diag, spine, beta_blowup

def wmin(M, n): return min(M[:n+1])

# ---- oracle: run clear_pivot's prefix reduction, return final prod (the acceptance target) ----
def oracle_prod(M):
    L = len(M) - 1
    layers = [cwt.gen_layer(M[s], M[s+1], f'a{s}') for s in range(L)]
    P = layers[0].as_mutable()
    for S in range(L):
        cap = cwt.widthMinUpto(M, S+1)
        for J in range(1, cap+1):
            P = cwt.clear_pivot(P, J-1)
        if S+1 < L:
            P = sp.simplify(P * layers[S+1])
    return sp.simplify(P)

# ---- completed-alpha node variants (per-factor, logging (J,J)) ----
def interior_schur(P, M, S, c):
    newP = dict(P); w = set()
    for i in range(c+1, M[S]):
        for j in range(c+1, M[S+1]):
            newP[(S, i, j)] = P[(S, i, j)] - P[(S, i, c)] * P[(S, c, j)]; w.add((S, i, j))
    return newP, w

def lg_inlayer(P, M, S, c):
    """pivot-col clear IN LAYER (row op, divides by corner). writes (i,j), i>c, j>=c."""
    newP = dict(P); w = set(); p = P[(S, c, c)]
    for i in range(c+1, M[S]):
        f = P[(S, i, c)] / p
        for j in range(c, M[S+1]):
            newP[(S, i, j)] = P[(S, i, j)] - f * P[(S, c, j)]; w.add((S, i, j))
    return newP, w

def lg_cross_Sm1(P, M, S, c):
    """pivot-col clear as CHART cross-cell backward: clear layer-S col c (left-mult) + compensate
       layer S-1 col c (right-mult) -> writes col c of C^{(S-1)}. Transpose of Rg_fwd."""
    newP = dict(P); w = set(); p = P[(S, c, c)]
    f = {i: P[(S, i, c)] / p for i in range(c+1, M[S])}
    for i in range(c+1, M[S]):
        for j in range(M[S+1]):
            newP[(S, i, j)] = P[(S, i, j)] - f[i] * P[(S, c, j)]; w.add((S, i, j))
    if S - 1 >= 0:
        for k in range(M[S-1]):
            newP[(S-1, k, c)] = P[(S-1, k, c)] + sum(f[i] * P[(S-1, k, i)] for i in range(c+1, M[S])); w.add((S-1, k, c))
    return newP, w

def rg_cross_Sp1(P, M, S, c):
    """pivot-row clear cross-cell forward -> writes row c of C^{(S+1)} (+ layer-S row c)."""
    newP = dict(P); w = set(); p = P[(S, c, c)]
    f = {j: P[(S, c, j)] / p for j in range(c+1, M[S+1])}
    for j in range(c+1, M[S+1]):
        for i in range(M[S]):
            newP[(S, i, j)] = P[(S, i, j)] - f[j] * P[(S, i, c)]; w.add((S, i, j))
    if S+1 < len(M)-1:
        for k in range(M[S+2]):
            newP[(S+1, c, k)] = P[(S+1, c, k)] + sum(f[j] * P[(S+1, j, k)] for j in range(c+1, M[S+1])); w.add((S+1, c, k))
    return newP, w

def build(M, lg, order):
    """node = interior_schur, lg, rg_cross_Sp1, beta; compose in given order. Return prod + writelog."""
    P = init_params(M); log = {}
    seq = list(spine(M)) if order == "root_first" else list(reversed(spine(M)))
    for (S, c) in seq:
        wlog = {}
        P, w = interior_schur(P, M, S, c); wlog['interior'] = sorted(w)
        P, w = lg(P, M, S, c);             wlog['Lg'] = sorted(w)
        P, w = rg_cross_Sp1(P, M, S, c);   wlog['Rg'] = sorted(w)
        Pb, w = beta_blowup(P, M, S, c);   wlog['beta'] = sorted(w); P = Pb
        log[(S, c)] = wlog
    return prod_of(P, M), log

def jj_check(log):
    """for each node, is (S,c,c) [the pivot diagonal] written by any factor?"""
    bad = []
    for (S, c), wl in log.items():
        for fac in ['interior', 'Lg', 'Rg', 'beta']:
            if (S, c, c) in wl[fac]:
                bad.append(((S, c), fac))
    return bad

if __name__ == "__main__":
    for M in [[2, 2, 2], [3, 2, 3], [2, 2, 2, 2]]:
        print("=" * 90); print(f"M = {tuple(M)}  widthMin={[wmin(M,n) for n in range(len(M))]}"); print("=" * 90)
        orc = oracle_prod(M)
        orc_diag = is_diag(orc)
        print(f"  ORACLE clear_pivot: diagonal={orc_diag}  diag={[sp.factor(orc[i,i]) for i in range(min(orc.shape))]}")
        # dropped rows check (rows beyond running-min ceiling should be zero)
        ceil = wmin(M, len(M)-1)
        drops = [i for i in range(M[0]) if all(sp.simplify(orc[i, j]) == 0 for j in range(orc.shape[1]))]
        print(f"  ORACLE dropped(zero) rows: {drops}  (running-min ceiling = {ceil}, expect rows >= {ceil} zero)")
        for lgname, lg in [("Lg IN-LAYER", lg_inlayer), ("Lg CROSS->S-1", lg_cross_Sm1)]:
            for order in ["root_first", "leaf_first"]:
                pr, log = build(M, lg, order)
                d = is_diag(pr)
                match = d and orc_diag and all(
                    sp.simplify(sp.cancel(pr[i, i]) - sp.cancel(orc[i, i])) == 0 for i in range(min(pr.shape)))
                jj = jj_check(log)
                print(f"    [{lgname:14s}][{order:10s}] prod diag={d}  ==oracle:{match}  (J,J)-written:{jj if jj else 'NONE (all fixed)'}")
