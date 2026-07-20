#!/usr/bin/env python3
# pnp-full (thread 24): the DECISIVE chart-validity test. The Lean alpha-slot must be a det-1,
# a.e.-INJECTIVE map (residualSchurShear is; a.e.-inj transfer = task 2c). Q3 core: is the COMPLETED
# alpha (Lg+Rg, whatever order w.r.t. beta) a valid non-degenerate chart, or a PROJECTION (det 0,
# non-injective, cannot fill the slot)? Compute the EXACT full-composite chartMap Jacobian det for
# both node-internal orders (alpha-then-beta = Lean; beta-then-alpha = Aoyagi normalize-first) and
# both eval orders. Compare the interior-only baseline (PROVEN det = monomial). Exact sympy.
import sympy as sp
import sys
BATT = "/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/expeditions/2026-07-17-aoyagi-engine/threads/24-alpha-cover/battery"
sys.path.insert(0, BATT)
from rg_shape import (init_params, spine, beta_blowup, alpha_interior, alpha_Lg, alpha_Rg_crosslayer)

def flat_order(M):
    L = len(M) - 1
    return [(s, i, j) for s in range(L) for i in range(M[s]) for j in range(M[s + 1])]

def node_int_ab(P, M, S, c):   # interior alpha THEN beta (Lean order)
    P, _ = alpha_interior(P, M, S, c); P, _ = beta_blowup(P, M, S, c); return P
def node_comp_ab(P, M, S, c):  # completed alpha THEN beta
    P, _ = alpha_Lg(P, M, S, c); P, _ = alpha_Rg_crosslayer(P, M, S, c); P, _ = beta_blowup(P, M, S, c); return P
def node_comp_ba(P, M, S, c):  # beta THEN completed alpha (Aoyagi normalize-first)
    P, _ = beta_blowup(P, M, S, c); P, _ = alpha_Lg(P, M, S, c); P, _ = alpha_Rg_crosslayer(P, M, S, c); return P
def node_int_ba(P, M, S, c):
    P, _ = beta_blowup(P, M, S, c); P, _ = alpha_interior(P, M, S, c); return P

def chart_det(M, node_fn, order):
    coords = flat_order(M); src = init_params(M)
    P = init_params(M)
    seq = list(spine(M)) if order == "root_first" else list(reversed(spine(M)))
    for (S, c) in seq:
        P = node_fn(P, M, S, c)
    after = sp.Matrix([sp.together(P[c]) for c in coords])
    J = after.jacobian([src[c] for c in coords])
    det = J.det()
    return sp.factor(sp.cancel(det))

def classify(det, M):
    if det == 0:
        return "ZERO (projection / non-injective — CANNOT fill det-1 alpha slot)"
    corners = {sp.Symbol(f'a{s}_{c}{c}', real=True) for s in range(len(M)-1) for c in range(min(M[s],M[s+1]))}
    num, den = sp.fraction(sp.together(det))
    _, nf = sp.factor_list(num); _, df = sp.factor_list(den)
    non_corner_num = [(sp.factor(b), m) for b, m in nf if (not b.is_number) and b not in corners]
    non_corner_den = [(sp.factor(b), m) for b, m in df if (not b.is_number) and b not in corners]
    if not non_corner_num and not non_corner_den:
        exps = {}
        for b, m in nf:
            if b in corners: exps[b] = exps.get(b,0)+m
        for b, m in df:
            if b in corners: exps[b] = exps.get(b,0)-m
        return f"MONOMIAL in source corners, exps={ {str(k):v for k,v in exps.items()} }"
    return f"NON-corner-monomial: num extra {non_corner_num}, den extra {non_corner_den}"

if __name__ == "__main__":
    configs = [
        ("interior-only, alpha->beta", node_int_ab),
        ("interior-only, beta->alpha", node_int_ba),
        ("COMPLETED,     alpha->beta", node_comp_ab),
        ("COMPLETED,     beta->alpha", node_comp_ba),
    ]
    for M in [[2,2,2],[2,2,2,2]]:
        print("="*96); print(f"M = {tuple(M)}"); print("="*96)
        for order in ["root_first","leaf_first"]:
            for tag, nf in configs:
                try:
                    d = chart_det(M, nf, order)
                    print(f"  [{order:10s}][{tag}]  |det D chartMap| : {classify(d, M)}")
                except Exception as e:
                    print(f"  [{order:10s}][{tag}]  ERROR {type(e).__name__}: {e}")
        print()
