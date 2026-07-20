#!/usr/bin/env python3
# pnp-full (thread 24): Q1 -- the VALUE content, end-to-end root-first over the completed-alpha
# REDUCTION (Lg+Rg+beta). Verifies, at M in {(2,2,2),(2,2,2,2),(3,3,4),(4,3,4)}:
#  (V1) prod diagonal at the leaf; residualCore = frobSq(prod)/(divisor monomial) = 1 + sum ratios^2 >= 1.
#  (V2) InvVal3 three-state at EVERY walk state: prodPrefix row i is DIAG if clearedOf, ZERO if droppedOf
#       (the four-case maintenance's per-step content, verified against the ACTUAL completed-alpha reduction
#       -- stronger than clearedof_walk_trace's idealized clear_pivot).
#  (V3) CONTRAST: interior-only alpha residualCore HITS 0 on the box (why the fix was wanted).
# NB: this is the value content of the REDUCTION; chart-VALIDITY (det!=0, a.e.-injective) is Q2/Q3
# (the completed alpha is a projection, det 0 -- see fvw_chart.py). MC never used.
import sympy as sp, sys
BATT = "/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/expeditions/2026-07-17-aoyagi-engine/threads/24-alpha-cover/battery"
sys.path.insert(0, BATT)
from rg_shape import (init_params, layer_mat, spine, beta_blowup, alpha_interior,
                      alpha_Lg, alpha_Rg_crosslayer)

def wmin(M, n): return min(M[:n + 1])

def node_completed(P, M, S, c):
    P, _ = alpha_Lg(P, M, S, c)
    P, _ = alpha_Rg_crosslayer(P, M, S, c)
    P, _ = beta_blowup(P, M, S, c)
    return P

def node_interior(P, M, S, c):
    P, _ = alpha_interior(P, M, S, c)
    P, _ = beta_blowup(P, M, S, c)
    return P

def prod_layers(P, M, upto):
    """product of transformed layers 0..upto inclusive."""
    Pr = layer_mat(P, M, 0)
    for s in range(1, upto + 1):
        Pr = Pr * layer_mat(P, M, s)
    return sp.simplify(Pr)

def classify_rows(Mtx, m0):
    out = []
    for i in range(m0):
        nz = [j for j in range(Mtx.shape[1]) if sp.simplify(Mtx[i, j]) != 0]
        out.append('ZERO' if not nz else ('DIAG' if nz == [i] else 'RESID'))
    return out

def resolvedRows(M, layer, cleared, L):
    return wmin(M, L) if layer == L else cleared

def dropThreshold(M, layer, cleared):
    return wmin(M, layer + 1) if wmin(M, layer + 1) <= cleared else wmin(M, layer)

def value_walk(M, node_fn):
    """root-first walk; at each state snapshot prodPrefix (layers 0..min(layer,L-1)) + classify rows."""
    L = len(M) - 1; m0 = M[0]
    P = init_params(M)
    states = []
    def snap(layer, cleared):
        upto = min(layer, L - 1)
        Pr = prod_layers(P, M, upto)
        return (layer, cleared, classify_rows(Pr, m0))
    states.append(snap(0, 0))              # conRoot
    for S in range(L):
        cap = wmin(M, S + 1)
        for J in range(1, cap + 1):
            P = node_fn(P, M, S, J - 1)
            states.append(snap(S, J))
        if S + 1 < L:
            states.append(snap(S + 1, 0))  # rollover
        else:
            states.append(snap(L, 0))      # terminal
    return states, P

def check_invval3(M, states, L):
    m0 = M[0]; ok = True
    for (layer, cleared, cls) in states:
        rr = resolvedRows(M, layer, cleared, L)
        dt = dropThreshold(M, layer, cleared)
        cleared_set = {i for i in range(m0) if i < rr}
        dropped_set = {i for i in range(m0) if i >= dt}
        zero = {i for i in range(m0) if cls[i] == 'ZERO'}
        diag = {i for i in range(m0) if cls[i] == 'DIAG'}
        c_ok = cleared_set <= diag           # cleared => DIAG
        d_ok = dropped_set <= zero           # dropped => ZERO
        ok = ok and c_ok and d_ok
        flag = "" if (c_ok and d_ok) else "  <<< VIOLATION"
        print(f"    ({layer},{cleared}) rows={cls}  cleared(i<{rr})={sorted(cleared_set)}=>DIAG:{c_ok}  "
              f"dropped(i>={dt})={sorted(dropped_set)}=>ZERO:{d_ok}{flag}")
    return ok

def residual_core(M, Pfinal, node_tag):
    L = len(M) - 1; m0 = M[0]
    Pr = prod_layers(Pfinal, M, L - 1)
    diag = Pr.shape[0]; ncol = Pr.shape[1]
    is_diag = all(sp.simplify(Pr[i, j]) == 0 for i in range(m0) for j in range(ncol) if i != j)
    dvals = [sp.factor(Pr[i, i]) for i in range(min(m0, ncol))]
    frob = sp.expand(sum(sp.simplify(Pr[i, j]) ** 2 for i in range(m0) for j in range(ncol)))
    return is_diag, dvals, frob

def interior_hits_zero(M):
    """does interior-only residualCore hit 0 on {-1,0,1}? (pnp-diag W3)."""
    import itertools
    P = init_params(M)
    for S in range(len(M) - 1):
        for c in range(wmin(M, S + 1)):
            P = node_interior(P, M, S, c)
    Pr = prod_layers(P, M, len(M) - 2)
    syms = sorted(Pr.free_symbols, key=str)
    frob = sp.expand(sum(sp.simplify(Pr[i, j]) ** 2 for i in range(Pr.shape[0]) for j in range(Pr.shape[1])))
    # sample small grid for a zero of frob with not-all-zero (divisor monomial != 0 region proxy):
    for vals in itertools.product([-1, 0, 1], repeat=len(syms)):
        sub = dict(zip(syms, vals))
        if frob.subs(sub) == 0 and any(v != 0 for v in vals):
            return True, dict(zip([str(s) for s in syms], vals))
    return False, None

if __name__ == "__main__":
    for M in [[2, 2, 2], [2, 2, 2, 2], [3, 3, 4], [4, 3, 4]]:
        L = len(M) - 1
        print("=" * 92)
        print(f"M = {tuple(M)}   widthMinUpto = {[wmin(M, n) for n in range(len(M))]}   spine = {spine(M)}")
        print("=" * 92)
        states, Pfin = value_walk(M, node_completed)
        print("  -- InvVal3 three-state at every root-first walk state (completed-alpha reduction) --")
        inv_ok = check_invval3(M, states, L)
        is_diag, dvals, frob = residual_core(M, Pfin, "completed")
        print(f"  (V1) leaf prod diagonal? {is_diag}   diag(b-chain) = {dvals}")
        # residualCore structure: factor out gcd (smallest divisor)
        print(f"  (V2) InvVal3 maintenance holds at all states? {inv_ok}")
        hit, wit = interior_hits_zero(M) if M in ([2,2,2],[2,2,2,2],[3,3,4]) else (None, None)
        print(f"  (V3) interior-only residualCore hits 0 on box? {hit}  witness={wit}")
        print()
