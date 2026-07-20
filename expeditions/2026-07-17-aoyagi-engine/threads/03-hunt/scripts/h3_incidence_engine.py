#!/usr/bin/env python3
"""HUNT h3 -- Tier B incidence-chart valuation engine (sympy, EXACT).

A divisorial valuation is realized by a birational chart phi: (new coords y) -> (old
matrix entries x), COMPOSED of incidence normalizations, plus a monomial weight w on
the new coords. The rlct-candidate is (change-of-variables / relative-canonical rule)

    rho = ( sum_i w_i + w(det d phi/d y) ) / ( 2 * min_g w(g o phi) )

where w(P) = min over the (sympy-EXPANDED, cancellation-corrected) monomial support of
P of the w-weighted degree. KILL the coverage >=-leg iff some genuine chart+weight has
rho < 1/2 minAdm, i.e.  2*rho = (sum w + w(Jac)) / min_g w(g o phi) < minAdm.

Incidence normalization on a residual block (rows R, cols Cc) of layer s, pivot (p,q):
factor alpha = C^(s)[p][q]; new coords a_j (row p cleared), b_i (col q cleared),
delta_ij (Schur residual); C^(s)[i][j] -> alpha*(b_i a_j + delta_ij), etc. This is the
exact Case-1/incidence chart (worked tex ssec:blowup, A = alpha[[1,a],[b,ab+delta]]).

This module provides the primitives; h4/h5 drive the actual hunt over chart families.
"""
import sys, itertools
from fractions import Fraction as F
import sympy as sp
sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/map/battery")
from _minadm import minAdm


def mat_symbols(name, r, c):
    return sp.Matrix(r, c, lambda i, j: sp.Symbol(f"{name}_{i}_{j}"))


def incidence_layer(Cmat, pivot=(0, 0), prefix="c1"):
    """Return (Cnew, newvars, subs) for an incidence normalization of matrix Cmat
    (r x c) at pivot (p,q). Cnew is Cmat re-expressed in incidence coords; newvars is
    the ordered list of new symbols; subs maps OLD entry symbol -> expr in new coords.
    New coords: alpha; a_j (j != q); b_i (i != p); delta_ij (i != p, j != q)."""
    r, c = Cmat.shape
    p, q = pivot
    alpha = sp.Symbol(f"{prefix}_al")
    a = {j: sp.Symbol(f"{prefix}_a{j}") for j in range(c) if j != q}
    b = {i: sp.Symbol(f"{prefix}_b{i}") for i in range(r) if i != p}
    d = {(i, j): sp.Symbol(f"{prefix}_d{i}_{j}") for i in range(r) for j in range(c)
         if i != p and j != q}
    Cnew = sp.zeros(r, c)
    for i in range(r):
        for j in range(c):
            if i == p and j == q:
                Cnew[i, j] = alpha
            elif i == p:
                Cnew[i, j] = alpha * a[j]
            elif j == q:
                Cnew[i, j] = alpha * b[i]
            else:
                Cnew[i, j] = alpha * (b[i] * a[j] + d[(i, j)])
    newvars = [alpha] + [a[j] for j in sorted(a)] + [b[i] for i in sorted(b)] \
              + [d[k] for k in sorted(d)]
    return Cnew, newvars, alpha


def support_exps(expr, varlist):
    """EXACT expanded monomial support of expr as a list of exponent tuples over varlist."""
    expr = sp.expand(expr)
    if expr == 0:
        return []
    poly = sp.Poly(expr, *varlist)
    return [tuple(int(e) for e in m) for m in poly.monoms()]


def wdeg_min(exps, w):
    """min over exponent tuples of the w-weighted degree (w a tuple aligned to varlist)."""
    return min(sum(e * wi for e, wi in zip(m, w)) for m in exps)


def jac_order_support(subs_matrices, oldvars, newvars):
    """Given the substitution old_entry -> expr(new) for ALL layers (concatenated),
    return the monomial support (exponent tuples over newvars) of det(Jacobian d old/d new).
    subs_matrices: list of (old_symbol, expr_in_new). Must be a square change of vars."""
    olds = [os for (os, _) in subs_matrices]
    exprs = [ex for (_, ex) in subs_matrices]
    J = sp.Matrix([[sp.diff(ex, nv) for nv in newvars] for ex in exprs])
    det = sp.expand(J.det())
    if det == 0:
        return None  # degenerate chart
    return support_exps(det, newvars)


def build_product_entries(mats):
    """entries of the matrix product mats[0]*mats[1]*...; returns flat list of sympy exprs."""
    P = mats[0]
    for m in mats[1:]:
        P = P * m
    return [sp.expand(P[i, j]) for i in range(P.shape[0]) for j in range(P.shape[1])]


def min_ratio_over_weights(gen_exps, jac_exps, nvars, wmax=3, w_alpha_boost=None):
    """Grid-search integer weights w in {0..wmax}^nvars; return (min 2rho as Fraction, argw).
    2rho = (sum w + w(Jac)) / min_g w(g). Skips weights making denom 0."""
    best = None; argw = None
    rng = range(wmax + 1)
    for w in itertools.product(rng, repeat=nvars):
        if sum(w) == 0:
            continue
        denom = min(wdeg_min(g, w) for g in gen_exps)
        if denom <= 0:
            continue
        num = sum(w) + (wdeg_min(jac_exps, w) if jac_exps else 0)
        r = F(num, denom)
        if best is None or r < best:
            best, argw = r, w
    return best, argw


# ---- validation on (2,2,2): incidence on C1 (rank-1 pivot), then read min ratio ----
if __name__ == "__main__":
    print("VALIDATION: (2,2,2) incidence chart on C1, single-layer, monomial weight search")
    C1 = mat_symbols("C1", 2, 2)
    C2 = mat_symbols("C2", 2, 2)
    C1new, nv1, alpha1 = incidence_layer(C1, (0, 0), "c1")
    # old->new substitution for C1 entries; C2 entries stay as their own new coords
    subs = []
    for i in range(2):
        for j in range(2):
            subs.append((C1[i, j], C1new[i, j]))
    for i in range(2):
        for j in range(2):
            subs.append((C2[i, j], C2[i, j]))  # identity on C2
    newvars = list(nv1) + [C2[i, j] for i in range(2) for j in range(2)]
    # product entries in new coords
    prod = build_product_entries([C1new, C2])
    gen_exps = [support_exps(g, newvars) for g in prod]
    jac_exps = jac_order_support(subs, None, newvars)
    print(f"  #newvars={len(newvars)}, Jac support size={len(jac_exps) if jac_exps else 0}")
    best, argw = min_ratio_over_weights(gen_exps, jac_exps, len(newvars), wmax=3)
    ma = minAdm((2, 2, 2))
    print(f"  min 2rho over this chart = {best} (rho={best/2}); minAdm={ma}, 1/2 minAdm={F(ma,2)}")
    print(f"  argmin w (aligned to {[str(v) for v in newvars]}) = {argw}")
    print(f"  chart min undershoots 1/2 minAdm? {best < ma}")
