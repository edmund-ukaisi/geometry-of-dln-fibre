#!/usr/bin/env python3
"""
EXACT codimension of the product-rank-drop locus.

For a tail chain (d0, d1, ..., dk) with matrices X_i : d_{i-1} x d_i, the product
P = X_1 X_2 ... X_k  is  d0 x dk, generic rank  r* = min(d0,...,dk).

We compute the EXACT codimension of  Z(s') = { (X_i) : rank(P) <= s' }  in the tuple space,
for s' < r*.  Method: rank of the Jacobian of the (s'+1)-minor ideal at a GENERIC point of the
stratum rank(P)=s', using EXACT rational arithmetic (sympy). codim = that Jacobian rank.

Cross-check: a *single* free matrix (k=1) must give codim (d0-s')(d1-s').
"""
import sympy as sp
from itertools import combinations
import random

def build_tuple_with_prod_rank(dims, sp_rank, seed):
    """Construct a rational tuple (X_1,...,X_k) whose product has rank EXACTLY sp_rank,
       generically otherwise. Trick: make X_1 have rank sp_rank (first sp_rank cols random,
       rest = combos), keep the others generic full-rank. Then product rank = sp_rank generically
       IF sp_rank <= min of the rest. We instead force the BOTTLENECK: insert a rank-sp_rank
       factor. Simplest robust construction: choose all factors generic EXCEPT force an internal
       rank drop by composing through an sp_rank-dim space at the first factor's row space.
       We build P_target of rank sp_rank and realize each X_i as generic subject to product=P
       is hard; instead we just make ONE factor rank sp_rank and the rest generic full-rank,
       which yields product rank = sp_rank when sp_rank <= all other dims (true since sp_rank<r*)."""
    rng = random.Random(seed)
    k = len(dims) - 1
    Xs = []
    for i in range(k):
        r, c = dims[i], dims[i+1]
        M = sp.Matrix(r, c, lambda a, b: sp.Rational(rng.randint(-9, 9)))
        Xs.append(M)
    # Force factor 0 to have rank exactly sp_rank: columns >= sp_rank are combos of first sp_rank.
    r0, c0 = dims[0], dims[1]
    X0 = Xs[0]
    if sp_rank < min(r0, c0):
        # set columns sp_rank..c0-1 as random combos of the first sp_rank columns
        for j in range(sp_rank, c0):
            coeffs = [sp.Rational(rng.randint(-5, 5)) for _ in range(sp_rank)]
            X0[:, j] = sum((coeffs[t] * X0[:, t] for t in range(sp_rank)), sp.zeros(r0, 1))
        Xs[0] = X0
    return Xs

def product(Xs):
    P = Xs[0]
    for X in Xs[1:]:
        P = P * X
    return P

def codim_prod_rank(dims, sp_rank, seed=1, verbose=False):
    """codim of {rank(prod) <= sp_rank} via Jacobian rank of (sp_rank+1)-minors
       at a generic stratum point (product rank exactly sp_rank)."""
    k = len(dims) - 1
    # symbolic variables for a FRESH tuple (all entries symbols)
    syms = []
    Xsym = []
    for i in range(k):
        r, c = dims[i], dims[i+1]
        block = sp.Matrix(r, c, lambda a, b: sp.Symbol(f'x{i}_{a}_{b}'))
        Xsym.append(block)
        syms += list(block)
    Psym = product(Xsym)
    r0, ck = dims[0], dims[-1]
    # all (sp_rank+1)-minors
    minors = []
    for rows in combinations(range(r0), sp_rank+1):
        for cols in combinations(range(ck), sp_rank+1):
            minors.append(Psym[list(rows), list(cols)].det())
    # generic stratum point
    Xs_num = build_tuple_with_prod_rank(dims, sp_rank, seed)
    Pnum = product(Xs_num)
    actual_rank = Pnum.rank()
    subs = {}
    for i in range(k):
        r, c = dims[i], dims[i+1]
        for a in range(r):
            for b in range(c):
                subs[sp.Symbol(f'x{i}_{a}_{b}')] = Xs_num[i][a, b]
    # Jacobian of minors wrt all syms, evaluated at the point
    J = sp.Matrix([[sp.diff(m, s) for s in syms] for m in minors])
    Jval = J.subs(subs)
    codim = Jval.rank()
    if verbose:
        print(f"    dims={dims} s'={sp_rank}: actual prod rank={actual_rank} "
              f"(target {sp_rank}), #minors={len(minors)}, codim(Jac rank)={codim}, "
              f"free-formula (d0-s')(dk-s')={(r0-sp_rank)*(ck-sp_rank)}")
    return codim, actual_rank

if __name__ == "__main__":
    print("== sanity: single free matrix k=1, codim must be (d0-s')(d1-s') ==")
    for dims, sp_rank in [((4,2),1),((4,2),0),((3,3),1),((3,3),2),((5,3),2)]:
        c, ar = codim_prod_rank(dims, sp_rank, verbose=True)

    print("\n== genuine products k>=2: is codim = free (d0-s')(dk-s') or different? ==")
    tests = [
        ((4,2,2),1), ((4,2,2),0),      # b=4, tail (2,2): n=2
        ((3,2,3),1), ((3,2,3),0),      # bottleneck internal =2
        ((4,3,2),1), ((4,3,2),0),      # M=(?,4,3,2) tail
        ((3,3,2),1), ((3,3,2),0),
        ((4,2,2,2),1),((4,2,2,2),0),
        ((3,3,3),2),((3,3,3),1),
    ]
    for dims, sp_rank in tests:
        c, ar = codim_prod_rank(dims, sp_rank, verbose=True)
