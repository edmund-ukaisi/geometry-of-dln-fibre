#!/usr/bin/env python3
"""Exact Newton-polytope RLCT machine for monomial ideals (rational, no float).

For a monomial ideal I = <x^{a_1}, ..., x^{a_m}> (generators = monomials with
exponent vectors a_k in Z_{>=0}^n), the real log canonical threshold of the
sum-of-squares  F = sum_k (x^{a_k})^2  at the origin is the LP

    rlct(I) = min { sum_i u_i : u >= 0,  <u, a_k> >= 1/2  for all k }.

(Single monomial x: constraint u>=1/2, min = 1/2. <dx,dy>: 1/2. <d1x,d2y>: 1.)

Solved EXACTLY by rational vertex enumeration: every basic optimum sits where n
of the (m generator + n nonneg) constraints are tight; solve each n x n rational
system with fractions, keep feasible ones, take the min objective. Exact.
"""
from fractions import Fraction as F
from itertools import combinations


def _solve(rows, rhs):
    """Exact solve of a square rational system via Gaussian elimination; None if singular."""
    n = len(rows)
    A = [[F(x) for x in r] + [F(b)] for r, b in zip(rows, rhs)]
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c] != 0), None)
        if piv is None:
            return None
        A[c], A[piv] = A[piv], A[c]
        inv = A[c][c]
        A[c] = [x / inv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [a - f * b for a, b in zip(A[r], A[c])]
    return [A[r][n] for r in range(n)]


def rlct_monomial_ideal_lp(gens, nvars):
    """Fast FLOAT cross-check via scipy linprog (a GUIDE, not a certificate)."""
    import numpy as np
    from scipy.optimize import linprog
    # min sum u  s.t.  -A u <= -1/2 ,  u >= 0
    A = np.array([[float(a) for a in g] for g in gens])
    b = np.full(len(gens), 0.5)
    res = linprog(c=np.ones(nvars), A_ub=-A, b_ub=-b, bounds=[(0, None)] * nvars,
                  method="highs")
    return res.fun if res.success else None


def rlct_monomial_ideal(gens, nvars):
    """gens: list of exponent tuples (len nvars). Returns exact Fraction rlct.
    Exact vertex enumeration; only feasible for small nvars (<=9)."""
    half = F(1, 2)
    # Constraints as (coef vector, rhs) for  <coef,u> >= rhs :
    #   generator k:  a_k . u >= 1/2
    #   nonneg i:     e_i . u >= 0
    cons = [([F(a) for a in g], half) for g in gens]
    for i in range(nvars):
        e = [F(0)] * nvars
        e[i] = F(1)
        cons.append((e, F(0)))
    best = None
    idxs = list(range(len(cons)))
    for combo in combinations(idxs, nvars):
        rows = [cons[c][0] for c in combo]
        rhs = [cons[c][1] for c in combo]
        sol = _solve(rows, rhs)
        if sol is None:
            continue
        # feasibility: all constraints satisfied
        if all(sum(cf * s for cf, s in zip(cv, sol)) >= rv for cv, rv in cons):
            obj = sum(sol)
            if best is None or obj < best:
                best = obj
    return best


if __name__ == "__main__":
    tests = [
        ("x (single coord)",           [(1,)], 1, F(1, 2)),
        ("x^2+y^2 (Morse pair)",       [(1, 0), (0, 1)], 2, F(1)),
        ("<dx,dy> shared",             [(1, 1, 0), (1, 0, 1)], 3, F(1, 2)),
        ("<d1x,d2y> indep",            [(1, 0, 1, 0), (0, 1, 0, 1)], 4, F(1)),
        # (2,2,2) block-eliminated at rank-1 C1 pivot:
        #   vars (c11,c12,C4,c21,c22); gens c11,c12,C4 c21,C4 c22
        ("(2,2,2) rank-1 reduction",   [(1,0,0,0,0),(0,1,0,0,0),(0,0,1,1,0),(0,0,1,0,1)], 5, F(3, 2)),
        # (2,2,2) full-rank C1 -> ||C2||^2, 4 coords
        ("(2,2,2) full-rank reduction",[(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)], 4, F(2)),
    ]
    allok = True
    for name, gens, n, expect in tests:
        got = rlct_monomial_ideal(gens, n)
        ok = got == expect
        allok &= ok
        print(f"{'OK ' if ok else 'FAIL'} {name:32s} rlct={got}  expect={expect}")
    print("ALL PASS" if allok else "SOME FAILED")
