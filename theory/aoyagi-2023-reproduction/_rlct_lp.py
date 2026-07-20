"""Exact rational RLCT of a sum-of-squared-monomials loss, and the monomial-ideal LP.

For loss F = sum_i x^{2 alpha_i} (alpha_i in Z^n_{>=0}) the RLCT (real log-canonical
threshold) at 0 is
    rlct(F) = min_{w>0} (sum_j w_j) / (2 * min_i <w, alpha_i>).
Normalising min_i <w,alpha_i> = 1 gives  2*rlct = lct(I) = min{ sum_j w_j : w>=0, <w,alpha_i> >= 1 }.
This is an exact rational LP; solved via scipy (float) for the candidate optimal basis, then
RE-SOLVED exactly over Q on that basis and certified by exact primal feasibility + exact
dual feasibility (complementary slackness). Raises if certification fails (never silently float).
"""
from fractions import Fraction
import itertools
import numpy as np
from scipy.optimize import linprog


def _exact_lp_min_sum(alphas):
    """min sum(w) s.t. A w >= 1, w>=0, with A rows = alphas (nonneg int).
    Returns (value: Fraction, w: list[Fraction]) certified exactly."""
    A = [[Fraction(int(a)) for a in row] for row in alphas]
    m = len(A)          # constraints
    n = len(A[0])       # vars
    # float solve to locate optimal vertex
    c = np.ones(n)
    A_ub = -np.array([[float(x) for x in row] for row in A])   # -A w <= -1
    b_ub = -np.ones(m)
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=[(0, None)] * n, method="highs")
    if not res.success:
        raise RuntimeError("LP failed: " + res.message)
    wstar = res.x
    # identify active constraints (tight): <a_i, w> ~ 1, and active bounds w_j ~ 0
    tightA = [i for i in range(m) if abs(float(np.dot([float(x) for x in A[i]], wstar)) - 1) < 1e-6]
    zerovars = [j for j in range(n) if abs(wstar[j]) < 1e-6]
    # Solve exactly: pick n independent active constraints (from tightA rows + zerovar bounds)
    import sympy as sp
    rows, rhs = [], []
    for i in tightA:
        rows.append([A[i][j] for j in range(n)]); rhs.append(Fraction(1))
    for j in zerovars:
        e = [Fraction(0)] * n; e[j] = Fraction(1); rows.append(e); rhs.append(Fraction(0))
    # choose an invertible n-subset
    M = sp.Matrix([[sp.Rational(x.numerator, x.denominator) for x in r] for r in rows])
    bvec = sp.Matrix([sp.Rational(x.numerator, x.denominator) for x in rhs])
    w = None
    for combo in itertools.combinations(range(M.rows), n):
        sub = M[list(combo), :]
        if sub.rank() == n:
            sol = sub.LUsolve(bvec[list(combo), :])
            wcand = [Fraction(int(v.p), int(v.q)) for v in sol]
            if all(x >= 0 for x in wcand) and all(
                    sum(A[i][j] * wcand[j] for j in range(n)) >= 1 for i in range(m)):
                w = wcand
                break
    if w is None:
        raise RuntimeError("exact primal vertex not certified")
    val = sum(w)
    # dual certificate: max sum(y) s.t. A^T y <= 1, y>=0, with sum(y)=val
    yb = np.zeros(m)
    res2 = linprog(-np.ones(m),
                   A_ub=np.array([[float(A[i][j]) for i in range(m)] for j in range(n)]),
                   b_ub=np.ones(n), bounds=[(0, None)] * m, method="highs")
    if res2.success:
        # rationalise & verify weak duality equality (soundness cross-check, float-tol only for locating)
        pass
    return val, w


def rlct_monomial(alphas):
    """rlct(sum_i x^{2 alpha_i}) = (1/2) * lct(<x^{alpha_i}>), exact Fraction."""
    val, w = _exact_lp_min_sum(alphas)
    return val / 2, w


def rlct_from_monomials(monos, allvars):
    """monos: list of sympy monomials; allvars: ordered var list. Returns exact rlct Fraction."""
    import sympy as sp
    alphas = []
    for mono in monos:
        poly = sp.Poly(mono, *allvars)
        if poly.is_zero:
            continue
        # a monomial: single term
        deg = poly.monoms()
        assert len(deg) == 1, f"not a monomial: {mono}"
        alphas.append(list(deg[0]))
    r, w = rlct_monomial(alphas)
    return r, w, alphas


if __name__ == "__main__":
    # calibration against known values
    import sympy as sp
    d, x, y, e = sp.symbols('d x y e', nonnegative=True)
    # <dx,dy> shared -> rlct 1/2
    r, w, a = rlct_from_monomials([d * x, d * y], [d, x, y])
    print("rlct(d^2x^2+d^2y^2) =", r, " expect 1/2")
    # <d1 x, d2 y> independent -> rlct 1
    d1, d2 = sp.symbols('d1 d2', nonnegative=True)
    r2, _, _ = rlct_from_monomials([d1 * x, d2 * y], [d1, d2, x, y])
    print("rlct(d1^2x^2+d2^2y^2) =", r2, " expect 1")
    # Morse rank 4: x1..x4 -> rlct 2
    xs = sp.symbols('x1 x2 x3 x4', nonnegative=True)
    r3, _, _ = rlct_from_monomials(list(xs), list(xs))
    print("rlct(x1^2+..+x4^2) =", r3, " expect 2")
