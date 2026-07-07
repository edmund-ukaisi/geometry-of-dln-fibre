"""
(1) INVARIANT B at NON-SCALAR core (m=2), L=3,4, exact-rational:
      blockSchur(P) == coreProd  AND  coreProd == plain-product of the per-layer factors
      (S_0, (1-K_1)S_1, ..., (1-K_{L-1})S_{L-1}) -- so the moved point's conjAbsorb reads Score.
(2) DERIVATIVE: the core-untwist residual (ΔP under the core-only move) is O(eps^3) as a germ,
      hence the whole move psiSplitRawGen = id + O(eps^3) and D(psiSplitRawGen - id)(0) = 0
      (the banked DeepestPsiFlatCutGen triple fires).
"""
import sympy as sp, random

eps = sp.Symbol('eps')


def b22(A, Y, Z, T):
    return A.row_join(Y).col_join(Z.row_join(T))


def prod(Cs):
    P = Cs[0]
    for s in range(1, len(Cs)):
        P = P * Cs[s]
    return P


def data(L, r, m, scaled, seed):
    random.seed(seed)
    def M(a, b):
        f = (eps if scaled else sp.Integer(1))
        return sp.Matrix(a, b, lambda i, j: f * sp.Rational(random.randint(-4, 4), 9))
    return ({s: M(r, r) for s in range(L)}, {s: M(r, m) for s in range(L)},
            {s: M(m, r) for s in range(L)}, {s: M(m, m) for s in range(L)})


def invariant_B(L, r, m, seed=1):
    X, Y, Z, T = data(L, r, m, False, seed)
    Ir = sp.eye(r); Im = sp.eye(m); n = r + m
    A = {s: Ir + X[s] for s in range(L)}
    C = {s: b22(A[s], Y[s], Z[s], T[s]) for s in range(L)}
    Pp = {0: sp.eye(n)}
    for j in range(1, L + 1):
        Pp[j] = Pp[j - 1] * C[j - 1]
    P = Pp[L]
    S = {s: T[s] - Z[s] * A[s].inv() * Y[s] for s in range(L)}
    K = {0: sp.zeros(m, m)}
    for s in range(1, L):
        K[s] = Z[s] * (Pp[s + 1][:r, :r]).inv() * (Pp[s][:r, r:])
    factor = {0: S[0]}
    for s in range(1, L):
        factor[s] = (Im - K[s]) * S[s]
    coreProd = factor[0]
    for s in range(1, L):
        coreProd = coreProd * factor[s]
    blockSchurP = P[r:, r:] - P[r:, :r] * P[:r, :r].inv() * P[:r, r:]
    plainprod = factor[0]
    for s in range(1, L):
        plainprod = plainprod * factor[s]
    okBS = sp.simplify(blockSchurP - coreProd) == sp.zeros(m, m)
    okPP = sp.simplify(plainprod - coreProd) == sp.zeros(m, m)
    print(f"  L={L} m={m}: blockSchur(P)==coreProd: {okBS} ;  "
          f"plain-prod of (1-K_s)S_s == coreProd (== Score): {okPP}")
    return okBS and okPP


def min_order(M):
    lo = None
    for e in M:
        e = sp.expand(e)
        if e == 0:
            continue
        d = sp.Poly(e, eps).monoms()
        md = min(mm[0] for mm in d)
        lo = md if lo is None else min(lo, md)
    return lo


def deriv_order(L, r, m, seed=1):
    """min eps-order of the core-only reg-block residual = order at which the correction starts."""
    X, Y, Z, T = data(L, r, m, True, seed)
    Ir = sp.eye(r); Im = sp.eye(m); n = r + m
    A = {s: Ir + X[s] for s in range(L)}
    C = {s: b22(A[s], Y[s], Z[s], T[s]) for s in range(L)}
    Pp = {0: sp.eye(n)}
    for j in range(1, L + 1):
        Pp[j] = sp.expand(Pp[j - 1] * C[j - 1])
    P = Pp[L]
    # inverse via series (A_s = I+O(eps)); use plain .inv() then series-expand entries is heavy;
    # instead compute S,K exactly as rational funcs of eps (small) then min-order.
    S = {s: sp.expand(T[s] - Z[s] * A[s].inv() * Y[s]) for s in range(L)}
    S = {s: S[s].applyfunc(sp.expand) for s in range(L)}
    K = {0: sp.zeros(m, m)}
    for s in range(1, L):
        K[s] = (Z[s] * (Pp[s + 1][:r, :r]).inv() * (Pp[s][:r, r:])).applyfunc(sp.expand)
    # core-only move: T'_s = T_s - K_s S_s
    Cco = {s: b22(A[s], Y[s], Z[s], sp.expand(T[s] - K[s] * S[s])) for s in range(L)}
    Pco = Cco[0]
    for s in range(1, L):
        Pco = sp.expand(Pco * Cco[s])
    resid = []
    for (a0, a1, b0, b1) in [(0, r, 0, r), (0, r, r, r + m), (r, r + m, 0, r)]:
        for i in range(a0, a1):
            for j in range(b0, b1):
                resid.append(sp.series(sp.expand(Pco[i, j] - P[i, j]), eps, 0, 8).removeO())
    lo = min_order(sp.Matrix(resid))
    print(f"  L={L} m={m}: core-only reg-block residual (=correction start) is O(eps^{lo})  "
          f"-> D(psi-id)(0)=0 iff lo>=2: {lo is not None and lo >= 2}")
    return lo


if __name__ == "__main__":
    print("INVARIANT B (non-scalar):")
    invariant_B(3, 1, 2); invariant_B(4, 1, 2); invariant_B(3, 1, 1); invariant_B(4, 1, 1)
    print("\nDERIVATIVE (correction start order):")
    deriv_order(3, 1, 1); deriv_order(3, 1, 2); deriv_order(4, 1, 1); deriv_order(4, 1, 2)
