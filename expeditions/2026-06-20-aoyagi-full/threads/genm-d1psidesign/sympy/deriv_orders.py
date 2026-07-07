"""
Edit-orders of Codex's construction (eps-scaled data) -> D(psiSplitRawGen - id)(0) = 0.
Reports the lowest eps-order of: core untwist (S~_s - S_s), up edit (Y~_s - Y_s), down edit (Z~_0 - Z_0),
and hence of the whole move minus identity.  All >= 2  => D(psi - id)(0) = 0.
"""
import sympy as sp, random
eps = sp.Symbol('eps')


def b22(A, Y, Z, T):
    return A.row_join(Y).col_join(Z.row_join(T))


def minord(M):
    lo = None
    for e in (M if hasattr(M, '__iter__') else [M]):
        e = sp.expand(sp.series(sp.expand(e), eps, 0, 9).removeO())
        if e == 0:
            continue
        d = min(mm[0] for mm in sp.Poly(e, eps).monoms())
        lo = d if lo is None else min(lo, d)
    return lo


def run(L, r, m, seed=5):
    random.seed(seed)
    def G(a, b):
        return sp.Matrix(a, b, lambda i, j: eps * sp.Rational(random.randint(-4, 4), 5))
    Ir = sp.eye(r); Im = sp.eye(m); n = r + m
    X = {s: G(r, r) for s in range(L)}; Y = {s: G(r, m) for s in range(L)}
    Z = {s: G(m, r) for s in range(L)}; T = {s: G(m, m) for s in range(L)}
    A = {s: Ir + X[s] for s in range(L)}
    C = {s: b22(A[s], Y[s], Z[s], T[s]) for s in range(L)}
    Q = {0: sp.eye(n)}
    for s in range(1, L + 1):
        Q[s] = (Q[s - 1] * C[s - 1]).applyfunc(sp.expand)
    B = {s: Q[s][:r, :r] for s in range(L)}; R = {s: Q[s][:r, r:] for s in range(L)}
    u = {s: (B[s].inv() * R[s]).applyfunc(sp.expand) for s in range(L)}
    V = {s: (Z[s] * A[s].inv()).applyfunc(sp.expand) for s in range(L)}
    S = {s: (T[s] - Z[s] * A[s].inv() * Y[s]).applyfunc(sp.expand) for s in range(L)}
    Nn = {s: Ir + u[s] * V[s] for s in range(L)}
    Msh = {s: Im - V[s] * Nn[s].inv() * u[s] for s in range(L)}
    Stil = {s: (Msh[s] * S[s]).applyfunc(sp.expand) for s in range(L)}
    Ytil = {s: (Y[s] + Nn[s].inv() * u[s] * (S[s] - Stil[s])).applyfunc(sp.expand) for s in range(L)}
    # Z0 accumulator (reading b)
    W = {s: (Q[s][r:, r:] - Q[s][r:, :r] * B[s].inv() * R[s]).applyfunc(sp.expand) for s in range(L)}
    va = sp.zeros(m, r); vt = sp.zeros(m, r); Wt = Im
    for s in range(L):
        va = va + W[s] * V[s] * Nn[s].inv() * B[s].inv()
        vt = vt + Wt * V[s] * Nn[s].inv() * B[s].inv()
        Wt = Wt * Msh[s] * Stil[s]
    dV0 = va - vt
    Z0t = (V[0] + dV0) * A[0]
    core_ord = min(minord(list(Stil[s] - S[s])) or 99 for s in range(L))
    up_ord = min(minord(list(Ytil[s] - Y[s])) or 99 for s in range(L))
    z0_ord = minord(list(Z0t - Z[0]))
    print(f"L={L} r={r} m={m}: core(S~-S)=O(eps^{core_ord})  up(Y~-Y)=O(eps^{up_ord})  "
          f"Z0(Z~-Z)=O(eps^{z0_ord})  -> move-id = O(eps^{min(core_ord,up_ord,z0_ord if z0_ord else 99)})")


if __name__ == "__main__":
    for (L, r, m) in [(3, 1, 1), (3, 1, 2), (4, 1, 2), (5, 1, 1)]:
        run(L, r, m)
