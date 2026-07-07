"""
INVARIANT A -- fast INCREMENTAL near-origin germ test.

Same model as germ_solve.py, but solves order-by-order with lower orders substituted to EXACT
RATIONALS before each order (only the current order's ~O(L*dim) coefficients are symbolic),
so each linear solve is small.  A genuine obstruction shows up as an unsolvable order-k system.

Move family (rigid per-layer Schur-core target (1-K_s)S_s; reg edits dA_s,dZ_s,dw_s):
    C'_s = [[A_s+dA_s, (A_s+dA_s)(w_s+dw_s)], [Z_s+dZ_s, (Z_s+dZ_s)(w_s+dw_s) + (1-K_s)S_s]]
"""
import sympy as sp, random, sys

eps = sp.Symbol('eps')


def b22(A, Y, Z, T):
    return A.row_join(Y).col_join(Z.row_join(T))


def trunc(M, N):
    return M.applyfunc(lambda e: sp.Add(*[t for t in sp.expand(e).as_ordered_terms()
                                          if sp.Poly(t, eps).degree() <= N]) if sp.expand(e) != 0 else 0)


def trunc_expr(e, N):
    e = sp.expand(e)
    if e == 0:
        return sp.Integer(0)
    p = sp.Poly(e, eps)
    return sum((c * eps**mono[0] for mono, c in p.terms() if mono[0] <= N), sp.Integer(0))


def germ_data(L, r, m, seed):
    random.seed(seed)
    def D(a, b):
        return sp.Matrix(a, b, lambda i, j: eps * sp.Rational(random.randint(-4, 4), 5))
    return ({s: D(r, r) for s in range(L)}, {s: D(r, m) for s in range(L)},
            {s: D(m, r) for s in range(L)}, {s: D(m, m) for s in range(L)})


def inv_series(Mx, N):
    Nn = trunc(Mx - sp.eye(Mx.rows), N)
    acc = sp.eye(Mx.rows); term = sp.eye(Mx.rows)
    for _ in range(N + 1):
        term = trunc(term * (-Nn), N); acc = acc + term
    return trunc(acc, N)


def base(L, r, m, X, Y, Z, T, N):
    Ir = sp.eye(r); Im = sp.eye(m); n = r + m
    A = {s: Ir + X[s] for s in range(L)}
    Ainv = {s: inv_series(A[s], N) for s in range(L)}
    C = {s: b22(A[s], Y[s], Z[s], T[s]) for s in range(L)}
    Pp = {0: sp.eye(n)}
    for j in range(1, L + 1):
        Pp[j] = trunc(Pp[j - 1] * C[j - 1], N)
    P = Pp[L]
    S = {s: trunc(T[s] - Z[s] * Ainv[s] * Y[s], N) for s in range(L)}
    w = {s: trunc(Ainv[s] * Y[s], N) for s in range(L)}
    K = {0: sp.zeros(m, m)}
    for s in range(1, L):
        K[s] = trunc(Z[s] * inv_series(Pp[s + 1][:r, :r], N) * Pp[s][:r, r:], N)
    Stil = {s: trunc((Im - K[s]) * S[s], N) for s in range(L)}
    return dict(A=A, Z=Z, w=w, Stil=Stil, P=P, r=r, m=m, L=L, n=n)


def moved_product(D, dedits, N):
    """dedits[s] = (dA,dZ,dw) matrices (possibly symbolic); truncate product to order N."""
    L, r, m = D['L'], D['r'], D['m']
    Cp = {}
    for s in range(L):
        A = D['A'][s] + dedits[s][0]
        Z = D['Z'][s] + dedits[s][1]
        w = D['w'][s] + dedits[s][2]
        Y = trunc(A * w, N); T = trunc(Z * w + D['Stil'][s], N)
        Cp[s] = b22(A, Y, Z, T)
    Pn = Cp[0]
    for s in range(1, L):
        Pn = trunc(Pn * Cp[s], N)
    return Pn


def reg_resid(D, Pn):
    r, m = D['r'], D['m']; P = D['P']; out = []
    for (a0, a1, b0, b1) in [(0, r, 0, r), (0, r, r, r + m), (r, r + m, 0, r)]:
        for i in range(a0, a1):
            for j in range(b0, b1):
                out.append(sp.expand(Pn[i, j] - P[i, j]))
    return out


def solve_germ(L, r, m, family, N, seed=3):
    X, Y, Z, T = germ_data(L, r, m, seed)
    D = base(L, r, m, X, Y, Z, T, N)
    solved = {s: [sp.zeros(r, r), sp.zeros(m, r), sp.zeros(r, m)] for s in range(L)}  # accumulated numeric edits
    for k in range(1, N + 1):
        # order-k symbolic coeffs
        sym = []
        dedits = {}
        for s in range(L):
            dA = solved[s][0].copy(); dZ = solved[s][1].copy(); dw = solved[s][2].copy()
            if 'A' in family:
                MA = sp.Matrix(r, r, lambda i, j: sp.Symbol(f'a{s}_{i}{j}')); sym += list(MA); dA = dA + eps**k * MA
            if 'Z' in family:
                MZ = sp.Matrix(m, r, lambda i, j: sp.Symbol(f'z{s}_{i}{j}')); sym += list(MZ); dZ = dZ + eps**k * MZ
            if 'w' in family:
                MW = sp.Matrix(r, m, lambda i, j: sp.Symbol(f'u{s}_{i}{j}')); sym += list(MW); dw = dw + eps**k * MW
            dedits[s] = (dA, dZ, dw)
        Pn = moved_product(D, dedits, k)
        res = reg_resid(D, Pn)
        eqs = []
        for e in res:
            ck = sp.expand(trunc_expr(e, k)).coeff(eps, k)
            if ck != 0:
                eqs.append(ck)
        if eqs:
            sol = sp.linsolve(eqs, sym)
            if len(sol) == 0:
                print(f"  fam={''.join(sorted(family)):4s} seed={seed}: OBSTRUCTED at eps^{k}")
                return ('OBSTRUCTED', k)
            s0 = list(sol)[0]
            sub = {}
            free = (set().union(*[set(sp.sympify(v).free_symbols) for v in s0]) if s0 else set())
            free -= {eps}
            for c, v in zip(sym, s0):
                sub[c] = sp.sympify(v).subs({f: 0 for f in free})
            # write solved order-k coeffs back (numeric)
            idx = 0
            for s in range(L):
                if 'A' in family:
                    for i in range(r):
                        for j in range(r):
                            solved[s][0][i, j] += eps**k * sub[sym[idx]]; idx += 1
                if 'Z' in family:
                    for i in range(m):
                        for j in range(r):
                            solved[s][1][i, j] += eps**k * sub[sym[idx]]; idx += 1
                if 'w' in family:
                    for i in range(r):
                        for j in range(m):
                            solved[s][2][i, j] += eps**k * sub[sym[idx]]; idx += 1
    # final verify
    dedits = {s: (solved[s][0], solved[s][1], solved[s][2]) for s in range(L)}
    Pn = moved_product(D, dedits, N)
    res = reg_resid(D, Pn)
    ok = all(trunc_expr(e, N) == 0 for e in res)
    print(f"  fam={''.join(sorted(family)):4s} seed={seed}: SOLVABLE to eps^{N},  verify==0: {ok}")
    return ('SOLVABLE', N, ok)


if __name__ == "__main__":
    if len(sys.argv) >= 5:
        L, r, m = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
        fam = set(sys.argv[4]); N = int(sys.argv[5]) if len(sys.argv) > 5 else 6
        seed = int(sys.argv[6]) if len(sys.argv) > 6 else 3
        print(f"L={L} r={r} m={m} fam={sys.argv[4]} N={N} seed={seed}")
        solve_germ(L, r, m, fam, N, seed)
    else:
        for (L, r, m, lbl) in [(3, 1, 1, "L=3 scalar"), (3, 1, 2, "L=3 m=2"),
                               (4, 1, 1, "L=4 scalar"), (4, 1, 2, "L=4 m=2")]:
            print(lbl)
            for fam in [set('w'), set('wZ')]:
                solve_germ(L, r, m, fam, 6)
