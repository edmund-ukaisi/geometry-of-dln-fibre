"""
INVARIANT A -- RIGOROUS near-origin germ test (power series in eps).

The germ hsub3reg lives near the DEEPEST point: layer data are analytic in x, vanishing at x=0.
Model a generic 1-parameter germ through the origin: X_s,Y_s,Z_s,T_s = eps * (generic rational dir).
The reg-block residual to correct (from the core untwist) is O(eps^3); the Jacobian of the reg-edit
map DEGENERATES at eps=0, so the correction must be found ORDER BY ORDER.

Move family (rigid Schur-core target (1-K_s)S_s; edits dA_s,dZ_s,dw_s as power series in eps):
    C'_s = [[A_s+dA_s, (A_s+dA_s)(w_s+dw_s)], [Z_s+dZ_s, (Z_s+dZ_s)(w_s+dw_s) + (1-K_s)S_s]]
The correction exists as an analytic germ iff the reg-block equations
    (P'11,P'12,P'21) = (P11,P12,P21)
are solvable to all orders in eps.  We solve to order N and report the max order reached
(a genuine obstruction shows up as an unsolvable linear system at some order <= N).
"""
import sympy as sp, random

eps = sp.Symbol('eps')


def block22(A, Y, Z, T):
    return A.row_join(Y).col_join(Z.row_join(T))


def prod(Cs):
    P = Cs[0]
    for s in range(1, len(Cs)):
        P = P * Cs[s]
    return P


def trunc(M, N):
    return M.applyfunc(lambda e: sp.series(sp.expand(e), eps, 0, N + 1).removeO())


def germ_data(L, r, m, seed):
    random.seed(seed)
    def D(rows, cols):
        return sp.Matrix(rows, cols, lambda i, j: eps * sp.Rational(random.randint(-4, 4), 5))
    return ({s: D(r, r) for s in range(L)}, {s: D(r, m) for s in range(L)},
            {s: D(m, r) for s in range(L)}, {s: D(m, m) for s in range(L)})


def base(L, r, m, X, Y, Z, T, N):
    Ir = sp.eye(r); Im = sp.eye(m); n = r + m
    A = {s: Ir + X[s] for s in range(L)}
    # inverse of A as truncated series (A = I + O(eps))
    def inv_series(Mx):
        # (I + N)^{-1} = sum (-N)^k ; N = Mx - I
        Nn = Mx - sp.eye(Mx.rows)
        acc = sp.eye(Mx.rows); term = sp.eye(Mx.rows)
        for k in range(1, N + 2):
            term = trunc(term * (-Nn), N)
            acc = acc + term
        return trunc(acc, N)
    Ainv = {s: inv_series(A[s]) for s in range(L)}
    C = {s: block22(A[s], Y[s], Z[s], T[s]) for s in range(L)}
    Pp = {0: sp.eye(n)}
    for j in range(1, L + 1):
        Pp[j] = trunc(Pp[j - 1] * C[j - 1], N)
    P = Pp[L]
    S = {s: trunc(T[s] - Z[s] * Ainv[s] * Y[s], N) for s in range(L)}
    w = {s: trunc(Ainv[s] * Y[s], N) for s in range(L)}
    # couplings K_s = Z_s (Pp(s+1)_11)^{-1} (Pp(s)_12)
    def inv_series_gen(Mx):
        Nn = Mx - sp.eye(Mx.rows)
        acc = sp.eye(Mx.rows); term = sp.eye(Mx.rows)
        for k in range(1, N + 2):
            term = trunc(term * (-Nn), N); acc = acc + term
        return trunc(acc, N)
    K = {0: sp.zeros(m, m)}
    for s in range(1, L):
        P11 = Pp[s + 1][:r, :r]; P12s = Pp[s][:r, r:]
        K[s] = trunc(Z[s] * inv_series_gen(P11) * P12s, N)
    Stil = {s: trunc((Im - K[s]) * S[s], N) for s in range(L)}
    return dict(A=A, Z=Z, w=w, Stil=Stil, P=P, r=r, m=m, L=L, Ir=Ir, Im=Im)


def solve_germ(L, r, m, family, N, seed=3, verbose=False):
    X, Y, Z, T = germ_data(L, r, m, seed)
    D = base(L, r, m, X, Y, Z, T, N)
    r_, m_, L_ = D['r'], D['m'], D['L']
    # unknown edit coefficients: dA_s, dZ_s, dw_s each = sum_{k=1..N} eps^k * coeff-matrix
    coeffs = []
    edits = {}
    for s in range(L):
        dA = sp.zeros(r_, r_); dZ = sp.zeros(m_, r_); dw = sp.zeros(r_, m_)
        for k in range(1, N + 1):
            if 'A' in family:
                MA = sp.Matrix(r_, r_, lambda i, j: sp.Symbol(f'a{s}_{k}_{i}{j}')); coeffs += list(MA); dA += eps**k * MA
            if 'Z' in family:
                MZ = sp.Matrix(m_, r_, lambda i, j: sp.Symbol(f'z{s}_{k}_{i}{j}')); coeffs += list(MZ); dZ += eps**k * MZ
            if 'w' in family:
                MW = sp.Matrix(r_, m_, lambda i, j: sp.Symbol(f'u{s}_{k}_{i}{j}')); coeffs += list(MW); dw += eps**k * MW
        edits[s] = (dA, dZ, dw)
    # moved product
    Cp = {}
    for s in range(L):
        A = D['A'][s] + edits[s][0]; Z_ = D['Z'][s] + edits[s][1]; w = D['w'][s] + edits[s][2]
        Yb = A * w; Tb = Z_ * w + D['Stil'][s]
        Cp[s] = block22(A, Yb, Z_, Tb)
    Pn = Cp[0]
    for s in range(1, L):
        Pn = trunc(Pn * Cp[s], N)
    # reg-block residual entries (as eps-polynomials)
    P = D['P']; res = []
    for (a0, a1, b0, b1) in [(0, r_, 0, r_), (0, r_, r_, r_ + m_), (r_, r_ + m_, 0, r_)]:
        for i in range(a0, a1):
            for j in range(b0, b1):
                res.append(sp.expand(Pn[i, j] - P[i, j]))
    res = [sp.Poly(e, eps) for e in res]

    # ITERATIVE order-by-order solve: at order k the eqn is LINEAR in order-k coeffs
    # (all nonlinear cross-terms involve strictly-lower orders, already substituted).
    def order_k_coeffs(k):
        return [c for c in coeffs if f'_{k}_' in c.name]
    subst = {}
    max_order = 0
    for k in range(1, N + 1):
        uk = order_k_coeffs(k)
        eqs_k = []
        for pe in res:
            ck = sp.expand(pe.coeff_monomial(eps**k).subs(subst))
            if ck != 0:
                eqs_k.append(ck)
        if not eqs_k:
            max_order = k
            continue
        sol = sp.linsolve(eqs_k, uk)
        if len(sol) == 0:
            print(f"  family={'+'.join(sorted(family)):5s} N={N}: OBSTRUCTED at order eps^{k}")
            return False, k
        s0 = list(sol)[0]
        newsub = {c: v for c, v in zip(uk, s0)}
        free = (set().union(*[set(sp.sympify(v).free_symbols) for v in s0]) if s0 else set()) - {eps}
        for f in free:
            newsub = {c: v.subs({f: 0}) for c, v in newsub.items()}
        subst.update(newsub)
        max_order = k
    # verify residual vanishes to order N under the assembled substitution
    chk_ok = True
    for pe in res:
        ev = sp.expand(pe.as_expr().subs(subst))
        evs = sp.series(ev, eps, 0, N + 1).removeO()
        if sp.expand(evs) != 0:
            chk_ok = False; break
    print(f"  family={'+'.join(sorted(family)):5s} N={N}: germ solvable to O(eps^{max_order}): "
          f"{max_order == N}   verify==0: {chk_ok}")
    return (max_order == N and chk_ok), max_order


if __name__ == "__main__":
    import sys
    if len(sys.argv) >= 5:
        L = int(sys.argv[1]); r = int(sys.argv[2]); m = int(sys.argv[3])
        fam = set(sys.argv[4]); N = int(sys.argv[5]) if len(sys.argv) > 5 else 6
        seed = int(sys.argv[6]) if len(sys.argv) > 6 else 3
        print(f"L={L} r={r} m={m} family={sys.argv[4]} N={N} seed={seed}")
        solve_germ(L, r, m, fam, N, seed=seed)
    else:
        N = 6
        for (L, r, m, lbl) in [(3, 1, 1, "L=3 scalar"), (3, 1, 2, "L=3 NON-scalar m=2"),
                               (4, 1, 1, "L=4 scalar"), (4, 1, 2, "L=4 NON-scalar m=2")]:
            print(f"\n{lbl}:")
            for fam in [set('w'), set('wZ')]:
                solve_germ(L, r, m, fam, N)
