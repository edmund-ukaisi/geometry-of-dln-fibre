"""
INVARIANT A satisfiability test for the general-L joint move.

Move family (keep A_s, Z_s fixed; per-layer Schur core -> (1-K_s)S_s; up-direction w'_s free):
    Y'_s = A_s w'_s ,  T'_s = Z_s w'_s + (1-K_s) S_s .
Question: exists {w'_s} with (P'11,P'12,P'21) = (P11,P12,P21) ?

Two exact certificates of germ-existence:
 (1) exact-RATIONAL: pick rational layer data near 0, solve the (multilinear) system EXACTLY,
     verify (P'11,P'12,P'21)=(P11,P12,P21) and Invariant B for the moved point, all exact.
 (2) JACOBIAN-RANK at the origin: the derivative of {w'_s} |-> (P'11,P'12,P'21) is SURJECTIVE
     onto the constraint space at the base solution -> IFT gives an analytic germ solution.
     (Certifies existence for ALL nearby data, not just one point.)
"""
import sympy as sp


def block22(A, Y, Z, T):
    return A.row_join(Y).col_join(Z.row_join(T))


def prod(Cs):
    P = Cs[0]
    for s in range(1, len(Cs)):
        P = P * Cs[s]
    return P


def setup(L, r, m, val):
    """Build layer data; `val` maps a Symbol-name -> exact value (Rational) or returns None to keep symbolic."""
    X = {}; Y = {}; Z = {}; T = {}
    for s in range(L):
        X[s] = sp.Matrix(r, r, lambda i, j: val(f'X{s}_{i}{j}'))
        Y[s] = sp.Matrix(r, m, lambda i, j: val(f'Y{s}_{i}{j}'))
        Z[s] = sp.Matrix(m, r, lambda i, j: val(f'Z{s}_{i}{j}'))
        T[s] = sp.Matrix(m, m, lambda i, j: val(f'T{s}_{i}{j}'))
    Ir = sp.eye(r); Im = sp.eye(m); n = r + m
    A = {s: Ir + X[s] for s in range(L)}
    C = {s: block22(A[s], Y[s], Z[s], T[s]) for s in range(L)}
    Pp = {0: sp.eye(n)}
    for j in range(1, L + 1):
        Pp[j] = Pp[j - 1] * C[j - 1]
    P = Pp[L]
    S = {s: T[s] - Z[s] * A[s].inv() * Y[s] for s in range(L)}
    K = {0: sp.zeros(m, m)}
    for s in range(1, L):
        K[s] = Z[s] * (Pp[s + 1][:r, :r]).inv() * (Pp[s][:r, r:])
    return dict(X=X, Y=Y, Z=Z, T=T, A=A, C=C, Pp=Pp, P=P, S=S, K=K,
                Ir=Ir, Im=Im, n=n, r=r, m=m, L=L)


def moved_product(D, wp):
    """new product P' given up-directions wp[s] (r x m matrices)."""
    L, r, m = D['L'], D['r'], D['m']
    A, Z, S, K, Im = D['A'], D['Z'], D['S'], D['K'], D['Im']
    Cp = {}
    for s in range(L):
        Yp = A[s] * wp[s]
        Tp = Z[s] * wp[s] + (Im - K[s]) * S[s]
        Cp[s] = block22(A[s], Yp, Z[s], Tp)
    return prod([Cp[s] for s in range(L)]), Cp


def reg_residual_eqs(D, Pp_new):
    """list of scalar equations (P'11-P11, P'12-P12, P'21-P21) entrywise."""
    r, m = D['r'], D['m']; P = D['P']
    eqs = []
    for (a0, a1, b0, b1) in [(0, r, 0, r), (0, r, r, r + m), (r, r + m, 0, r)]:
        for i in range(a0, a1):
            for j in range(b0, b1):
                eqs.append(sp.expand(Pp_new[i, j] - P[i, j]))
    return eqs


def per_layer_schur_check(D, Cp):
    """verify each moved layer's Schur core == (1-K_s) S_s (Invariant B ingredient)."""
    L, r, m = D['L'], D['r'], D['m']
    A, Z, S, K, Im = D['A'], D['Z'], D['S'], D['K'], D['Im']
    ok = True
    for s in range(L):
        Ap = Cp[s][:r, :r]; Yp = Cp[s][:r, r:]; Zp = Cp[s][r:, :r]; Tp = Cp[s][r:, r:]
        Snew = Tp - Zp * Ap.inv() * Yp
        target = (Im - K[s]) * S[s]
        if sp.simplify(Snew - target) != sp.zeros(m, m):
            ok = False
    return ok


def wp_symbols(L, r, m):
    return {s: sp.Matrix(r, m, lambda i, j: sp.Symbol(f'wp{s}_{i}{j}')) for s in range(L)}


def cert_exact_rational(L, r, m, seed=0):
    print(f"\n--- exact-RATIONAL solvability : L={L}, r={r}, m={m} ---")
    import random
    random.seed(seed)
    # small rationals near 0 so pivots (I+X) invertible and partial-product pivots invertible
    def val(name):
        num = random.randint(-3, 3)
        return sp.Rational(num, 20)   # in [-0.15, 0.15]
    D = setup(L, r, m, val)
    wp = wp_symbols(L, r, m)
    Pnew, Cp = moved_product(D, wp)
    eqs = reg_residual_eqs(D, Pnew)
    unknowns = [wp[s][i, j] for s in range(L) for i in range(r) for j in range(m)]
    sol = sp.solve(eqs, unknowns, dict=True)
    if not sol:
        print("  NO SOLUTION found -> OBSTRUCTED at this data")
        return False
    sol = sol[0]
    # substitute back and verify EXACTLY
    wp_val = {s: wp[s].subs(sol) for s in range(L)}
    # any free unknown left symbolic -> set to 0 (a valid choice)
    freesyms = set().union(*[set(wp_val[s].free_symbols) for s in range(L)])
    zero_free = {z: 0 for z in freesyms}
    wp_val = {s: wp_val[s].subs(zero_free) for s in range(L)}
    Pnew2, Cp2 = moved_product(D, wp_val)
    resid = reg_residual_eqs(D, Pnew2)
    ok_reg = all(sp.simplify(e) == 0 for e in resid)
    ok_B = per_layer_schur_check(D, Cp2)
    print(f"  solution found;  (P'11,P'12,P'21)==(P11,P12,P21) EXACT: {ok_reg}")
    print(f"  per-layer Schur cores == (1-K_s)S_s (Invariant B ingredient): {ok_B}")
    # also confirm origin-fixing: at zero data the solution's wp -> 0
    return ok_reg and ok_B


def cert_jacobian_rank(L, r, m):
    """Germ-existence for ALL nearby data: derivative of {w'_s}|->(P'11,P'12,P'21) surjective at origin base.
       Base point = origin (all data 0). There wp=0 gives P'=I=P (deepestEFull=0). Check d/dwp is onto."""
    print(f"\n--- JACOBIAN-RANK germ-existence : L={L}, r={r}, m={m} ---")
    D = setup(L, r, m, lambda name: sp.Integer(0))   # origin data
    wp = wp_symbols(L, r, m)
    Pnew, Cp = moved_product(D, wp)
    eqs = reg_residual_eqs(D, Pnew)     # = (P'11-I, P'12, P'21) as fns of wp, at origin data
    unknowns = [wp[s][i, j] for s in range(L) for i in range(r) for j in range(m)]
    Jac = sp.Matrix([[sp.diff(e, u) for u in unknowns] for e in eqs])
    Jac0 = Jac.subs({u: 0 for u in unknowns})
    rk = Jac0.rank()
    ncon = len(eqs)
    print(f"  #constraints = {ncon},  #unknowns(wp) = {len(unknowns)},  rank(J0) = {rk}")
    print(f"  surjective onto constraints (rank == #constraints): {rk == ncon}")
    return rk == ncon


if __name__ == "__main__":
    print("=" * 78)
    print("INVARIANT A  (deepestEFull invariance) satisfiability")
    print("=" * 78)
    r1 = cert_exact_rational(3, 1, 1)
    r2 = cert_exact_rational(4, 1, 1)
    r3 = cert_exact_rational(3, 1, 2)   # NON-SCALAR core
    print("\n[jacobian-rank germ existence]")
    j1 = cert_jacobian_rank(3, 1, 1)
    j2 = cert_jacobian_rank(4, 1, 1)
    j3 = cert_jacobian_rank(3, 1, 2)
    print("\nSUMMARY exact-rational:", r1, r2, r3, " jacobian:", j1, j2, j3)
