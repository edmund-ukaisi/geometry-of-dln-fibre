"""
INVARIANT A, decisive satisfiability with RICHER reg freedom.

Move family (rigid per-layer Schur-core target S~_s = (1-K_s)S_s; edit the L-part A'_s, Z'_s
AND up-direction w'_s; core T'_s determined to hold the Schur core):
    C'_s = [[ A'_s ,        A'_s w'_s        ],
            [ Z'_s ,  Z'_s w'_s + (1-K_s)S_s ]]
    => blockSchur(C'_s) = (1-K_s)S_s  for ANY (A'_s, Z'_s, w'_s)   -> Invariant B automatic.

Base of the family = the "core-only" move (A'_s=A_s, Z'_s=Z_s, w'_s=w_s).
IFT solvability test (exact, at a GENERIC rational base so the germ is non-degenerate):
    the reg-block residual map  R(edits) = (P'11-P11, P'12-P12, P'21-P21)
    has R(0) = delta_coreonly (nonzero).  Invariant A holds near this base iff
    delta_coreonly is in the RANGE of the Jacobian dR/d(edits) at edits=0.
    We test the STRONGER sufficient condition: dR/d(edits) SURJECTIVE (rank == #constraints)
    -> then delta is trivially in range and a germ correction exists (implicit function thm).
"""
import sympy as sp, random


def block22(A, Y, Z, T):
    return A.row_join(Y).col_join(Z.row_join(T))


def prod(Cs):
    P = Cs[0]
    for s in range(1, len(Cs)):
        P = P * Cs[s]
    return P


def base_data(L, r, m, seed):
    random.seed(seed)
    def M(rows, cols):
        return sp.Matrix(rows, cols, lambda i, j: sp.Rational(random.randint(-4, 4), 7))
    X = {s: M(r, r) for s in range(L)}
    Y = {s: M(r, m) for s in range(L)}
    Z = {s: M(m, r) for s in range(L)}
    T = {s: M(m, m) for s in range(L)}
    return X, Y, Z, T


def compute(L, r, m, X, Y, Z, T):
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
    w = {s: A[s].inv() * Y[s] for s in range(L)}   # original up-direction
    Stil = {s: (Im - K[s]) * S[s] for s in range(L)}  # target Schur cores
    return dict(A=A, Z=Z, C=C, Pp=Pp, P=P, S=S, K=K, w=w, Stil=Stil, Ir=Ir, Im=Im, n=n, r=r, m=m, L=L)


def moved(D, edits, family):
    """edits: dict layer-> (dA, dZ, dw) symbolic matrices; family selects which are active."""
    L, r, m = D['L'], D['r'], D['m']
    Cp = {}
    for s in range(L):
        A = D['A'][s] + (edits[s]['dA'] if 'A' in family else sp.zeros(r, r))
        Z = D['Z'][s] + (edits[s]['dZ'] if 'Z' in family else sp.zeros(m, r))
        w = D['w'][s] + (edits[s]['dw'] if 'w' in family else sp.zeros(r, m))
        Y = A * w
        T = Z * w + D['Stil'][s]
        Cp[s] = block22(A, Y, Z, T)
    return prod([Cp[s] for s in range(L)]), Cp


def reg_resid(D, Pn):
    r, m = D['r'], D['m']; P = D['P']
    out = []
    for (a0, a1, b0, b1) in [(0, r, 0, r), (0, r, r, r + m), (r, r + m, 0, r)]:
        for i in range(a0, a1):
            for j in range(b0, b1):
                out.append(Pn[i, j] - P[i, j])
    return out


def edit_symbols(L, r, m):
    E = {}
    for s in range(L):
        E[s] = dict(
            dA=sp.Matrix(r, r, lambda i, j: sp.Symbol(f'dA{s}_{i}{j}')),
            dZ=sp.Matrix(m, r, lambda i, j: sp.Symbol(f'dZ{s}_{i}{j}')),
            dw=sp.Matrix(r, m, lambda i, j: sp.Symbol(f'dw{s}_{i}{j}')),
        )
    return E


def ift_test(L, r, m, family, seed=1):
    D = compute(L, r, m, *base_data(L, r, m, seed))
    E = edit_symbols(L, r, m)
    Pn, Cp = moved(D, E, family)
    R = reg_resid(D, Pn)
    # unknowns present in this family
    unk = []
    for s in range(L):
        if 'A' in family: unk += list(E[s]['dA'])
        if 'Z' in family: unk += list(E[s]['dZ'])
        if 'w' in family: unk += list(E[s]['dw'])
    J = sp.Matrix([[sp.diff(rr, u) for u in unk] for rr in R])
    zero = {u: 0 for u in unk}
    J0 = J.subs(zero)                        # Jacobian at base (core-only move)
    delta = sp.Matrix([rr.subs(zero) for rr in R])   # residual at base
    rk = J0.rank()
    ncon = len(R)
    # delta in range(J0)?
    aug = J0.row_join(delta)
    in_range = (aug.rank() == rk)
    print(f"  family={'+'.join(sorted(family)) or 'none':7s}  #con={ncon} #unk={len(unk)} "
          f"rank(J0)={rk}  surjective={rk==ncon}  delta_in_range={in_range}")
    return rk == ncon, in_range


if __name__ == "__main__":
    print("=" * 78)
    print("INVARIANT A: IFT solvability at generic base, by move family")
    print("=" * 78)
    for (L, r, m, lbl) in [(3, 1, 1, "L=3 scalar"), (4, 1, 1, "L=4 scalar"),
                           (3, 1, 2, "L=3 NON-scalar m=2"), (4, 1, 2, "L=4 NON-scalar m=2")]:
        print(f"\n{lbl}:")
        for fam in [set('w'), set('wZ'), set('wZA')]:
            ift_test(L, r, m, fam)
