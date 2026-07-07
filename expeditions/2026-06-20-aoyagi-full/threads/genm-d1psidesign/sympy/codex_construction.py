"""
DECISIVE reconciliation: implement Codex's EXPLICIT construction and test (A)+(B) EXACTLY
at finite rational data (small, near origin), for scalar and non-scalar cores, L=3 and L=4.

Codex claims an EXACT (not just germ) construction: keep pivots A_s fixed, edit up blocks Y_s
(all s), and for L>=3 edit ONE down block Z_0.  If it verifies exactly, then (i) no pivot edit is
needed and (ii) my earlier "wZ obstructed / need pivot" verdicts were artifacts of a greedy
order-by-order solve on underdetermined families.

Definitions (Codex):
  Q_s = C_0..C_{s-1} = [[B_s,R_s],[D_s,H_s]] ;  u_s = B_s^-1 R_s ;  v_s = D_s B_s^-1 ;  W_s = H_s - D_s B_s^-1 R_s
  V_s = Z_s A_s^-1 (layer down) ;  U_s = A_s^-1 Y_s (layer up)
  N_s = I_r + u_s V_s ;  M_s = I_m - V_s N_s^-1 u_s   (claimed = I - K_s) ;  S~_s = M_s S_s  (M_0=I)
  Up edit:  Y~_s = Y_s + N_s^-1 u_s (S_s - S~_s)
  Down (Z_0 only) via accumulators; ELSE Z~_s = Z_s.  T~_s = S~_s + Z~_s A_s^-1 Y~_s.
"""
import sympy as sp, random


def b22(A, Y, Z, T):
    return A.row_join(Y).col_join(Z.row_join(T))


def prod(Cs):
    P = Cs[0]
    for s in range(1, len(Cs)):
        P = P * Cs[s]
    return P


def gen(L, r, m, seed, scale=sp.Rational(1, 6)):
    random.seed(seed)
    def M(a, b):
        return sp.Matrix(a, b, lambda i, j: scale * sp.Rational(random.randint(-4, 4), 5))
    return ({s: M(r, r) for s in range(L)}, {s: M(r, m) for s in range(L)},
            {s: M(m, r) for s in range(L)}, {s: M(m, m) for s in range(L)})


def run(L, r, m, seed, use_Z0=True, verbose=False):
    Ir = sp.eye(r); Im = sp.eye(m); n = r + m
    X, Y, Z, T = gen(L, r, m, seed)
    A = {s: Ir + X[s] for s in range(L)}
    C = {s: b22(A[s], Y[s], Z[s], T[s]) for s in range(L)}
    Q = {0: sp.eye(n)}
    for s in range(1, L + 1):
        Q[s] = Q[s - 1] * C[s - 1]
    P = Q[L]
    B = {s: Q[s][:r, :r] for s in range(L + 1)}
    R = {s: Q[s][:r, r:] for s in range(L + 1)}
    D = {s: Q[s][r:, :r] for s in range(L + 1)}
    Hh = {s: Q[s][r:, r:] for s in range(L + 1)}
    u = {s: B[s].inv() * R[s] for s in range(L)}          # r x m
    W = {s: Hh[s] - D[s] * B[s].inv() * R[s] for s in range(L)}   # m x m
    V = {s: Z[s] * A[s].inv() for s in range(L)}           # m x r
    S = {s: T[s] - Z[s] * A[s].inv() * Y[s] for s in range(L)}    # m x m
    Nn = {s: Ir + u[s] * V[s] for s in range(L)}           # r x r
    Msh = {s: Im - V[s] * Nn[s].inv() * u[s] for s in range(L)}   # m x m  (claim = I-K_s)
    Stil = {s: Msh[s] * S[s] for s in range(L)}

    # cross-check M_s == I - K_s   (K_s = Z_s (Q_{s+1}_11)^-1 (Q_s)_12)
    Kchk = {0: sp.zeros(m, m)}
    for s in range(1, L):
        Kchk[s] = Z[s] * (Q[s + 1][:r, :r]).inv() * (Q[s][:r, r:])
    okM = all(sp.simplify(Msh[s] - (Im - Kchk[s])) == sp.zeros(m, m) for s in range(1, L))

    # up edit
    Ytil = {s: Y[s] + Nn[s].inv() * u[s] * (S[s] - Stil[s]) for s in range(L)}

    # down edit (Z_0 only) via accumulators (Codex): try the two readings of W~ recursion
    def make_moved(Z0edit):
        Ztil = {s: (Z0edit if s == 0 else Z[s]) for s in range(L)}
        Ttil = {s: Stil[s] + Ztil[s] * A[s].inv() * Ytil[s] for s in range(L)}
        Ct = {s: b22(A[s], Ytil[s], Ztil[s], Ttil[s]) for s in range(L)}
        return Ct

    results = {}
    # First: up-edit only (Z unchanged)
    for tag, Z0e in [('up-only', Z[0])]:
        Ct = make_moved(Z0e)
        Pn = prod([Ct[s] for s in range(L)])
        d11 = sp.simplify(Pn[:r, :r] - P[:r, :r]); d12 = sp.simplify(Pn[:r, r:] - P[:r, r:])
        d21 = sp.simplify(Pn[r:, :r] - P[r:, :r])
        results[tag] = (d11 == sp.zeros(r, r), d12 == sp.zeros(r, m), d21 == sp.zeros(m, r), None)

    # Down edit accumulators.  Reading (a): W~_{s+1}=W~_s * Stil_s ; reading (b): W~_{s+1}=W~_s*Msh_s*Stil_s
    def accum(readingb):
        va = sp.zeros(m, r); vt = sp.zeros(m, r); Wt = Im
        # note recursion index s = 0..L-1
        for s in range(L):
            va = va + W[s] * V[s] * Nn[s].inv() * B[s].inv()
            step = (Msh[s] * Stil[s]) if readingb else Stil[s]
            va_step = Wt * V[s] * Nn[s].inv() * B[s].inv()
            vt = vt + va_step
            Wt = Wt * step
        return va, vt
    for readingb in [False, True]:
        va, vt = accum(readingb)
        dV0 = va - vt
        Z0e = (V[0] + dV0) * A[0]
        Ct = make_moved(Z0e)
        Pn = prod([Ct[s] for s in range(L)])
        d11 = sp.simplify(Pn[:r, :r] - P[:r, :r]); d12 = sp.simplify(Pn[:r, r:] - P[:r, r:])
        d21 = sp.simplify(Pn[r:, :r] - P[r:, :r])
        # Invariant B: plain product of new per-layer Schur cores == coreProd (=blockSchur(P))
        Snew = {s: Ct[s][r:, r:] - Ct[s][r:, :r] * Ct[s][:r, :r].inv() * Ct[s][:r, r:] for s in range(L)}
        pp = Snew[0]
        for s in range(1, L):
            pp = pp * Snew[s]
        bs = P[r:, r:] - P[r:, :r] * P[:r, :r].inv() * P[:r, r:]
        okB = sp.simplify(pp - bs) == sp.zeros(m, m)
        results[f'up+Z0(read{"b" if readingb else "a"})'] = (
            d11 == sp.zeros(r, r), d12 == sp.zeros(r, m), d21 == sp.zeros(m, r), okB)
    return results, okM


if __name__ == "__main__":
    for (L, r, m) in [(3, 1, 1), (3, 1, 2), (4, 1, 1), (4, 1, 2),
                      (5, 1, 1), (3, 1, 3), (3, 2, 2), (5, 1, 2)]:
        for seed in (5, 11):
            res, okM = run(L, r, m, seed=seed)
            a, b, c, okB = res['up+Z0(readb)']
            au, bu, cu, _ = res['up-only']
            print(f"L={L} r={r} m={m} seed={seed}:  M==I-K:{okM}  "
                  f"UP-ONLY(P11,P12,P21)=({au},{bu},{cu})  "
                  f"UP+Z0(P11,P12,P21,InvB)=({a},{b},{c},{okB})")
