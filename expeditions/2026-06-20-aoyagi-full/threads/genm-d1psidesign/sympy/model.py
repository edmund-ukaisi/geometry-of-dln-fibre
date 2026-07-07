"""
Faithful exact-algebra model of the general-L deepest-point joint move `psiSplitRawGen`.

Objects (r x r pivot, per-layer core width m; interior frames = identity, J = frontEmbed so
the last-layer column split IS the threshold split -> uniform layer shape):

  layer  C_s = [[ A_s , Y_s ],
               [ Z_s , T_s ]]         A_s = I_r + X_s   (pivot base I + read X)
  full product  P = C_0 * C_1 * ... * C_{L-1}
  deepestEFull(q) = ( P11 - I_r , P12 , P21 )         (the reg residual the loss squares)
  loss-core reads (via conj-absorb) the PLAIN PRODUCT of the per-layer Schur cores.

  per-layer Schur core        S_s = T_s - Z_s A_s^{-1} Y_s          ( = blockSchur(C_s) )
  partial product             Pp(j) = C_0..C_{j-1}   (Pp(0)=I)
  coupling                    K_s = Z_s * (Pp(s+1)_11)^{-1} * (Pp(s)_12)    (K_0 = 0)
  coreProd                    S_0 (1-K_1) S_1 (1-K_2) S_2 ... (1-K_{L-1}) S_{L-1}

Invariant B (Schur recursion, F2 already banked): blockSchur(P) = coreProd.

The MOVE family we test (keep A_s, Z_s FIXED; set per-layer Schur core to (1-K_s)S_s;
choose new up-direction w'_s freely):
  Y'_s = A_s w'_s ,  T'_s = Z_s w'_s + (1-K_s) S_s .
  => new per-layer Schur core  T'_s - Z_s A_s^{-1} Y'_s = (1-K_s) S_s   (ANY w'_s)  -> Invariant B automatic.
Invariant A (the risk): can {w'_s} be chosen so the NEW product P' has
  (P'11, P'12, P'21) = (P11, P12, P21)  ?   (deepestEFull invariant)
"""
import sympy as sp


def block22(A, Y, Z, T):
    top = A.row_join(Y)
    bot = Z.row_join(T)
    return top.col_join(bot)


def toblocks(P, r):
    return P[:r, :r], P[:r, r:], P[r:, :r], P[r:, r:]


def prod(Cs):
    P = Cs[0]
    for s in range(1, len(Cs)):
        P = P * Cs[s]
    return P


def build_layers(L, r, m):
    X = {}; Y = {}; Z = {}; T = {}
    for s in range(L):
        X[s] = sp.Matrix(r, r, lambda i, j: sp.Symbol(f'X{s}_{i}{j}'))
        Y[s] = sp.Matrix(r, m, lambda i, j: sp.Symbol(f'Y{s}_{i}{j}'))
        Z[s] = sp.Matrix(m, r, lambda i, j: sp.Symbol(f'Z{s}_{i}{j}'))
        T[s] = sp.Matrix(m, m, lambda i, j: sp.Symbol(f'T{s}_{i}{j}'))
    return X, Y, Z, T


def schur_core(A, Y, Z, T):
    return T - Z * A.inv() * Y


def run(L, r, m, label):
    print("=" * 78)
    print(f"{label}   (L={L}, r={r}, core m={m})")
    print("=" * 78)
    X, Y, Z, T = build_layers(L, r, m)
    Ir = sp.eye(r); Im = sp.eye(m); n = r + m
    A = {s: Ir + X[s] for s in range(L)}
    C = {s: block22(A[s], Y[s], Z[s], T[s]) for s in range(L)}

    Pp = {0: sp.eye(n)}
    for j in range(1, L + 1):
        Pp[j] = Pp[j - 1] * C[j - 1]
    P = Pp[L]
    P11, P12, P21, P22 = toblocks(P, r)

    S = {s: schur_core(A[s], Y[s], Z[s], T[s]) for s in range(L)}

    K = {0: sp.zeros(m, m)}
    for s in range(1, L):
        K[s] = Z[s] * (Pp[s + 1][:r, :r]).inv() * (Pp[s][:r, r:])

    coreProd = S[0]
    for s in range(1, L):
        coreProd = coreProd * (Im - K[s]) * S[s]

    blockSchurP = P22 - P21 * P11.inv() * P12

    diffB = sp.simplify(blockSchurP - coreProd)
    okB = diffB == sp.zeros(m, m)
    print(f"[Invariant B]  blockSchur(P) == coreProd :  {okB}")
    if not okB:
        print("   residual:", diffB)

    # core-only move: T_s -> T_s - K_s S_s (keep X,Y,Z)
    Cco = {s: block22(A[s], Y[s], Z[s], T[s] - K[s] * S[s]) for s in range(L)}
    Pco = prod([Cco[s] for s in range(L)])
    d11 = sp.simplify(Pco[:r, :r] - P11)
    d12 = sp.simplify(Pco[:r, r:] - P12)
    d21 = sp.simplify(Pco[r:, :r] - P21)
    breaks = not (d11 == sp.zeros(r, r) and d12 == sp.zeros(r, m) and d21 == sp.zeros(m, r))
    print(f"[core-only move]  breaks deepestEFull :  {breaks}"
          f"   (dP11==0:{d11==sp.zeros(r,r)} dP12==0:{d12==sp.zeros(r,m)} dP21==0:{d21==sp.zeros(m,r)})")

    return dict(X=X, Y=Y, Z=Z, T=T, A=A, C=C, Pp=Pp, P=P, P11=P11, P12=P12, P21=P21, P22=P22,
                S=S, K=K, coreProd=coreProd, blockSchurP=blockSchurP, r=r, m=m, L=L, n=n)


if __name__ == "__main__":
    run(2, 1, 1, "L=2 scalar (sanity)")
    run(3, 1, 1, "L=3 scalar")
    run(4, 1, 1, "L=4 scalar")
