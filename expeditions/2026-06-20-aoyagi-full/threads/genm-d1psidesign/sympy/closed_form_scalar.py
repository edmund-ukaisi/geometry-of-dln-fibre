"""
Closed-form of the scalar (m=1) up-direction correction at L=3, to exhibit the construction shape.
Move: keep A_s, Z_s; per-layer Schur core -> (1-K_s)S_s; up-direction w_s -> w'_s.
Solve (P'11,P'12,P'21) = (P11,P12,P21) for (w'_0,w'_1,w'_2) symbolically and simplify.
(Confirms Invariant A is a rational germ near origin for scalar cores; shows the L=2 pattern.)
"""
import sympy as sp

L, r, m = 3, 1, 1


def b22(A, Y, Z, T):
    return A.row_join(Y).col_join(Z.row_join(T))


X = {s: sp.Symbol(f'X{s}') for s in range(L)}
Y = {s: sp.Symbol(f'Y{s}') for s in range(L)}
Z = {s: sp.Symbol(f'Z{s}') for s in range(L)}
T = {s: sp.Symbol(f'T{s}') for s in range(L)}
A = {s: 1 + X[s] for s in range(L)}
C = {s: sp.Matrix([[A[s], Y[s]], [Z[s], T[s]]]) for s in range(L)}
Pp = {0: sp.eye(2)}
for j in range(1, L + 1):
    Pp[j] = Pp[j - 1] * C[j - 1]
P = Pp[L]
S = {s: T[s] - Z[s] / A[s] * Y[s] for s in range(L)}
K = {0: sp.Integer(0)}
for s in range(1, L):
    K[s] = Z[s] * (Pp[s + 1][0, 0])**(-1) * Pp[s][0, 1]
Stil = {s: (1 - K[s]) * S[s] for s in range(L)}

wp = {s: sp.Symbol(f"wp{s}") for s in range(L)}
Cp = {}
for s in range(L):
    Yp = A[s] * wp[s]
    Tp = Z[s] * wp[s] + Stil[s]
    Cp[s] = sp.Matrix([[A[s], Yp], [Z[s], Tp]])
Ppp = Cp[0] * Cp[1] * Cp[2]

eqs = [sp.expand(Ppp[0, 0] - P[0, 0]),
       sp.expand(Ppp[0, 1] - P[0, 1]),
       sp.expand(Ppp[1, 0] - P[1, 0])]
sol = sp.solve(eqs, [wp[0], wp[1], wp[2]], dict=True)
print("scalar L=3 up-only correction solvable:", bool(sol))
if sol:
    s0 = sol[0]
    for s in range(L):
        val = sp.simplify(s0.get(wp[s], wp[s]))
        # check germ: value at origin (all data 0)
        at0 = sp.simplify(val.subs({**{X[t]: 0 for t in range(L)}, **{Y[t]: 0 for t in range(L)},
                                    **{Z[t]: 0 for t in range(L)}, **{T[t]: 0 for t in range(L)}}))
        print(f"  w'_{s} at origin = {at0}   (finite germ: {at0.is_finite})")
    # verify the solution reproduces P blocks exactly
    chk = [sp.simplify(e.subs(s0)) for e in eqs]
    print("  reg-block match exact:", all(c == 0 for c in chk))
