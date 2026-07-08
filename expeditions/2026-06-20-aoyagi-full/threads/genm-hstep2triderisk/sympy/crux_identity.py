"""Crux identity-read recovery (Codex's cheapest check + the (star) used in the derisk):
   forcedDecodeLeft (P_0)   (P_0 * R)    = R        (Q_0 = I framing inverted)
   forcedDecodeRight(Q_last) (R * Q_last) = R        (P_last = I framing inverted)
for a FULLY SYMBOLIC generic block R and symbolic invertible frame corners.  Exact.

This is the (star) that makes  identityRead_s = forcedDecode(frame_s)(C_s - corM)  hold
IDENTICALLY, hence  f_s = forcedDecode(frame_s)(movedC_s - C_s)  exactly (so f_s inherits
the O(||q||^2) vanishing of movedC_s - C_s, with NO frame-created first-order term)."""
import sympy as sp


def fromB(A, Y, Z, T):
    return (A.row_join(Y)).col_join(Z.row_join(T))


def blk(M, r, w):
    d = {'11': (slice(0, r), slice(0, r)), '12': (slice(0, r), slice(r, None)),
         '21': (slice(r, None), slice(0, r)), '22': (slice(r, None), slice(r, None))}[w]
    return M[d[0], d[1]]


def fdL(F, D, r, Pinv):
    P21 = blk(F, r, '21')
    A, Y, Z, T = blk(D, r, '11'), blk(D, r, '12'), blk(D, r, '21'), blk(D, r, '22')
    return fromB(Pinv * A, Pinv * Y, Z - P21 * (Pinv * A), T - P21 * (Pinv * Y))


def fdR(Q, D, r, Qinv):
    Q12 = blk(Q, r, '12')
    A, Y, Z, T = blk(D, r, '11'), blk(D, r, '12'), blk(D, r, '21'), blk(D, r, '22')
    return fromB(A * Qinv, Y - A * Qinv * Q12, Z * Qinv, T - Z * Qinv * Q12)


def sym(a, b, name):
    return sp.Matrix(a, b, lambda i, j: sp.Symbol(f'{name}_{i}{j}'))


for (r, m) in [(1, 1), (1, 2), (2, 2), (2, 1)]:
    Im = sp.eye(m)
    P11 = sym(r, r, 'P'); Q11 = sym(r, r, 'Q')          # generic invertible corners
    P21 = sym(m, r, 'p'); Q12 = sym(r, m, 'q')          # generic constant off-blocks
    R = fromB(sym(r, r, 'X'), sym(r, m, 'Y'), sym(m, r, 'Z'), sym(m, m, 'T'))
    # realise the invertible corners by a genuine symbolic inverse (r<=2) => exact identities
    Pinv, Qinv = P11.inv(), Q11.inv()
    P0 = fromB(P11, sp.zeros(r, m), P21, Im)              # block-lower layer-0 frame
    Qlast = fromB(Q11, Q12, sp.zeros(m, r), Im)           # block-upper last-layer frame

    okL = sp.simplify(fdL(P0, P0 * R, r, Pinv) - R) == sp.zeros(r + m, r + m)
    okR = sp.simplify(fdR(Qlast, R * Qlast, r, Qinv) - R) == sp.zeros(r + m, r + m)
    print(f"r={r} m={m}:  forcedDecodeLeft(P0,P0*R)==R : {okL}   "
          f"forcedDecodeRight(Qlast,R*Qlast)==R : {okR}")
