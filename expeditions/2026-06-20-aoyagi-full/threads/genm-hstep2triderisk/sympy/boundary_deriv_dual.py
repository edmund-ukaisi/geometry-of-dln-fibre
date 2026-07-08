"""
genm-hstep2triderisk : BOUNDARY derivative-zero de-risk (EXACT, via dual numbers eps^2 = 0).

Load-bearing question (Producer 1, #120 hstep2): at q=0 (wstar) is
    D( psiReadBlk - identityRead )(0) = 0
at the BOUNDARY layers 0 / last (frame-dependent reads through forcedDecodeLeft/Right +
Ring.inverse)?  I.e. psiReadBlk_s - identityRead_s = O(||q||^2) at s in {0,last}, so
HasStrictFDerivAt (psiSplitRawGen - id) 0 0 holds INCLUDING the boundary.

Dual numbers R[eps]/(eps^2) carry (value, first-derivative) EXACTLY through +,-,*,inv
(inv valid where the eps=0 value is invertible; every inverse here has value I or a constant
unit frame corner).  So f.val = f(0) and f.der = f'(0) are EXACT, not truncation estimates.
GREEN iff f_s.val = 0 AND f_s.der = 0 at every layer, in particular s in {0, last}.

Model = faithful transcription of the Lean objects (see boundary_deriv.py header + cert.md).
"""
import sympy as sp
import random


class Dual:
    """value + eps*der matrix, eps^2 = 0.  val, der are sympy Matrices of equal shape."""
    __slots__ = ('v', 'd')

    def __init__(self, v, d=None):
        self.v = sp.Matrix(v)
        self.d = sp.zeros(*self.v.shape) if d is None else sp.Matrix(d)

    def __add__(s, o): return Dual(s.v + o.v, s.d + o.d)
    def __sub__(s, o): return Dual(s.v - o.v, s.d - o.d)
    def __mul__(s, o): return Dual(s.v * o.v, s.v * o.d + s.d * o.v)

    def inv(s):
        vi = s.v.inv()
        return Dual(vi, -vi * s.d * vi)

    def blk(s, r, which):
        sl = {'11': (slice(0, r), slice(0, r)), '12': (slice(0, r), slice(r, None)),
              '21': (slice(r, None), slice(0, r)), '22': (slice(r, None), slice(r, None))}[which]
        return Dual(s.v[sl[0], sl[1]], s.d[sl[0], sl[1]])

    def is_zero(s):
        return s.v == sp.zeros(*s.v.shape) and s.d == sp.zeros(*s.d.shape)


def const(M):        # eps-independent constant (der = 0)
    return Dual(M, sp.zeros(*sp.Matrix(M).shape))


def linear(M):       # pure first-order eps*M (val = 0, der = M)
    return Dual(sp.zeros(*sp.Matrix(M).shape), M)


def fromBlocks(A, Y, Z, T):
    v = (A.v.row_join(Y.v)).col_join(Z.v.row_join(T.v))
    d = (A.d.row_join(Y.d)).col_join(Z.d.row_join(T.d))
    return Dual(v, d)


def dzeros(a, b): return Dual(sp.zeros(a, b))
def deye(n): return const(sp.eye(n))


def forcedDecodeLeft(F, D, r):
    Pinv = F.blk(r, '11').inv()
    P21 = F.blk(r, '21')
    A, Y, Z, T = D.blk(r, '11'), D.blk(r, '12'), D.blk(r, '21'), D.blk(r, '22')
    return fromBlocks(Pinv * A, Pinv * Y, Z - P21 * (Pinv * A), T - P21 * (Pinv * Y))


def forcedDecodeRight(Q, D, r):
    Qinv = Q.blk(r, '11').inv()
    Q12 = Q.blk(r, '12')
    A, Y, Z, T = D.blk(r, '11'), D.blk(r, '12'), D.blk(r, '21'), D.blk(r, '22')
    return fromBlocks(A * Qinv, Y - A * Qinv * Q12, Z * Qinv, T - Z * Qinv * Q12)


def gen(a, b, rng, sc=sp.Rational(1, 5)):
    return sp.Matrix(a, b, lambda i, j: sc * sp.Rational(rng.randint(-4, 4), 4))


def build(L, r, m, seed, other_side=False):
    rng = random.Random(seed)
    Ir, Im = sp.eye(r), sp.eye(m)
    corM = const(fromBlocks(deye(r).blk(r, '11'), dzeros(r, m), dzeros(m, r), dzeros(m, m)).v)

    def inv_const(dim):
        while True:
            M = sp.eye(dim) + gen(dim, dim, rng, sp.Rational(1, 3))
            if M.det() != 0:
                return M
    P11, Q11 = inv_const(r), inv_const(r)
    P21, Q12 = gen(m, r, rng), gen(r, m, rng)
    P0 = const(fromBlocks(const(P11), dzeros(r, m), const(P21), deye(m)).v)     # block-lower
    Qlast = const(fromBlocks(const(Q11), const(Q12), dzeros(m, r), deye(m)).v)  # block-upper

    rawDev = []
    for s in range(L):
        rawDev.append(linear(fromBlocks(linear(gen(r, r, rng)), linear(gen(r, m, rng)),
                                        linear(gen(m, r, rng)), linear(gen(m, m, rng))).d))
    Ps, Qs = [], []
    for s in range(L):
        if s == 0:
            Pcur = P0
            Qcur = const(fromBlocks(const(inv_const(r)), const(gen(r, m, rng)),
                                    dzeros(m, r), deye(m)).v) if other_side else deye(r + m)
        elif s == L - 1:
            Pcur = const(fromBlocks(const(inv_const(r)), dzeros(r, m),
                                    const(gen(m, r, rng)), deye(m)).v) if other_side else deye(r + m)
            Qcur = Qlast
        else:
            Pcur, Qcur = deye(r + m), deye(r + m)
        Ps.append(Pcur); Qs.append(Qcur)

    C = [corM + Ps[s] * rawDev[s] * Qs[s] for s in range(L)]
    return dict(C=C, rawDev=rawDev, r=r, m=m, corM=corM, P0=P0, Qlast=Qlast)


def moved_chain(C, L, r, m):
    Ir, Im = deye(r), deye(m)

    def partProd(k):
        P = deye(r + m)
        for s in range(k):
            P = P * C[s]
        return P

    def blockSchur(M):
        return M.blk(r, '22') - M.blk(r, '21') * M.blk(r, '11').inv() * M.blk(r, '12')

    def Kcoup(k):
        return C[k].blk(r, '21') * partProd(k + 1).blk(r, '11').inv() * partProd(k).blk(r, '12')

    def uNorm(s):
        Q = partProd(s)
        return Q.blk(r, '11').inv() * Q.blk(r, '12')

    def vDown(s):
        return C[s].blk(r, '21') * C[s].blk(r, '11').inv()

    def nMix(s):
        return Ir + uNorm(s) * vDown(s)

    def schurTilde(s):
        return (Im - Kcoup(s)) * blockSchur(C[s])

    def upEdit(s):
        return nMix(s).inv() * uNorm(s) * (blockSchur(C[s]) - schurTilde(s))

    def wHat(k):
        W = Im
        for j in range(k):
            W = W * (Im - Kcoup(j)) * schurTilde(j)
        return W

    def hTermLC(j):
        Q = partProd(j)
        return (blockSchur(Q) - wHat(j)) * vDown(j) * nMix(j).inv() * Q.blk(r, '11').inv()

    deltaV0 = dzeros(m, r)
    for j in range(L):
        deltaV0 = deltaV0 + hTermLC(j)
    Z0edit0 = C[0].blk(r, '21') + deltaV0 * C[0].blk(r, '11')

    def movedZ(s): return Z0edit0 if s == 0 else C[s].blk(r, '21')
    def movedY(s): return C[s].blk(r, '12') + upEdit(s)
    def movedT(s): return schurTilde(s) + movedZ(s) * C[s].blk(r, '11').inv() * movedY(s)
    def movedC(s): return fromBlocks(C[s].blk(r, '11'), movedY(s), movedZ(s), movedT(s))
    return [movedC(s) for s in range(L)], deltaV0, [upEdit(s) for s in range(L)]


def run(L, r, m, seed, other_side=False):
    inst = build(L, r, m, seed, other_side=other_side)
    r_, m_, corM = inst['r'], inst['m'], inst['corM']
    mC, deltaV0, upEdits = moved_chain(inst['C'], L, r_, m_)
    rows = []
    for s in range(L):
        D = mC[s] - corM
        if s == 0:
            g = forcedDecodeLeft(inst['P0'], D, r_)
        elif s == L - 1:
            g = forcedDecodeRight(inst['Qlast'], D, r_)
        else:
            g = D
        f = g - inst['rawDev'][s]
        pos = 'layer0' if s == 0 else ('LAST' if s == L - 1 else 'interior')
        rows.append((s, pos, f.v == sp.zeros(*f.v.shape), f.d == sp.zeros(*f.d.shape)))
    return rows


if __name__ == "__main__":
    print("=" * 88)
    print("TRUE DESIGN (only P_0 block-LOWER at layer 0, Q_last block-UPPER at last;")
    print("             P_last = Q_0 = I ; interior frames I; frames q-INDEPENDENT).")
    print("  f_s = psiReadBlk_s - identityRead_s ;  f(0)=value ;  Df(0)=first derivative")
    print("=" * 88)
    cases = [(3, 1, 1, 5), (3, 1, 2, 5), (3, 1, 2, 11), (4, 1, 1, 5), (4, 1, 2, 5),
             (4, 1, 2, 11), (3, 2, 2, 7), (3, 2, 2, 13), (4, 2, 2, 3), (5, 1, 2, 5)]
    allgreen = True
    for (L, r, m, seed) in cases:
        rows = run(L, r, m, seed)
        s0 = all(c0 for (_, _, c0, _) in rows)
        s1 = all(c1 for (_, _, _, c1) in rows)
        bdry = [(s, pos, c0, c1) for (s, pos, c0, c1) in rows if pos in ('layer0', 'LAST')]
        tag = "GREEN" if (s0 and s1) else "**BREAK**"
        bstr = "  ".join(f"{pos}:f0={c0},Df0={c1}" for (s, pos, c0, c1) in bdry)
        print(f"L={L} r={r} m={m} seed={seed}: all f(0)=0:{s0}  all Df(0)=0:{s1}  [{tag}]   {bstr}")
        if not (s0 and s1):
            allgreen = False
    print("-" * 88)
    print(f"TRUE-DESIGN VERDICT: {'ALL value & first-derivative ZERO at boundary+interior => GREEN' if allgreen else 'BREAK FOUND'}")

    print("\n" + "=" * 88)
    print("FALSIFICATION PROBE (wrongly turn ON the other-side boundary frames Q_0, P_last):")
    print("  single-sided forcedDecode should then MISS the other frame => boundary Df(0) != 0.")
    print("=" * 88)
    for (L, r, m, seed) in [(3, 1, 2, 5), (4, 1, 2, 11), (3, 2, 2, 7)]:
        rows = run(L, r, m, seed, other_side=True)
        bdry = [(pos, c0, c1) for (s, pos, c0, c1) in rows if pos in ('layer0', 'LAST')]
        bstr = "  ".join(f"{pos}:f0={c0},Df0={c1}" for (pos, c0, c1) in bdry)
        broke = any((not c1) for (_, _, c1) in bdry)
        print(f"L={L} r={r} m={m} seed={seed}:  {bstr}   -> boundary break: {broke}")
