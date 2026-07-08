"""
genm-hstep2triderisk : boundary LEADING-ORDER characterisation (corroborate cert O(||q||^3)).

Truncated eps-series arithmetic (nilpotent eps^K = 0), Neumann inverse to stay polynomial.
Reports, per layer, the leading eps-order of  f_s = psiReadBlk_s - identityRead_s .
GREEN needs order >= 2 (first derivative zero); cert claims O(eps^3).  Scalar/small cases (cheap).
Model identical to boundary_deriv_dual.py (faithful Lean transcription).
"""
import sympy as sp
import random

eps = sp.symbols('eps')
K = 5  # keep terms eps^0 .. eps^4


def tr(e):
    return sp.series(sp.expand(e), eps, 0, K).removeO()


def trM(M):
    return M.applyfunc(tr)


def fromBlocks(A, Y, Z, T):
    return trM((A.row_join(Y)).col_join(Z.row_join(T)))


def B(M, r, w):
    sl = {'11': (slice(0, r), slice(0, r)), '12': (slice(0, r), slice(r, None)),
          '21': (slice(r, None), slice(0, r)), '22': (slice(r, None), slice(r, None))}[w]
    return M[sl[0], sl[1]]


def mul(A, Bm):
    return trM(A * Bm)


def inv(M):
    n = M.shape[0]
    M0 = M.subs(eps, 0)
    M0i = M0.inv()
    E = trM(M0i * M - sp.eye(n))          # O(eps)
    S = sp.eye(n); term = sp.eye(n)
    for _ in range(K):
        term = trM(-term * E)
        S = trM(S + term)
    return trM(S * M0i)


def gen(a, b, rng, sc=sp.Rational(1, 5)):
    return sp.Matrix(a, b, lambda i, j: sc * sp.Rational(rng.randint(-4, 4), 4))


def order_of(e):
    e = sp.expand(e)
    if e == 0:
        return None
    for k in range(K):
        if sp.simplify(e.coeff(eps, k)) != 0:
            return k
    return '>=%d' % K


def lead(M):
    os = [order_of(M[i, j]) for i in range(M.rows) for j in range(M.cols)]
    nums = [o for o in os if isinstance(o, int)]
    return min(nums) if nums else 'ZERO(>=%d)' % K


def build(L, r, m, seed):
    rng = random.Random(seed)
    Ir, Im = sp.eye(r), sp.eye(m)
    corM = fromBlocks(Ir, sp.zeros(r, m), sp.zeros(m, r), sp.zeros(m, m))

    def inv_const(d):
        while True:
            Mx = sp.eye(d) + gen(d, d, rng, sp.Rational(1, 3))
            if Mx.det() != 0:
                return Mx
    P11, Q11 = inv_const(r), inv_const(r)
    P21, Q12 = gen(m, r, rng), gen(r, m, rng)
    P0 = fromBlocks(P11, sp.zeros(r, m), P21, Im)
    Qlast = fromBlocks(Q11, Q12, sp.zeros(m, r), Im)
    rawDev = [fromBlocks(eps * gen(r, r, rng), eps * gen(r, m, rng),
                         eps * gen(m, r, rng), eps * gen(m, m, rng)) for _ in range(L)]
    Ps = [P0 if s == 0 else sp.eye(r + m) for s in range(L)]
    Qs = [Qlast if s == L - 1 else sp.eye(r + m) for s in range(L)]
    C = [trM(corM + mul(mul(Ps[s], rawDev[s]), Qs[s])) for s in range(L)]
    return dict(C=C, rawDev=rawDev, r=r, m=m, corM=corM, P0=P0, Qlast=Qlast)


def moved(C, L, r, m):
    Ir, Im = sp.eye(r), sp.eye(m)

    def pp(k):
        P = sp.eye(r + m)
        for s in range(k):
            P = mul(P, C[s])
        return P

    def bs(M):
        return trM(B(M, r, '22') - mul(mul(B(M, r, '21'), inv(B(M, r, '11'))), B(M, r, '12')))

    def Kc(k):
        return trM(mul(mul(B(C[k], r, '21'), inv(B(pp(k + 1), r, '11'))), B(pp(k), r, '12')))

    def uN(s):
        Q = pp(s); return mul(inv(B(Q, r, '11')), B(Q, r, '12'))

    def vD(s):
        return mul(B(C[s], r, '21'), inv(B(C[s], r, '11')))

    def nM(s):
        return trM(Ir + mul(uN(s), vD(s)))

    def sT(s):
        return mul(Im - Kc(s), bs(C[s]))

    def uE(s):
        return mul(mul(inv(nM(s)), uN(s)), bs(C[s]) - sT(s))

    def wH(k):
        W = Im
        for j in range(k):
            W = mul(mul(W, Im - Kc(j)), sT(j))
        return W

    def hT(j):
        Q = pp(j)
        return mul(mul(mul(bs(Q) - wH(j), vD(j)), inv(nM(j))), inv(B(Q, r, '11')))

    dV0 = sp.zeros(m, r)
    for j in range(L):
        dV0 = trM(dV0 + hT(j))
    Z0e = trM(B(C[0], r, '21') + mul(dV0, B(C[0], r, '11')))

    def mZ(s): return Z0e if s == 0 else B(C[s], r, '21')
    def mY(s): return trM(B(C[s], r, '12') + uE(s))
    def mT(s): return trM(sT(s) + mul(mul(mZ(s), inv(B(C[s], r, '11'))), mY(s)))
    def mC(s): return fromBlocks(B(C[s], r, '11'), mY(s), mZ(s), mT(s))
    return [mC(s) for s in range(L)], dV0


def fdL(F, D, r):
    Pinv = inv(B(F, r, '11')); P21 = B(F, r, '21')
    A, Y, Z, T = B(D, r, '11'), B(D, r, '12'), B(D, r, '21'), B(D, r, '22')
    return fromBlocks(mul(Pinv, A), mul(Pinv, Y),
                      trM(Z - mul(P21, mul(Pinv, A))), trM(T - mul(P21, mul(Pinv, Y))))


def fdR(Q, D, r):
    Qinv = inv(B(Q, r, '11')); Q12 = B(Q, r, '12')
    A, Y, Z, T = B(D, r, '11'), B(D, r, '12'), B(D, r, '21'), B(D, r, '22')
    return fromBlocks(mul(A, Qinv), trM(Y - mul(mul(A, Qinv), Q12)),
                      mul(Z, Qinv), trM(T - mul(mul(Z, Qinv), Q12)))


def run(L, r, m, seed):
    inst = build(L, r, m, seed)
    r_, corM = inst['r'], inst['corM']
    mC, dV0 = moved(inst['C'], L, r_, m)
    out = []
    for s in range(L):
        D = trM(mC[s] - corM)
        if s == 0:
            g = fdL(inst['P0'], D, r_)
        elif s == L - 1:
            g = fdR(inst['Qlast'], D, r_)
        else:
            g = D
        f = trM(g - inst['rawDev'][s])
        pos = 'layer0' if s == 0 else ('LAST' if s == L - 1 else 'interior')
        out.append((s, pos, lead(f)))
    return out, lead(dV0)


if __name__ == "__main__":
    print("leading eps-order of f_s = psiReadBlk_s - identityRead_s  (truncated to eps^%d)" % (K - 1))
    print("order >= 2 => first derivative zero (GREEN); cert claims O(eps^3).")
    print("=" * 72)
    for (L, r, m, seed) in [(3, 1, 1, 5), (4, 1, 1, 5), (3, 1, 1, 11), (3, 1, 2, 5), (4, 1, 2, 7)]:
        out, dvo = run(L, r, m, seed)
        print(f"\nL={L} r={r} m={m} seed={seed}   (deltaV0 leading order: {dvo})")
        for (s, pos, lo) in out:
            print(f"   s={s:<2} {pos:<9}  leading eps-order of f_s = {lo}")
