"""
genm-hstep2triderisk : BOUNDARY derivative-zero de-risk for Producer 1 of #120 hstep2.

Question: at q = 0 (wstar), is  D( psiReadBlk - identityRead )(0) = 0  at the BOUNDARY
layers 0 / last (the frame-dependent reads through forcedDecodeLeft/Right + Ring.inverse)?
Equivalently: psiReadBlk(q,s) - identityRead(q,s) = O(||q||^2) at s in {0, last}, so that
psiSplitRawGen - id = O(||q||^3) (>= o(||q||), first derivative zero) INCLUDING the boundary.

We model the ACTUAL Lean objects faithfully (DeepestPsiSplitRawGen.lean +
DeepestPsiSplitGenMoved.lean + DeepestPsiSplitGenLeftCol.lean + DeepestFramedProductPivot.lean):

  framedLayer:  C_s = corM + P_s * fromBlocks(X_s,Y_s,Z_s,T_s) * Q_s      corM = fromBlocks(I_r,0,0,0)
  frames (q-INDEPENDENT constants at wstar, from the triangular bundle):
     layer 0    : P_0 = fromBlocks(P11, 0, P21, I_m)  (block-LOWER),  Q_0 = I
     interior s : P_s = Q_s = I
     last layer : P_last = I,  Q_last = fromBlocks(Q11, Q12, 0, I_m)  (block-UPPER)
  abstract move (movedC / Z0edit0 / up-edit / core) operates on the FRAMED chain C.
  psiTargetD_s = movedC C Z0e s - corM
  psiGhat_s    : interior = psiTargetD_s
                 layer 0  = forcedDecodeLeft (P_0)  (psiTargetD_0)
                 last     = forcedDecodeRight(Q_last)(psiTargetD_last)
  psiReadBlk   = psiGhat (the H-width relabel is a q-independent permutation; irrelevant here)
  identityRead_s = q's own reads = fromBlocks(X_s,Y_s,Z_s,T_s) = rawDev_s     (linear in q)

Deviations rawDev_s = eps * (generic rational blocks).  eps SYMBOLIC.
We check, entrywise, the eps^0 and eps^1 coefficients of  f_s = psiReadBlk_s - identityRead_s.
GREEN iff f_s(eps=0)=0 AND d/deps f_s |_0 = 0 at EVERY layer, in particular s in {0, last}.
"""
import sympy as sp
import random

eps = sp.symbols('eps')


def fromBlocks(A, Y, Z, T):
    return A.row_join(Y).col_join(Z.row_join(T))


def B11(M, r): return M[:r, :r]
def B12(M, r): return M[:r, r:]
def B21(M, r): return M[r:, :r]
def B22(M, r): return M[r:, r:]


def prod(mats):
    P = mats[0]
    for M in mats[1:]:
        P = P * M
    return P


# ------- forced decodes (EXACT transcription of the Lean defs) -------
def forcedDecodeLeft(F, D, r):
    Pinv = B11(F, r).inv()          # Ring.inverse F.toBlocks11 ; F11 constant unit
    P21 = B21(F, r)
    A, Y, Z, T = B11(D, r), B12(D, r), B21(D, r), B22(D, r)
    return fromBlocks(Pinv * A, Pinv * Y, Z - P21 * (Pinv * A), T - P21 * (Pinv * Y))


def forcedDecodeRight(Q, D, r):
    Qinv = B11(Q, r).inv()          # Ring.inverse Q.toBlocks11 ; Q11 constant unit
    Q12 = B12(Q, r)
    A, Y, Z, T = B11(D, r), B12(D, r), B21(D, r), B22(D, r)
    return fromBlocks(A * Qinv, Y - A * Qinv * Q12, Z * Qinv, T - Z * Qinv * Q12)


def gen_rat(a, b, rng, scale=sp.Rational(1, 5)):
    return sp.Matrix(a, b, lambda i, j: scale * sp.Rational(rng.randint(-4, 4), 4))


def build(L, r, m, seed, other_side_frames=False):
    """Return (framed chain C, rawDev list, frames P,Q, r) for the concrete instance.

    other_side_frames=True (a FALSIFICATION probe): additionally make Q_0 and P_last
    non-trivial. The design says they are I; if they are not, forcedDecode should FAIL to
    invert the framing => identityRead mismatch => first-order break. Used to confirm the
    model is faithful (the derisk is decisive only if the TRUE design is green AND the wrong
    design breaks).
    """
    rng = random.Random(seed)
    Ir, Im = sp.eye(r), sp.eye(m)
    corM = fromBlocks(Ir, sp.zeros(r, m), sp.zeros(m, r), sp.zeros(m, m))

    # q-independent constant frame corners (generic invertible; deepBlkA_0 / deepBlkZ_last analog)
    def invert_const(dim):
        while True:
            M = sp.eye(dim) + gen_rat(dim, dim, rng, sp.Rational(1, 3))
            if M.det() != 0:
                return M
    P11 = invert_const(r)
    Q11 = invert_const(r)
    P21 = gen_rat(m, r, rng)
    Q12 = gen_rat(r, m, rng)

    P0 = fromBlocks(P11, sp.zeros(r, m), P21, Im)                 # block-lower left frame
    Qlast = fromBlocks(Q11, Q12, sp.zeros(m, r), Im)             # block-upper right frame

    # deviations (linear in eps)
    rawDev = []
    for s in range(L):
        X = eps * gen_rat(r, r, rng)
        Y = eps * gen_rat(r, m, rng)
        Z = eps * gen_rat(m, r, rng)
        T = eps * gen_rat(m, m, rng)
        rawDev.append(fromBlocks(X, Y, Z, T))

    # per-layer frames
    Ps, Qs = [], []
    for s in range(L):
        if s == 0:
            Pcur = P0
            Qcur = (invert_const(r).row_join(gen_rat(r, m, rng)).col_join(
                    sp.zeros(m, r).row_join(Im))) if other_side_frames else sp.eye(r + m)
        elif s == L - 1:
            Pcur = fromBlocks(invert_const(r), sp.zeros(r, m), gen_rat(m, r, rng), Im) \
                   if other_side_frames else sp.eye(r + m)
            Qcur = Qlast
        else:
            Pcur, Qcur = sp.eye(r + m), sp.eye(r + m)
        Ps.append(Pcur)
        Qs.append(Qcur)

    C = [corM + Ps[s] * rawDev[s] * Qs[s] for s in range(L)]
    return dict(C=C, rawDev=rawDev, Ps=Ps, Qs=Qs, r=r, m=m, corM=corM,
                P0=P0, Qlast=Qlast)


# ------- the abstract move machinery (EXACT transcription) -------
def moved_chain(C, L, r, m):
    Ir, Im = sp.eye(r), sp.eye(m)

    def partProd(k):
        P = sp.eye(r + m)
        for s in range(k):
            P = P * C[s]
        return P

    def blockSchur(M):
        return B22(M, r) - B21(M, r) * B11(M, r).inv() * B12(M, r)

    def Kcoup(k):
        return B21(C[k], r) * B11(partProd(k + 1), r).inv() * B12(partProd(k), r)

    def uNorm(s):
        Q = partProd(s)
        return B11(Q, r).inv() * B12(Q, r)

    def vDown(s):
        return B21(C[s], r) * B11(C[s], r).inv()

    def nMix(s):
        return Ir + uNorm(s) * vDown(s)

    def schurTilde(s):
        return (Im - Kcoup(s)) * blockSchur(C[s])

    def upEdit(s):
        return nMix(s).inv() * uNorm(s) * (blockSchur(C[s]) - schurTilde(s))

    # wHatAccum
    def wHat(k):
        W = Im
        for j in range(k):
            W = W * (Im - Kcoup(j)) * schurTilde(j)
        return W

    def hTermLC(j):
        Q = partProd(j)
        return (blockSchur(Q) - wHat(j)) * vDown(j) * nMix(j).inv() * B11(Q, r).inv()

    deltaV0 = sp.zeros(m, r)
    for j in range(L):
        deltaV0 += hTermLC(j)
    Z0edit0 = B21(C[0], r) + deltaV0 * B11(C[0], r)

    def movedZ(s):
        return Z0edit0 if s == 0 else B21(C[s], r)

    def movedY(s):
        return B12(C[s], r) + upEdit(s)

    def movedT(s):
        return schurTilde(s) + movedZ(s) * B11(C[s], r).inv() * movedY(s)

    def movedC(s):
        return fromBlocks(B11(C[s], r), movedY(s), movedZ(s), movedT(s))

    return [movedC(s) for s in range(L)]


def psi_read(inst, L):
    r, m = inst['r'], inst['m']
    corM = inst['corM']
    C = inst['C']
    mC = moved_chain(C, L, r, m)
    reads = []
    for s in range(L):
        D = mC[s] - corM                      # psiTargetD
        if s == 0:
            g = forcedDecodeLeft(inst['P0'], D, r)
        elif s == L - 1:
            g = forcedDecodeRight(inst['Qlast'], D, r)
        else:
            g = D
        reads.append(g)
    return reads


def order_of(expr):
    """Leading eps-order of a scalar rational expr analytic at 0 (or 'ZERO')."""
    expr = sp.simplify(expr)
    if expr == 0:
        return 'ZERO'
    for k in range(0, 7):
        c = sp.simplify(sp.diff(expr, eps, k).subs(eps, 0)) / sp.factorial(k)
        if c != 0:
            return k
    return '>=7'


def coeffs01(M):
    """(c0 matrix, c1 matrix) : eps^0 and eps^1 coefficients entrywise."""
    c0 = M.applyfunc(lambda e: sp.simplify(sp.simplify(e).subs(eps, 0)))
    c1 = M.applyfunc(lambda e: sp.simplify(sp.diff(sp.simplify(e), eps).subs(eps, 0)))
    return c0, c1


def run_case(L, r, m, seed, other_side_frames=False):
    inst = build(L, r, m, seed, other_side_frames=other_side_frames)
    reads = psi_read(inst, L)
    rows = []
    for s in range(L):
        f = reads[s] - inst['rawDev'][s]
        c0, c1 = coeffs01(f)
        c0z = c0 == sp.zeros(*c0.shape)
        c1z = c1 == sp.zeros(*c1.shape)
        # leading order of the whole f (min over entries)
        ords = [order_of(f[i, j]) for i in range(f.rows) for j in range(f.cols)]
        numeric = [o for o in ords if isinstance(o, int)]
        lead = min(numeric) if numeric else 'ZERO'
        pos = 'layer0' if s == 0 else ('LAST' if s == L - 1 else 'interior')
        rows.append((s, pos, c0z, c1z, lead))
    return rows


if __name__ == "__main__":
    print("=" * 92)
    print("TRUE DESIGN (P_last = Q_0 = I ; only P_0 block-lower, Q_last block-upper) :")
    print("  columns: layer s | position | f(0)==0 | Df(0)==0 | leading eps-order of f_s")
    print("=" * 92)
    # Full-symbolic-eps REFERENCE cross-check (slow; nested r x r inverses over layers blow up).
    # Kept small here so it completes; the decisive sweep is boundary_deriv_dual.py (exact
    # value+first-derivative via dual numbers) + boundary_order.py (leading order).
    cases = [(3, 1, 1, 5), (3, 1, 2, 5)]
    allgreen = True
    for (L, r, m, seed) in cases:
        rows = run_case(L, r, m, seed)
        print(f"\nL={L} r={r} m={m} seed={seed}:")
        for (s, pos, c0z, c1z, lead) in rows:
            flag = "" if (c0z and c1z) else "   <<< FIRST-ORDER / VALUE BREAK"
            print(f"   s={s:<2} {pos:<9}  f(0)=0:{str(c0z):<5}  Df(0)=0:{str(c1z):<5}  "
                  f"lead-order:{lead}{flag}")
            if not (c0z and c1z):
                allgreen = False
    print("\n" + "=" * 92)
    print(f"TRUE-DESIGN VERDICT: {'ALL BOUNDARY+INTERIOR FIRST DERIVATIVES ZERO (GREEN)' if allgreen else 'BREAK FOUND'}")
    print("=" * 92)

    # Falsification probe: if the OTHER-side boundary frame were non-trivial, the single-sided
    # forcedDecode should NOT recover the identity read -> a first-order break must appear.
    print("\n" + "=" * 92)
    print("FALSIFICATION PROBE (wrongly make Q_0 and P_last non-trivial):")
    print("  expectation: forcedDecode inverts ONE side only -> boundary Df(0) != 0 (break).")
    print("=" * 92)
    for (L, r, m, seed) in [(3, 1, 2, 5), (4, 1, 2, 11)]:
        rows = run_case(L, r, m, seed, other_side_frames=True)
        print(f"\nL={L} r={r} m={m} seed={seed} [other-side frames ON]:")
        for (s, pos, c0z, c1z, lead) in rows:
            flag = "" if (c0z and c1z) else "   <<< break (EXPECTED at boundary)"
            print(f"   s={s:<2} {pos:<9}  f(0)=0:{str(c0z):<5}  Df(0)=0:{str(c1z):<5}  "
                  f"lead-order:{lead}{flag}")
