"""
Self-contained QIP / cValue / cTheta engine (mirrors Core.CThetaValue),
operating on a weakly-INCREASING reordering of the dimension vector.

C(d), theta(d), delta(d) are computed from the SORTED-ascending vector
(the order-sensitive prefix data qipM/qipS read d through its sorted form;
(C, theta) are permutation invariant -- proved Cor 5.10 -- so we sort).

For the fibre with target rank r, the relevant codim/component data lives on the
SHIFTED vector  dsh = (d_0 - r, ..., d_N - r).

Conventions match expeditions/2026-06-23-fibre-codim/aoyagi_check.py.
"""
from fractions import Fraction as F

def _qipA(M, l):
    N = len(M) - 1
    s = sum(M[i] for i in range(min(l, N) + 1))
    return s - l * M[min(l, N)]

def qipM(M):
    """greatest l in 0..N with A_l >= 0."""
    N = len(M) - 1
    best = 0
    for l in range(0, N + 1):
        if _qipA(M, l) >= 0:
            best = l
    return best

def qipS(M):
    m = qipM(M); N = len(M) - 1
    return sum(M[min(i, N)] for i in range(m + 1))

def qipRound(M):
    m = qipM(M); S = qipS(M)
    return (2 * S + m) // (2 * m)

def qipDelta(M):
    m = qipM(M); S = qipS(M); a = qipRound(M)
    return S - m * a

def cValue(M):
    """C = combinatorial codim of the zero-product (r=0) / shifted problem on M."""
    m = qipM(M); S = qipS(M); a = qipRound(M); dd = qipDelta(M); N = len(M) - 1
    d0 = M[0]
    pref = sum((M[min(i, N)] - d0) ** 2 for i in range(1, m + 1))
    num = d0 ** 2 - pref + m * (a - d0) ** 2 + 2 * (a - d0) * dd + abs(dd)
    assert num % 2 == 0, ("cValue num odd", M, num)
    return num // 2

def cTheta(M):
    from math import comb
    return comb(qipM(M), abs(qipDelta(M)))

def shifted(d, r):
    return [x - r for x in d]

def sorted_asc(v):
    return sorted(v)

def fibre_data(d, r):
    """Return the load-bearing integers for the fibre mult^{-1}(E_r) over dim vec d.
       delta   = r*(d_0 + d_N - r)             (endpoint determinantal codim)
       C_sh    = cValue(sorted shifted vector)  (shifted zero-product codim)
       Q       = delta + C_sh                    (= C + delta, the fibre codim)
       theta   = cTheta(sorted shifted vector)   (# top components)
    """
    d0, dN = d[0], d[-1]
    delta = r * (d0 + dN - r)
    dsh = sorted_asc(shifted(d, r))
    Csh = cValue(dsh)
    theta = cTheta(dsh)
    return dict(delta=delta, Csh=Csh, Q=delta + Csh, theta=theta,
                dsh_sorted=dsh, m=qipM(dsh), qdelta=qipDelta(dsh))

if __name__ == "__main__":
    # cross-check against thread-13's four cases + the boundary cases
    cases = [
        ([2,2,2], 1), ([2,2,2,2], 1), ([3,3,3], 2), ([2,2,2,2,2], 0),
        ([3,3,3], 1), ([3,2,3], 1),
        ([3,2,4], 1), ([4,2,3], 1), ([3,2,3], 0), ([4,4,4,4], 2),
        ([2,3,2], 1),
    ]
    print(f"{'d':<16}{'r':<3}{'delta':<7}{'C_sh':<6}{'Q':<5}{'theta':<7}{'m':<4}{'qdelta':<8}{'dsh_sorted'}")
    for d, r in cases:
        fd = fibre_data(d, r)
        print(f"{str(d):<16}{r:<3}{fd['delta']:<7}{fd['Csh']:<6}{fd['Q']:<5}{fd['theta']:<7}{fd['m']:<4}{fd['qdelta']:<8}{fd['dsh_sorted']}")
