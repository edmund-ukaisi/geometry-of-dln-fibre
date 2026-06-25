"""Route-B evidence: Aoyagi's own Definition-3 ℓ (`paperEll`) recovers the same λ as the
LR surrogate `ell = qipM`. Reproducible from a clean checkout (reads the committed sibling
`aoyagi_check.py` for the shared engine). Run: `python3 paperell_check.py`.

Findings (all 0 violations across ~3000 monotone shifted-width vectors):
  (a) qipA(M,·) = 0 strictly between paperEll and qipM            (the zero-run structure)
  (b) paperLambdaCore(paperEll) == lambdaCore(qipM)               (the step-invariance => paperLambda = lambda)
  (c) paperEll is the UNIQUE solution of Aoyagi's Definition-3 conditions (corrected (ℓ-1)->ℓ)
  (d) paperEll == the corrected-Definition-3 selection search
"""
import itertools, os
from fractions import Fraction as F

_here = os.path.dirname(os.path.abspath(__file__))
exec(open(os.path.join(_here, 'aoyagi_check.py')).read().split('# ---- enumerate')[0])


def paperEll(M):
    """Aoyagi's ell = greatest l<=N with qipA(M,l) >= 1 (last index where the active threshold is strict)."""
    N = len(M) - 1
    best = None
    for l in range(0, N + 1):
        if qipA(M, l) >= 1:
            best = l
    return best


def core_with_ell(M, ell, S):
    """The displayed Aoyagi core (lambdaCore) evaluated at an arbitrary cutoff ell, active sum S."""
    aw = [M[k] for k in range(ell + 1)]
    ceilM = (S + ell - 1) // ell
    a = S - (ceilM - 1) * ell
    pairsum = sum(aw[i] * aw[j] for i in range(ell + 1) for j in range(i + 1, ell + 1))
    return F(a * (ell - a), 4 * ell) - F(ell * (ell - 1), 4) * F(S, ell) ** 2 + F(1, 2) * pairsum


def IsAoyagiEll(M, l):
    """Aoyagi Definition 3 (corrected (ℓ-1)->ℓ), reduced to its binding inequalities via sortedness:
       active: qipA(M,l) >= 1   (T_l > l*M_l) ;  inactive: qipA(M,l+1) <= 0  (T_l <= l*M_{l+1})."""
    N = len(M) - 1
    return qipA(M, l) >= 1 and (l == N or qipA(M, l + 1) <= 0)


def aoyagi_ell_corrected(M):
    """Direct search of corrected Definition 3 over active-set sizes."""
    N = len(M) - 1
    cands = []
    for ell in range(1, N + 1):
        T = sum(M[k] for k in range(ell + 1))
        if (T > ell * M[ell]) and (ell == N or T <= ell * M[ell + 1]):
            cands.append(ell)
    return cands


def main():
    bad_zero = bad_lambda = bad_is = bad_uniq = bad_d3 = 0
    checked = 0
    for N1 in range(2, 7):
        for tup in itertools.combinations_with_replacement(range(0, 9), N1):
            M = list(tup)
            if M[0] < 1 or qipM_(M) < 1:
                continue
            checked += 1
            m = qipM_(M)
            pe = paperEll(M)
            if any(qipA(M, j) != 0 for j in range(pe + 1, m + 1)):
                bad_zero += 1
            Spe = sum(M[k] for k in range(pe + 1))
            if core_with_ell(M, pe, Spe) != core_with_ell(M, m, qipS_(M)):
                bad_lambda += 1
            if not IsAoyagiEll(M, pe):
                bad_is += 1
            if [l for l in range(len(M)) if IsAoyagiEll(M, l)] != [pe]:
                bad_uniq += 1
            if aoyagi_ell_corrected(M) != [pe]:
                bad_d3 += 1
    print(f"checked {checked} monotone shifted-width vectors")
    print(f"(a) qipA==0 between paperEll..qipM           : {bad_zero} violations")
    print(f"(b) paperLambdaCore == lambdaCore (invariance): {bad_lambda} violations")
    print(f"(c) paperEll satisfies+unique IsAoyagiEll     : {bad_is}/{bad_uniq} violations")
    print(f"(d) paperEll == corrected-Def-3 search        : {bad_d3} mismatches")


if __name__ == "__main__":
    main()
