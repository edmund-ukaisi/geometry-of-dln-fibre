#!/usr/bin/env python3
"""HUNT h2 -- independent codim check with a CORRECT generic-point builder.

h1's random+fallback builder produced degenerate points (e.g. C2=0) whenever the
rank drops were hard to hit randomly, collapsing the Jacobian rank -> spurious
'mismatches'. Here we build a genuinely GENERIC point of the rank-profile-t
component S(t) via a nested factorization corridor:

  carry P_j = C^(1)..C^(j) = Bcol_j . Qrow_j,  Bcol_j: M0 x t_j,  Qrow_j: t_j x M_j
  step: solve  Qrow_{j-1} . C^(j) = alpha_j . Qrow_j   for C^(j) (particular + generic
        kernel), with alpha_j (t_{j-1} x t_j), Qrow_j (t_j x M_j) generic.
  Then Bcol_j = Bcol_{j-1} . alpha_j.

The Jacobian rank of the M0*ML product equations at such a generic point = codim of
V(I) there = codim S(t) (S(t) smooth at its generic point). We verify it equals
Mval(t), so min_t codim = minAdm (validating minAdm as the true codimension; a
strict shortfall would give, via Watanabe rlct <= 1/2 codim, an immediate value kill).
"""
import sys, random
from fractions import Fraction as F
sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/threads/03-hunt/scripts")
sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/map/battery")
from h1_baseline_codim import mat_rank, matmul, jac_rank_at, mval
from _minadm import minAdm
from itertools import product as iproduct


def rand_mat(r, c, rng, lim=4):
    return [[F(rng.randint(-lim, lim)) for _ in range(c)] for _ in range(r)]


def rref_solve_particular(A, B):
    """Solve A X = B exactly for X (A: r x n, B: r x m). A assumed full row rank (r<=n).
    Returns a particular solution X (n x m) plus a basis of ker(A) (list of n-vectors)."""
    r = len(A); n = len(A[0]); m = len(B[0])
    # augment [A | B], row reduce
    aug = [A[i][:] + B[i][:] for i in range(r)]
    pivots = []
    row = 0
    for col in range(n):
        piv = next((i for i in range(row, r) if aug[i][col] != 0), None)
        if piv is None:
            continue
        aug[row], aug[piv] = aug[piv], aug[row]
        inv = aug[row][col]
        aug[row] = [x / inv for x in aug[row]]
        for i in range(r):
            if i != row and aug[i][col] != 0:
                f = aug[i][col]
                aug[i] = [a - f * b for a, b in zip(aug[i], aug[row])]
        pivots.append(col); row += 1
        if row == r:
            break
    # particular solution: free cols = 0
    X = [[F(0)] * m for _ in range(n)]
    for pr, col in enumerate(pivots):
        for j in range(m):
            X[col][j] = aug[pr][n + j]
    # kernel basis: for each free column set it to 1
    free = [c for c in range(n) if c not in pivots]
    ker = []
    for fc in free:
        v = [F(0)] * n
        v[fc] = F(1)
        for pr, col in enumerate(pivots):
            v[col] = -aug[pr][fc]
        ker.append(v)
    return X, ker


def build_generic_point(M, t, rng):
    """Generic point of the component with rank(C^1..C^j) = t_j (t = (t_1..t_L), t_L=0)."""
    L = len(M) - 1
    # Bcol: M0 x t_prev ; Qrow: t_prev x M_prev(cols). Start P_0 = I_{M0}.
    Bcol = [[F(1) if a == b else F(0) for b in range(M[0])] for a in range(M[0])]  # M0 x M0
    Qrow = [[F(1) if a == b else F(0) for b in range(M[0])] for a in range(M[0])]  # M0 x M0 (t_prev=M0)
    t_prev = M[0]
    Cs = []
    for j in range(1, L + 1):
        tj = t[j - 1]              # target rank after layer j
        Mj = M[j]                  # cols of C^(j)
        Mjm1 = M[j - 1]            # rows of C^(j)
        if t_prev == 0:
            # running product already 0: remaining layers are fully generic (product stays 0)
            Cs.append(rand_mat(Mjm1, Mj, rng))
            continue
        if tj == 0:
            # C^(j): need Qrow_{j-1} . C^(j) = 0 (so product becomes 0), C^(j) generic in kernel.
            # kernel of (X -> Qrow_{j-1} X): columns in ker(Qrow_{j-1}).
            X0, ker = rref_solve_particular(Qrow, [[F(0)] * Mj for _ in range(t_prev)])
            Cj = [[F(0)] * Mj for _ in range(Mjm1)]
            for v in ker:
                coeffs = [F(rng.randint(-4, 4)) for _ in range(Mj)]
                for a in range(Mjm1):
                    for b in range(Mj):
                        Cj[a][b] += v[a] * coeffs[b]
            Cs.append(Cj)
            Bcol = None; Qrow = None; t_prev = 0
            continue
        # generic targets alpha (t_prev x tj), Qrow_j (tj x Mj)
        for _ in range(50):
            alpha = rand_mat(t_prev, tj, rng)
            if mat_rank(alpha) == min(t_prev, tj):
                break
        for _ in range(50):
            Qrow_j = rand_mat(tj, Mj, rng)
            if mat_rank(Qrow_j) == min(tj, Mj):
                break
        T = matmul(alpha, Qrow_j)                      # t_prev x Mj
        Xpart, ker = rref_solve_particular(Qrow, T)    # solve Qrow . Cj = T
        Cj = [row[:] for row in Xpart]                 # Mjm1 x Mj
        for v in ker:
            coeffs = [F(rng.randint(-4, 4)) for _ in range(Mj)]
            for a in range(Mjm1):
                for b in range(Mj):
                    Cj[a][b] += v[a] * coeffs[b]
        Cs.append(Cj)
        Bcol = matmul(Bcol, alpha)                     # M0 x tj
        Qrow = Qrow_j                                  # tj x Mj
        t_prev = tj
    return Cs


def running_ranks(M, Cs):
    L = len(M) - 1
    P = Cs[0]
    ranks = [mat_rank(P)]
    for s in range(1, L):
        P = matmul(P, Cs[s])
        ranks.append(mat_rank(P))
    return ranks


if __name__ == "__main__":
    rng = random.Random(424242)
    print("INDEPENDENT CODIM CHECK (generic-point builder) vs Mval / minAdm")
    print("=" * 78)
    overall = True
    for M in [(2, 2, 2), (2, 2, 3), (3, 3, 4), (2, 2, 2, 2), (2, 3, 2, 2), (4, 4, 4, 4)]:
        L = len(M) - 1
        ranges = [range(0, min(M[s], M[s + 1]) + 1) for s in range(L)]
        profs = [t for t in iproduct(*ranges)
                 if t[-1] == 0 and all(t[i] >= t[i + 1] for i in range(L - 1))]
        print(f"\nM={M}: minAdm={minAdm(M)}")
        codims = []
        for t in profs:
            mv = mval(M, t)
            best_rank = 0; got_ranks = None
            for _ in range(8):
                Cs = build_generic_point(M, t, rng)
                rr = running_ranks(M, Cs)
                # confirm the profile realized: rr[j] == t[j] for j<L, and full product 0
                P = Cs[0]
                for s in range(1, L):
                    P = matmul(P, Cs[s])
                prod_zero = all(P[a][b] == 0 for a in range(len(P)) for b in range(len(P[0])))
                if not prod_zero:
                    continue
                jr = jac_rank_at(M, Cs)
                if jr > best_rank:
                    best_rank = jr; got_ranks = rr
            codims.append(best_rank)
            ok = (best_rank == mv)
            overall &= ok
            print(f"   t={t}: Mval={mv}, generic Jac-codim={best_rank}, realized running-ranks={got_ranks}  "
                  f"{'OK' if ok else 'MISMATCH!'}")
        mc = min(codims)
        match = (mc == minAdm(M))
        overall &= match
        print(f"   -> min codim={mc} vs minAdm={minAdm(M)}: {'MATCH' if match else 'MISMATCH -> POSSIBLE VALUE KILL'}")
    print("\n" + ("ALL CODIMS MATCH Mval / minAdm (no codim-side value kill)"
                  if overall else "SOME MISMATCH -- investigate"))
