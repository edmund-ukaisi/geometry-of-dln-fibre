"""
INDEPENDENT verification of Codex's rank-stratification lemma for the shifted
zero-product variety Z(e) = { B : B_N..B_1 = 0 } on dim vector e = (e_0,...,e_N).

Codex's claim (the proof of (R) = generic smoothness of each top component):
  Strata indexed by prefix-rank sequences r = (r_0,...,r_N), r_0 = e_0, r_N = 0,
  with feasibility r_i <= min(e_i, r_{i-1}) and r_i >= r_{i-1} - (e_{i-1} - 0)... we
  enumerate all non-increasing-by-feasibility chains.
  - stratum codim:        c(r)   = sum_{i=1}^N (r_{i-1} - r_i)(e_i - r_i)
  - generic Jacobian rank: J(r)  = sum_{i=1}^N (r_{i-1} - r_i) * min_{j>=i}(e_j - r_j)
                                   with the convention e_N - r_N = e_N (r_N = 0).
  Claim A: min_r c(r) = C_sh  (the QIP/cValue codim of the top component).
  Claim B: the minimizers r are exactly the theta = C(m,|qd|) top components.
  Claim C: at every minimizer, J(r) = c(r) (generic smoothness => rank = codim).
  Claim D (the crux): at non-minimizers J(r) can EXCEED c(r)? No -- J(r) <= c(r)
           always (tangent >= dim), and = c(r) iff the stratum is generically
           smooth; the claim is that MINIMIZERS are always smooth.

We cross-check Claim A/B/C against the exact QIP engine (C_sh, theta) for many e.
"""
import sys
from itertools import product

sys.path.insert(0, "/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/theta-components/expeditions/2026-06-25-theta-components/threads/14-rank-witness/scripts")
from qip import cValue, cTheta, sorted_asc  # noqa: E402


def feasible_chains(e):
    """all r=(r_0..r_N), r_0=e_0, r_N=0, with 0<=r_i<=min(e_i, r_{i-1})."""
    N = len(e) - 1
    out = []
    # r_i in [0, min(e_i, r_{i-1})]
    def rec(i, prefix):
        if i == N:
            if prefix[-1] >= 0:  # r_{N-1} given; r_N must be 0 and feasible: 0<=min(e_N,r_{N-1}) ok
                out.append(tuple(prefix) + (0,))
            return
        hi = min(e[i], prefix[-1])
        for v in range(0, hi + 1):
            rec(i + 1, prefix + [v])
    rec(1, [e[0]])
    # keep only chains with r_N feasible: r_N=0 <= min(e_N, r_{N-1}) always true
    return out


def c_codim(e, r):
    N = len(e) - 1
    return sum((r[i - 1] - r[i]) * (e[i] - r[i]) for i in range(1, N + 1))


def jac_rank(e, r):
    N = len(e) - 1
    tot = 0
    for i in range(1, N + 1):
        drop = r[i - 1] - r[i]
        if drop == 0:
            continue
        # min_{j>=i} (e_j - r_j); for j=N use e_N - 0 = e_N
        suffix_min = min((e[j] - r[j]) for j in range(i, N + 1))
        tot += drop * suffix_min
    return tot


def analyze(e):
    e = list(e)
    N = len(e) - 1
    chains = feasible_chains(e)
    cs = [(r, c_codim(e, r), jac_rank(e, r)) for r in chains]
    minc = min(c for _, c, _ in cs)
    mins = [(r, c, j) for r, c, j in cs if c == minc]
    Csh = cValue(sorted_asc(e))
    theta = cTheta(sorted_asc(e))
    # checks
    A = (minc == Csh)
    B = (len(mins) == theta)
    C = all(j == c for _, c, j in mins)           # at minimizers, rank == codim (smooth)
    D = all(j <= c for _, c, j in cs)             # universal tangent bound rank <= codim
    return dict(e=e, minc=minc, Csh=Csh, theta=theta, nmin=len(mins),
                A=A, B=B, C=C, D=D, mins=mins, all=cs)


if __name__ == "__main__":
    # shifted vectors arising in our cases + a broad sweep
    explicit = [
        [1,1,1],[1,1,1,1],[2,2,2],[1,2,2],          # from r>0 fibres / r=0
        [2,2,2,2,2],[1,2,3],[2,2,3],[1,2,2,2],[1,2,2,3],
        [2,2,2,2,2,2],[1,2,1],[2,2,2,2],
    ]
    print("=== explicit shifted vectors (cross-check A,B,C,D) ===")
    bad = []
    for e in explicit:
        res = analyze(e)
        ok = res['A'] and res['B'] and res['C'] and res['D']
        if not ok:
            bad.append(res)
        print(f"  e={str(e):<16} minc={res['minc']} Csh={res['Csh']} (A={res['A']})  "
              f"#min={res['nmin']} theta={res['theta']} (B={res['B']})  rank==codim@min C={res['C']}  rank<=codim D={res['D']}")
    print()
    # broad sweep
    print("=== broad sweep: all e of length 3..6, entries 0..4 (e_0>=1) ===")
    cntA = cntB = cntC = cntD = 0; tot = 0; fails = []
    for L in range(3, 7):
        for e in product(range(0, 5), repeat=L):
            if e[0] < 1:
                continue
            e = list(e)
            if all(x == 0 for x in e):
                continue
            res = analyze(e)
            tot += 1
            cntA += res['A']; cntB += res['B']; cntC += res['C']; cntD += res['D']
            if not (res['A'] and res['B'] and res['C'] and res['D']):
                fails.append((e, res['A'], res['B'], res['C'], res['D'], res['minc'], res['Csh'], res['nmin'], res['theta']))
    print(f"  total e checked: {tot}")
    print(f"  A (min c = C_sh):           {cntA}/{tot}")
    print(f"  B (#minimizers = theta):    {cntB}/{tot}")
    print(f"  C (rank==codim at minim.):  {cntC}/{tot}")
    print(f"  D (rank<=codim universally):{cntD}/{tot}")
    if fails:
        print(f"  FAILURES ({len(fails)}):")
        for f in fails[:30]:
            print("    ", f)
    else:
        print("  NO FAILURES -- Codex's stratification lemma holds on the entire sweep.")
