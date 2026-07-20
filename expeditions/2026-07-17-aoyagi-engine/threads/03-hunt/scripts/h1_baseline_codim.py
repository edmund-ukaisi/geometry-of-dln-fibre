#!/usr/bin/env python3
"""HUNT h1 -- Tier A baseline (general L) + independent codimension check.

Convention (pinned, exact): for a divisorial valuation v centered at 0 of the
core ideal I = <entries of prod_s C^(s)>, the rlct-candidate is

    rho(v) = A_v / (2 * v(I)),     A_v = log discrepancy,  v(I) = min_g v(g).

KILL the coverage >=-leg iff some v has rho(v) < 1/2 minAdm, i.e.

    2*rho(v) = A_v / v(I) < minAdm    (integer RHS -- the clean kill test).

Tier A: MONOMIAL valuations w in the ORIGINAL entry coordinates. Here A_w = sum w
(smooth ambient, no Jacobian correction), v(I) = min_{ij} ord_w(P_ij),
ord_w(P_ij) = min over contraction paths i->..->j of the summed weights.
Documented VACUOUS in the spec (min 2*rho well above minAdm) -- run broadly as a
pre-filter that would catch a gross transcription error in I or minAdm.

Independent codim check: minAdm is claimed = codim V(I) = min_t Mval(t). We verify
by building an EXACT-rational point in the rank-profile-t stratum and computing the
rank of the Jacobian of the M0*ML equations {P_ij} there (= codim of the component
at a generic/smooth point). If codim < minAdm for some stratum, Watanabe gives
rlct <= 1/2 codim < 1/2 minAdm -- an immediate value kill (via a transcription bug).
"""
import sys, itertools, random
from fractions import Fraction as F
sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/map/battery")
from _minadm import minAdm


# ---------- symbolic matrix product over a weight/exponent semiring ----------

def product_paths(M):
    """Return, for each output entry (i,j) of prod_s C^(s), the list of paths.
    A path is a tuple of (layer s, row, col) entry-indices multiplied together.
    M = (M0,...,ML); layer s (1..L) is an M_{s-1} x M_s matrix C^(s)."""
    L = len(M) - 1
    M0, ML = M[0], M[L]
    paths = {}
    for i in range(M0):
        for j in range(ML):
            # inner indices k_1..k_{L-1}
            inner_ranges = [range(M[s]) for s in range(1, L)]
            plist = []
            for inner in itertools.product(*inner_ranges):
                idx = (i,) + inner + (j,)   # idx[s] is the col of layer s+1 start...
                # entry of layer s (1-based) is (idx[s-1], idx[s])
                path = tuple((s, idx[s - 1], idx[s]) for s in range(1, L + 1))
                plist.append(path)
            paths[(i, j)] = plist
    return paths


def _ratio_of_weights(M, paths, var_list, assign):
    w = dict(zip(var_list, assign))
    tot = sum(assign)
    if tot == 0:
        return None
    ordI = None
    for (ij, plist) in paths.items():
        oe = min(sum(w[e] for e in path) for path in plist)
        ordI = oe if ordI is None else min(ordI, oe)
    if ordI == 0:
        return None
    return F(tot, ordI)


def tierA_min_ratio(M, wmax=2, exhaustive_cap=17, nrand=200000, seed=1):
    """min over original-coordinate monomial valuations of 2*rho = A_w / w(I).
    Exhaustive grid {0..wmax} when #vars <= exhaustive_cap; otherwise a STRUCTURED
    family (single entries, full rows/cols/layers, unit blocks) + a random sample.
    Returns (min_2rho, argmin, mode)."""
    L = len(M) - 1
    paths = product_paths(M)
    var_list = [(s, i, j) for s in range(1, L + 1)
                for i in range(M[s - 1]) for j in range(M[s])]
    nv = len(var_list)
    best = None; best_w = None
    def consider(assign):
        nonlocal best, best_w
        r = _ratio_of_weights(M, paths, var_list, assign)
        if r is not None and (best is None or r < best):
            best, best_w = r, tuple(assign)
    if nv <= exhaustive_cap:
        for assign in itertools.product(range(wmax + 1), repeat=nv):
            consider(assign)
        return best, best_w, "exhaustive"
    # structured family
    idx = {v: k for k, v in enumerate(var_list)}
    def zeros(): return [0] * nv
    # single entries (weight 1,2)
    for k in range(nv):
        for wv in range(1, wmax + 1):
            a = zeros(); a[k] = wv; consider(a)
    # full layer s at weight 1..wmax
    for s in range(1, L + 1):
        for wv in range(1, wmax + 1):
            a = zeros()
            for v in var_list:
                if v[0] == s: a[idx[v]] = wv
            consider(a)
    # full rows / full cols of each layer
    for s in range(1, L + 1):
        for i in range(M[s - 1]):
            a = zeros()
            for j in range(M[s]): a[idx[(s, i, j)]] = 1
            consider(a)
        for j in range(M[s]):
            a = zeros()
            for i in range(M[s - 1]): a[idx[(s, i, j)]] = 1
            consider(a)
    # all-ones and all-ones-two-layers combos
    for s in range(1, L + 1):
        a = zeros()
        for v in var_list:
            if v[0] == s: a[idx[v]] = 1
        consider(a)
    a = [1] * nv; consider(a)
    # random sample
    rng = random.Random(seed)
    for _ in range(nrand):
        a = [rng.randint(0, wmax) for _ in range(nv)]
        consider(a)
    return best, best_w, "structured+random"


# ---------- independent codimension check via exact Jacobian rank ----------

def rand_full_rank(rows, cols, rank, rng, lim=5):
    """Exact-rational rows x cols matrix of exactly `rank` via A = U V, U rows x rank,
    V rank x cols, both generic (full-rank)."""
    while True:
        U = [[F(rng.randint(-lim, lim)) for _ in range(rank)] for _ in range(rows)]
        V = [[F(rng.randint(-lim, lim)) for _ in range(cols)] for _ in range(rank)]
        A = [[sum(U[i][k] * V[k][j] for k in range(rank)) for j in range(cols)] for i in range(rows)]
        if mat_rank(A) == rank:
            return A


def mat_rank(A):
    """Exact rank over Q via Gaussian elimination."""
    A = [row[:] for row in A]
    m = len(A); n = len(A[0]) if m else 0
    r = 0
    for c in range(n):
        piv = next((i for i in range(r, m) if A[i][c] != 0), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = A[r][c]
        A[r] = [x / inv for x in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        r += 1
        if r == m:
            break
    return r


def mval(M, t):
    """Mval(t): (M0-t1)(M1-t1) + sum_{j=2}^L (t_{j-1}-t_j)(M_{j+1}-t_j), t_L=0."""
    L = len(M) - 1
    val = (M[0] - t[0]) * (M[1] - t[0])
    for j in range(2, L + 1):
        tj = t[j - 1] if (j - 1) < L else 0
        tjm1 = t[j - 2]
        val += (tjm1 - tj) * (M[j] - tj)
    return val


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))]
            for i in range(len(A))]


def build_point_in_stratum(M, t, rng):
    """Build C^(1..L) (exact rational) with rank(prod_{s<=j} C) = t_j for j<L, and
    prod over all L = 0 (t_L = 0). Construction: set successive ranks by choosing
    each C^(s) so the running product has the target rank. Simplest: choose the
    running products' ranks via a factorization ladder. Returns list of matrices."""
    L = len(M) - 1
    # target running ranks r_0=M0 (C-independent start is identity-like), r_j after j layers.
    # We want rank(C1..Cj) = t_j (given profile t=(t1,...,tL), t_L=0).
    # Strategy: pick C1 of rank t1; then C2 s.t. rank(C1 C2)=t2 (<= t1); etc.
    r_prev_rows = M[0]
    Cs = []
    # running product P (M0 x M_{s})
    P = [[F(1) if i == j else F(0) for j in range(M[0])] for i in range(M[0])]  # M0 x M0 identity
    ranks = list(t)  # t_1..t_L
    for s in range(1, L + 1):
        rin = M[s - 1]; rout = M[s]
        target = ranks[s - 1]
        # choose C^(s) so that rank(P . C^(s)) = target. P is M0 x M_{s-1}.
        for _ in range(200):
            Cs_s = rand_generic(rin, rout, rng)
            newP = matmul(P, Cs_s)
            if mat_rank(newP) == target:
                Cs.append(Cs_s); P = newP; break
        else:
            # fall back: force via low-rank C^(s)
            Cs_s = rand_full_rank(rin, rout, max(target, 0) if target > 0 else 0, rng) if target > 0 \
                   else [[F(0)] * rout for _ in range(rin)]
            Cs.append(Cs_s); P = matmul(P, Cs_s)
    return Cs


def rand_generic(rows, cols, rng, lim=4):
    return [[F(rng.randint(-lim, lim)) for _ in range(cols)] for _ in range(rows)]


def jac_rank_at(M, Cs):
    """Rank (exact) of the Jacobian of the M0*ML equations {P_ij = (prod C)_ij}
    w.r.t. all N entry variables, evaluated at Cs. = codim of V(I) at Cs (if smooth)."""
    L = len(M) - 1
    var_list = [(s, i, j) for s in range(1, L + 1)
                for i in range(M[s - 1]) for j in range(M[s])]
    # d(P_ab)/d(c^(s)_{ij}) = sum over paths through that entry of the product of the
    # OTHER entries on the path. Compute by: left factor L_s = C1..C^(s-1), right R_s = C^(s+1)..CL.
    # dP/dc^(s)_{ij} has (a,b) entry = L_s[a,i] * R_s[j,b].
    left = {}; right = {}
    # prefix products
    pre = [None] * (L + 2)
    pre[0] = [[F(1) if a == b else F(0) for b in range(M[0])] for a in range(M[0])]  # M0 x M0
    for s in range(1, L + 1):
        pre[s] = matmul(pre[s - 1], Cs[s - 1])   # M0 x M_s
    suf = [None] * (L + 2)
    suf[L + 1] = [[F(1) if a == b else F(0) for b in range(M[L])] for a in range(M[L])]  # ML x ML
    for s in range(L, 0, -1):
        suf[s] = matmul(Cs[s - 1], suf[s + 1])   # M_{s-1} x ML
    # Jacobian rows = equations (a,b); cols = variables (s,i,j)
    rows = []
    for a in range(M[0]):
        for b in range(M[L]):
            row = []
            for (s, i, j) in var_list:
                Lsi = pre[s - 1][a][i]           # C1..C^(s-1) is pre[s-1]: M0 x M_{s-1}
                Rjb = suf[s + 1][j][b]           # C^(s+1)..CL is suf[s+1]: M_s x ML
                row.append(Lsi * Rjb)
            rows.append(row)
    return mat_rank(rows)


if __name__ == "__main__":
    from itertools import product as iproduct
    rng = random.Random(20260717)
    print("=" * 78)
    print("TIER A -- original-coordinate monomial valuation hunt (pre-filter)")
    print("kill iff 2*rho = A_w/w(I) < minAdm")
    print("=" * 78)
    for M in [(2, 2, 2), (2, 2, 1), (2, 2, 3), (3, 3, 4), (2, 2, 2, 2), (2, 3, 2, 2), (4, 4, 4, 4)]:
        wmax = 2
        best, bw, mode = tierA_min_ratio(M, wmax=wmax)
        ma = minAdm(M)
        kill = best < ma
        print(f"M={M}: minAdm={ma}, min 2*rho={best} (rho={best/2}), 1/2 minAdm={F(ma,2)}  "
              f"KILL={kill}  [{mode}]")

    print()
    print("=" * 78)
    print("INDEPENDENT CODIM CHECK -- Jacobian rank at a generic stratum point vs Mval(t)")
    print("(if codim < minAdm anywhere: Watanabe => rlct < 1/2 minAdm, value kill)")
    print("=" * 78)
    for M in [(2, 2, 2), (2, 2, 3), (3, 3, 4), (2, 2, 2, 2), (2, 3, 2, 2)]:
        L = len(M) - 1
        # admissible weakly-decreasing profiles t, t_L=0
        ranges = [range(0, min(M[s], M[s + 1]) + 1) for s in range(L)]
        profs = [t for t in iproduct(*ranges)
                 if t[-1] == 0 and all(t[i] >= t[i + 1] for i in range(L - 1))]
        print(f"\nM={M}: minAdm={minAdm(M)}")
        anymismatch = False
        codims_seen = []
        for t in profs:
            mv = mval(M, t)
            # sample a few points, take the MAX jac rank (generic = smooth codim)
            best_rank = 0
            for _ in range(6):
                Cs = build_point_in_stratum(M, t, rng)
                # confirm product is zero
                P = Cs[0]
                for s in range(1, L):
                    P = matmul(P, Cs[s])
                if any(P[a][b] != 0 for a in range(len(P)) for b in range(len(P[0]))):
                    continue
                jr = jac_rank_at(M, Cs)
                best_rank = max(best_rank, jr)
            codims_seen.append(best_rank)
            ok = (best_rank == mv)
            anymismatch |= (not ok)
            flag = "OK" if ok else "MISMATCH!"
            print(f"   t={t}: Mval={mv}, Jacobian-codim={best_rank}  {flag}")
        mincod = min(codims_seen) if codims_seen else None
        print(f"   -> min Jacobian-codim over strata = {mincod} (claim minAdm={minAdm(M)}); "
              f"{'MATCH' if mincod == minAdm(M) else 'MISMATCH -- POSSIBLE VALUE KILL'}")
