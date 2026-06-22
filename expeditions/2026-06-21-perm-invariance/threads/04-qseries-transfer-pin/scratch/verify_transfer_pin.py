"""Thread 04 — PIN the PEEL local transfer identity from elementary q-series primitives.

The transfer identity (thread 03 §4, load-bearing inside PEEL / Thm 5.6):

  P_{d_N} * prod_{i<N} P_{b_i}  =  sum_x q^{Delta_b(x)} P_{x_N} prod_{i<N} (P_{b_i-x_i} P_{x_i})

  sum over x=(x_0,..,x_{N-1},x_N), 0<=x_i<=b_i (i<N), x_N>=0, sum_i x_i = d_N,
  Delta_b(x) = sum_{0<=a<u<=N} (b_a - x_a) x_u, with b_N := 0.

Thread 03 EXACT-VERIFIED the endpoint. This script PINS the clean DECOMPOSITION, proving it from
ONE classical primitive (the N=1 Durfee identity) by a peel-first induction on the number of blocks N.
Every intermediate identity is exact-verified, not just the endpoint.

THE DECOMPOSITION (corrected — q-Vandermonde / Gaussian binomials are NOT needed):

  PRIMITIVE (the only classical input):  N=1 Durfee identity
     (D)   P_a P_b = sum_{r=0}^{min(a,b)} q^{(a-r)(b-r)} P_{a-r} P_r P_{b-r}.

  STEP 1 (exponent split, pure arithmetic — no q-series):
     (E)   Delta_b(x) = (b_0 - x_0)(d_N - x_0) + Delta'_{b'}(x_1,..,x_{N-1},x_N),
           where b' = (b_1,..,b_{N-1}) (re-based to indices 0..N-2, b'_{N-1}:=0),
           Delta' is the SAME functional on the dropped-first-index tuple,
           and d_N - x_0 = sum_{i>=1} x_i is the target of the sub-transfer.

  STEP 2 (peel-first recursion, from (E) + reindexing the sum):
     (R)   RHS_T(b_0,b_1..b_{N-1}; d) =
              sum_{x_0=0}^{b_0} q^{(b_0-x_0)(d-x_0)} P_{b_0-x_0} P_{x_0} * RHS_T(b_1..b_{N-1}; d-x_0).

  STEP 3 (induction on N): base N=0 is RHS_T(();d) = P_d (single term x_N=d, Delta=0).
     Inductive step: substitute IH  RHS_T(b_1..b_{N-1}; m) = P_m * prod_{i>=1} P_{b_i}  into (R):
        RHS_T(b;d) = (prod_{i>=1} P_{b_i}) * sum_{x_0} q^{(b_0-x_0)(d-x_0)} P_{d-x_0} P_{x_0} P_{b_0-x_0}
                   = (prod_{i>=1} P_{b_i}) * (P_d P_{b_0})      <- this inner sum IS (D) with a=d,b=b_0,r=x_0
                   = P_d * prod_{i>=0} P_{b_i}.                  QED.

So the transfer = N nested applications of (D), glued by the arithmetic split (E). The N=1 transfer
is (D) verbatim.
"""
import sys, os, random
from itertools import product as iproduct
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "03-qseries-route", "scratch"))
from qseries import P_s, pmul, padd, trunc, PREC, pscale_shift


def P_block(vals):
    res = [1] + [0] * (PREC - 1)
    for v in vals:
        res = pmul(res, P_s(v))
    return res


def delta_b(N, b, x):
    """Delta_b(x) = sum_{0<=a<u<=N} (b_a - x_a) x_u, b indexed 0..N-1 (b_N := 0), x indexed 0..N."""
    bb = {i: b[i] for i in range(N)}
    bb[N] = 0
    return sum((bb[a] - x[a]) * x[u] for a in range(N + 1) for u in range(a + 1, N + 1))


def transfer_lhs(b, dN):
    """P_{dN} prod_{i<N} P_{b_i}."""
    return trunc(pmul(P_s(dN), P_block(b)))


def transfer_rhs(b, dN):
    """sum_x q^{Delta} P_{x_N} prod_{i<N}(P_{b_i-x_i} P_{x_i})."""
    N = len(b)
    acc = [0] * PREC
    for xs in iproduct(*[range(bi + 1) for bi in b]):
        xN = dN - sum(xs)
        if xN < 0:
            continue
        x = {i: xs[i] for i in range(N)}
        x[N] = xN
        db = delta_b(N, b, x)
        term = pmul(P_s(xN), P_block([b[i] - xs[i] for i in range(N)] + list(xs)))
        acc = padd(acc, pscale_shift(term, 1, db))
    return trunc(acc)


# ----------------------------------------------------------------------------
# (D)  N=1 Durfee identity  P_a P_b = sum_r q^{(a-r)(b-r)} P_{a-r} P_r P_{b-r}
# ----------------------------------------------------------------------------
def durfee_rhs(a, b):
    acc = [0] * PREC
    for r in range(0, min(a, b) + 1):
        term = pmul(pmul(P_s(a - r), P_s(r)), P_s(b - r))
        acc = padd(acc, pscale_shift(term, 1, (a - r) * (b - r)))
    return trunc(acc)


def check_durfee(rng=9):
    fails = 0
    for a in range(rng):
        for b in range(rng):
            if trunc(pmul(P_s(a), P_s(b))) != durfee_rhs(a, b):
                fails += 1
    print(f"(D) N=1 Durfee identity, a,b in 0..{rng-1}: ", "OK" if fails == 0 else f"{fails} FAIL")
    return fails


# ----------------------------------------------------------------------------
# (E)  Exponent split (pure arithmetic): Delta = (b0-x0)(d-x0) + Delta'
# ----------------------------------------------------------------------------
def check_exponent_split_symbolic(maxN=6):
    """(E) as a POLYNOMIAL identity in indeterminate b_i, x_i (sympy expand == 0)."""
    try:
        import sympy as sp
    except ImportError:
        print("(E) symbolic: sympy unavailable — skipped (numeric check still runs)")
        return 0
    fails = 0
    for N in range(1, maxN + 1):
        b = sp.symbols(f"b0:{N}")
        x = sp.symbols(f"x0:{N + 1}")
        bb = list(b) + [sp.Integer(0)]
        d = sum(x)
        full = sum((bb[a] - x[a]) * x[u] for a in range(N + 1) for u in range(a + 1, N + 1))
        deltap = sum((bb[a] - x[a]) * x[u] for a in range(1, N + 1) for u in range(a + 1, N + 1))
        rhs = (b[0] - x[0]) * (d - x[0]) + deltap
        if sp.expand(full - rhs) != 0:
            fails += 1
            print(f"   symbolic split FAIL N={N}")
    print(f"(E) symbolic polynomial identity, N=1..{maxN}: ", "OK" if fails == 0 else f"{fails} FAIL")
    return fails


def check_exponent_split(trials=300000, maxb=5, maxxN=5):
    fails = 0
    for _ in range(trials):
        N = random.randint(1, 5)
        b = [random.randint(0, maxb) for _ in range(N)]
        x = {i: random.randint(0, b[i]) for i in range(N)}
        x[N] = random.randint(0, maxxN)
        d = sum(x[i] for i in range(N + 1))
        full = delta_b(N, b, x)
        # Delta' : drop index 0; same functional on indices 1..N
        bb = {i: b[i] for i in range(N)}
        bb[N] = 0
        deltap = sum((bb[a] - x[a]) * x[u] for a in range(1, N + 1) for u in range(a + 1, N + 1))
        split = (b[0] - x[0]) * (d - x[0]) + deltap
        if full != split:
            fails += 1
            if fails <= 5:
                print("   split FAIL", b, x, full, split)
    print(f"(E) exponent split  Delta=(b0-x0)(d-x0)+Delta'  ({trials} random): ",
          "OK" if fails == 0 else f"{fails} FAIL")
    return fails


# ----------------------------------------------------------------------------
# (R)  Peel-first recursion (q-series), and the FULL inductive reconstruction.
# ----------------------------------------------------------------------------
def peel_first(b, d):
    """RHS via one peel of x_0, sub-transfer computed independently (tests (R) as identity)."""
    N = len(b)
    if N == 0:
        return trunc(P_s(d))            # base: RHS_T((); d) = P_d
    b0 = b[0]
    acc = [0] * PREC
    for x0 in range(0, b0 + 1):
        if d - x0 < 0:
            continue
        sub = transfer_rhs(b[1:], d - x0)
        term = pmul(pmul(P_s(b0 - x0), P_s(x0)), sub)
        acc = padd(acc, pscale_shift(term, 1, (b0 - x0) * (d - x0)))
    return trunc(acc)


def induct_full(b, d):
    """Full induction: RHS_T built ENTIRELY from (R)+base, recursively (no transfer_rhs call)."""
    N = len(b)
    if N == 0:
        return trunc(P_s(d))
    b0 = b[0]
    acc = [0] * PREC
    for x0 in range(0, b0 + 1):
        if d - x0 < 0:
            continue
        sub = induct_full(b[1:], d - x0)
        term = pmul(pmul(P_s(b0 - x0), P_s(x0)), sub)
        acc = padd(acc, pscale_shift(term, 1, (b0 - x0) * (d - x0)))
    return trunc(acc)


def peel_with_IH(b, d):
    """Inductive step with IH substituted literally: sub = P_{d-x0} prod_{i>=1}P_{b_i}.
    Verifies the step collapses to LHS via the inner Durfee sum."""
    N = len(b)
    if N == 0:
        return trunc(P_s(d))
    b0 = b[0]
    acc = [0] * PREC
    for x0 in range(0, b0 + 1):
        if d - x0 < 0:
            continue
        subLHS = pmul(P_s(d - x0), P_block(b[1:]))    # IH
        term = pmul(pmul(P_s(b0 - x0), P_s(x0)), subLHS)
        acc = padd(acc, pscale_shift(term, 1, (b0 - x0) * (d - x0)))
    return trunc(acc)


# ----------------------------------------------------------------------------
# STAGED form (Codex's decorrelated derivation — the recommended Lean target).
#   running residual s_0=d, s_{j+1}=s_j-x_j; admissible x_j in 0..min(s_j,b_j);
#   partial exponent E_m = sum_{j<m}(b_j-x_j)s_{j+1}; terminal x_N := s_N.
#   Single induction on m (#processed blocks), invariant claim closes by ONE Durfee per step.
# ----------------------------------------------------------------------------
def rhs_staged(b, d):
    """Transfer RHS built via the staged single-induction-on-m recursion (one Durfee per block)."""
    N = len(b)
    acc = [0] * PREC

    def rec(j, s, xs, E):
        if j == N:
            term = pmul(P_s(s), P_block([b[i] - xs[i] for i in range(N)] + xs))  # P_{s_N}=P_{x_N}
            acc[:] = padd(acc, pscale_shift(term, 1, E))
            return
        for xj in range(0, min(s, b[j]) + 1):           # x_j <= min(s_j, b_j)
            rec(j + 1, s - xj, xs + [xj], E + (b[j] - xj) * (s - xj))
        # exponent increment (b_j - x_j) s_{j+1} = (b_j-x_j)(s_j-x_j): Durfee a=s_j,b=b_j,r=x_j
    rec(0, d, [], 0)
    return trunc(acc)


def flat_tuples(b, d):
    out = set()
    for xs in iproduct(*[range(bi + 1) for bi in b]):
        xN = d - sum(xs)
        if xN < 0:
            continue
        out.add(tuple(list(xs) + [xN]))
    return out


def staged_tuples(b, d):
    N = len(b)
    out = set()

    def rec(j, s, xs):
        if j == N:
            out.add(tuple(xs + [s]))
            return
        for xj in range(0, min(s, b[j]) + 1):
            rec(j + 1, s - xj, xs + [xj])
    rec(0, d, [])
    return out


def check_staged_equiv(tests):
    """The flagged subtle step: staged index set (x_j<=min(s_j,b_j)) == flat index set (x_j<=b_j),
    because s_j = sum_{u>=j} x_u >= x_j is automatic given sum x = d. Verified as q-series AND as
    sets of tuples (so the x_j<=s_j cap adds nothing)."""
    print("=== staged (Codex) form: equals flat, the x_j<=s_j cap is automatic ===")
    fq = ft = 0
    for b, d in tests:
        if rhs_staged(b, d) != transfer_rhs(b, d):
            fq += 1
            print(f"   q-series DIFFER b={b} d={d}")
        if staged_tuples(b, d) != flat_tuples(b, d):
            ft += 1
            print(f"   tuple-set DIFFER b={b} d={d}")
    print("  staged==flat (q-series): ", "OK" if fq == 0 else f"{fq} FAIL")
    print("  staged index set == flat index set (cap automatic): ",
          "OK" if ft == 0 else f"{ft} FAIL")
    return fq + ft


def check_chain(tests):
    print("=== full chain (each link exact) ===")
    f = 0
    for b, d in tests:
        L = transfer_lhs(b, d)
        R = transfer_rhs(b, d)
        pr = peel_first(b, d)
        iw = peel_with_IH(b, d)
        ind = induct_full(b, d)
        link = {
            "LHS==RHS (endpoint, reconfirm)": L == R,
            "(R) RHS==peel_first": R == pr,
            "(IH-step) peel_with_IH==LHS": iw == L,
            "(induction) induct_full==LHS": ind == L,
        }
        for k, ok in link.items():
            if not ok:
                f += 1
                print(f"   FAIL b={b} d={d}: {k}")
    print("  all links: ", "OK" if f == 0 else f"{f} FAIL")
    return f


if __name__ == "__main__":
    # broad family: monotone, non-monotone, wide, multiple N, zeros, equal blocks
    tests = [
        ((1,), 2), ((2, 1), 2), ((1, 2), 3), ((2, 2), 2), ((1, 1, 1), 2), ((2, 1, 3), 2),
        ((0, 2), 2), ((3,), 3), ((4, 1, 2), 5), ((1, 4, 2, 3), 6), ((3, 0, 2), 4), ((5,), 5),
        ((2, 3, 1, 4), 7), ((0, 0, 3), 3), ((4, 4), 8), ((2, 1, 3), 5), ((1, 4, 2), 6),
        ((2, 2), 3), ((3, 1), 4), ((1, 2, 3), 4), ((2, 1, 3, 2), 6), ((4,), 4), ((0, 3, 1), 5),
        ((5, 5), 10), ((1, 1, 1, 1), 3), ((6, 5, 5), 8), ((3, 3, 3), 4), ((1, 0, 2, 0, 3), 5),
    ]
    total = 0
    total += check_durfee()
    total += check_exponent_split_symbolic()
    total += check_exponent_split()
    total += check_chain(tests)
    total += check_staged_equiv(tests)
    print()
    print("TRANSFER PIN CERTIFIED — transfer = iterated N=1 Durfee (D) via arithmetic split (E);\n"
          "  peel-first and Codex staged-induction forms both reconstruct the LHS exactly."
          if total == 0 else f"{total} FAILS")
