"""
F₂ +γ-PAIRED regime — the last verification of the arc (elder condition (c)).

§7 fired ⟹ F₂ adopted: the deeper recoord returns to +γ (Q₁⁻¹, product-preserving), plus the Q₂⁻¹ input
compensator, plus the paired Q₁·A₀·Q₂ clearing (= diag(1,e₂), do-not-zero-but-absorb). The ideal-close /
census-0 is settled (rows A/D, product-preserving). This re-checks, on the FINAL +γ-paired object, the OTHER
two criteria that had only been verified under §8(m)'s −γ:
  (b) the CLEAN MULTILINEAR block / boostReady (Deg1SupportedOn center) — sign-robust? re-confirm under +γ.
  (c) SCOPE subsumption: does the paired Q₁·A₀ clearing (which zeroes the outer pivot rows) make the
      i≥cleared bound REDUNDANT (a later edge reads an earlier CLEARED row as 0 anyway), or is it still needed?
Witnesses (2,3,2)/(2,3,2,2) + (2,2,2,2).
"""
import sympy as sp


def make(d):
    N = len(d) - 1
    return N, {(L, r, c): sp.Symbol(f"u{L}{r}{c}") for L in range(N) for r in range(d[L + 1]) for c in range(d[L])}


def rd(u, d, S, row, col):
    N = len(d) - 1
    return u[(S, row, col)] if (0 <= S < N and 0 <= row < d[S + 1] and 0 <= col < d[S]) else sp.Integer(0)


def shear(u, d, sL, sC, piv, sign, scoped):
    """Paired clear (A_S pivot row+col -> 0, interior Schur) + branch-ii recoord(sign, scope)."""
    a, b = piv[1], piv[2]
    w = dict(u)
    for (L, r, c) in u:
        if L == sL and sC <= r and sC <= c:
            if r != a and c != b:
                w[(L, r, c)] = u[(L, r, c)] - rd(u, d, sL, r, b) * rd(u, d, sL, a, c)
            elif (r, c) != (a, b):
                w[(L, r, c)] = sp.Integer(0)                       # paired clearing (Q1·A0·Q2 -> diag)
        elif L == sL + 1 and c == a:
            lo = sC if scoped else 0
            w[(L, r, c)] = u[(L, r, c)] + sign * sum(
                (rd(u, d, sL, i, b) * rd(u, d, sL + 1, r, i) for i in range(lo, d[sL + 1]) if i != c), sp.Integer(0))
    return w


def apply_edge(u, d, case, sL, sC, piv, cen, delta, sign, scoped):
    w = dict(u) if case in ("case11", "rollover") else shear(u, d, sL, sC, piv, sign, scoped)
    out = {}
    for k in u:
        if case == "rollover":
            out[k] = w[k]
        elif delta == 1:
            out[k] = sp.Integer(1) if k == piv else w[k]
        else:
            out[k] = (w[piv] if k == piv else (w[piv] * w[k] if k in cen else w[k]))
    return out


def coreGen(u, d):
    N = len(d) - 1
    P = sp.Matrix(d[N], d[N - 1], lambda r, c: u[(N - 1, r, c)])
    for L in range(N - 2, -1, -1):
        P = P * sp.Matrix(d[L + 1], d[L], lambda r, c: u[(L, r, c)])
    return [sp.expand(P[i, j]) for i in range(P.rows) for j in range(P.cols)]


def foldtuple(d, edges, sign, scoped):
    N, u = make(d)
    v = dict(u)
    for e in reversed(edges):
        v = apply_edge(v, d, *e, sign, scoped)
    return N, u, v


def maxdeg(f, xs):
    xs = [x for x in xs if x in f.free_symbols]
    return 0 if not xs else max(sum(m) for m in sp.Poly(sp.expand(f), *xs).monoms())


def check(d, edges, label):
    print("=" * 82)
    print(f"{label}: d={d}")
    N, u0 = make(d)
    u001, u010 = u0[(0, 0, 1)], u0[(0, 1, 0)]
    # (b) block-form under +γ (F₂), scoped: E_J clean + D_J multilinear (deg≤1 per pivot-row/col coord)
    v = foldtuple(d, edges, +1, True)[2]
    ents = coreGen(v, d)
    wr = max(maxdeg(f, [u001]) for f in ents); wc = max(maxdeg(f, [u010]) for f in ents)
    print(f"  (b) F₂ +γ SCOPED block-form: max deg_u001={wr}, deg_u010={wc}  => MULTILINEAR: {wr<=1 and wc<=1}")
    # chart-frame boostReady: L0 clean cleared block + residual = A₂·L1·L0 Deg1 on center
    L0 = sp.Matrix(d[1], d[0], lambda r, c: sp.expand(v[(0, r, c)]))
    diagok = (L0[0, 0] == 1 and all(L0[0, c] == 0 for c in range(1, d[0])) and
              all(L0[r, 0] == 0 for r in range(1, d[1])))
    print(f"      L0 = clean cleared block (pivot row/col zeroed, diag-shaped): {diagok}")
    # (c) SCOPE subsumption: does UNSCOPED +γ (paired) already avoid u001^2 (paired clearing zeroes outer rows)?
    vun = foldtuple(d, edges, +1, False)[2]
    entun = coreGen(vun, d)
    wr_un = max(maxdeg(f, [u001]) for f in entun)
    print(f"  (c) F₂ +γ UNSCOPED block-form: max deg_u001={wr_un}  => "
          f"{'scope SUBSUMED (paired clear zeroes outer rows, no u001^2 even unscoped)' if wr_un<=1 else 'scope STILL NEEDED (u001^2 without i≥cleared)'}")


d2222 = [("case2", 0, 0, (0, 0, 0), set(), 1), ("case2", 0, 1, (0, 1, 1), {(0, 1, 1)}, 0),
         ("rollover", 0, 2, None, set(), 0)]
dwide = lambda: [("case2", 0, 0, (0, 0, 0), set(), 1),
                 ("case2", 0, 1, (0, 1, 1), {(0, 1, 1), (0, 2, 1)}, 0), ("rollover", 0, 2, None, set(), 0)]
check((2, 2, 2, 2), d2222, "CANONICAL (2,2,2,2)")
check((2, 3, 2), dwide(), "WIDE (2,3,2)")
check((2, 3, 2, 2), dwide(), "WIDE (2,3,2,2)")
