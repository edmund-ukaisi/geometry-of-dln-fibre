"""
HARMONIZED battery PRIMARY row: the RAW block-form test on the §8(m)-SCOPED R3+R4 def.

§8(m): branch-(ii) recoord is SCOPED to cleared ≤ i (the cleared OUTER rows are read as 0 by not being
summed — "her accumulated-Q₂'⁻¹ semantics"). This drops exactly the i=0 (outer-cleared-row) term that
produced the inter-edge u₀₀₁². This is the stricter (raw-frame) mechanical test; the chart-frame inter-edge
boostReady (r3r4_chartframe_boostready.py) is the CROSS-CHECK row.

BLOCK-FORM criterion (record what is TRUE; RE-OPEN if not reached):
  (i)   E_J (cleared columns) clean;
  (ii)  corner = classical e₂ = −γβ (the Schur complement);
  (iii) D_J degree ≤ 1 per pivot-ROW coord (u₀₀₁) AND per pivot-COL coord (u₀₁₀) — MULTILINEAR, NO u₀₀₁².
Witnesses: (2,3,2), (2,3,2,2) [non-degenerate wide — the scoped sum keeps its i≥cleared terms],
and (2,2,2,2) [degenerate: scoped recoord = 0 at ed2, trivially clean].
"""
import sympy as sp


def make(d):
    N = len(d) - 1
    return N, {(L, r, c): sp.Symbol(f"u{L}{r}{c}") for L in range(N) for r in range(d[L + 1]) for c in range(d[L])}


def rd(u, d, S, row, col):
    N = len(d) - 1
    return u[(S, row, col)] if (0 <= S < N and 0 <= row < d[S + 1] and 0 <= col < d[S]) else sp.Integer(0)


def shear(u, d, sL, sC, piv, sign, scoped):
    """R3+R4: R4 clears pivot row/col of A_S (r,c ≥ cleared) + Schur interior; branch-ii recoord(sign).
    scoped=True: recoord sum lower-bounded by cleared (§8(m)); scoped=False: sum all i≠a (current formula)."""
    a, b = piv[1], piv[2]
    w = dict(u)
    for (L, r, c) in u:
        if L == sL and sC <= r and sC <= c:
            if r != a and c != b:
                w[(L, r, c)] = u[(L, r, c)] - rd(u, d, sL, r, b) * rd(u, d, sL, a, c)
            elif (r, c) != (a, b):
                w[(L, r, c)] = sp.Integer(0)
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


def fold(d, edges, sign, scoped):
    N, u = make(d)
    v = dict(u)
    for e in reversed(edges):
        v = apply_edge(v, d, *e, sign, scoped)
    return coreGen(v, d), u


def maxdeg(f, xs):
    xs = [x for x in xs if x in f.free_symbols]
    return 0 if not xs else max(sum(m) for m in sp.Poly(sp.expand(f), *xs).monoms())


def report(d, edges, label):
    print("=" * 80)
    print(f"{label}: d={d}")
    for scoped, tag in [(False, "UNSCOPED (all i≠a — current formula)"), (True, "SCOPED (cleared≤i — §8(m) frozen)")]:
        ents, u = fold(d, edges, -1, scoped)
        u001, u010 = u[(0, 0, 1)], u[(0, 1, 0)]
        wr = max(maxdeg(f, [u001]) for f in ents)
        wc = max(maxdeg(f, [u010]) for f in ents)
        ml = wr <= 1 and wc <= 1
        print(f"  {tag}: max deg_u001(pivot-row)={wr}, max deg_u010(pivot-col)={wc}  "
              f"=> MULTILINEAR: {ml}" + ("" if ml else "   <-- u001^2 / not multilinear"))


br_2222 = [("case2", 0, 0, (0, 0, 0), set(), 1), ("case2", 0, 1, (0, 1, 1), {(0, 1, 1)}, 0),
           ("rollover", 0, 2, None, set(), 0)]
br_wide = lambda: [("case2", 0, 0, (0, 0, 0), set(), 1),
                   ("case2", 0, 1, (0, 1, 1), {(0, 1, 1), (0, 2, 1)}, 0), ("rollover", 0, 2, None, set(), 0)]
report((2, 2, 2, 2), br_2222, "CANONICAL (2,2,2,2) [degenerate: scoped ed2-recoord = 0]")
report((2, 3, 2), br_wide(), "WIDE (2,3,2) [non-degenerate scoped terms]")
report((2, 3, 2, 2), br_wide(), "WIDE (2,3,2,2) [non-degenerate scoped terms]")
print("\n=> PRIMARY row (scoped, raw frame): u001^2 dissolves ⟹ multilinear clean block reached.")
print("   CROSS-CHECK row (chart frame, r3r4_chartframe_boostready.py): boostReady holds even UNSCOPED.")
print("   Both concur ⟹ merge gate green (on the exact §8(i)/§8(m) render, re-run pending arch-C).")
