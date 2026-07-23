"""
R3+R4 BLOCK-FORM battery (§8(i) frozen spec; §8(j)-corrected criterion = the MULTILINEAR clean block,
NOT entry-ideal-equality — RLCT rides the change-of-variables).  Merge-gate pre-stage on §8(i) math;
the FINAL run must consume arch-C's EXACT rendered formulas (certificate-fidelity rule).

§8(i) DEF-EDIT-3:
  (a) branch-(i) REPLACED by R4 = the paired generator transform Q₁·A_S·Q₂ on the RAW A_S → diag(1,e₂)
      (clears BOTH the pivot column [Q₁, row-op] AND the pivot row [Q₂, col-op]; SUBSUMES the old Schur
      cross-term — stacking would double-count);
  (b) branch-(ii) FLIPPED to A_{S+1}·Q₁ (−γ, council's Q1);
  (c) foldResid at case11 = the CLEAN BLOCK D_J.

BATTERY (record what is TRUE; RE-OPEN if the multilinear clean block is NOT reached):
  (i)   E_J (cleared columns) clean — pure deeper product, no pivot/exceptional junk;
  (ii)  corner = classical e₂ = −γ·β (the Schur complement) in the block;
  (iii) D_J degree ≤ 1 per pivot-ROW coord (u₀₀₁) AND per pivot-COL coord (u₀₁₀) — MULTILINEAR, NO u₀₀₁².
The decisive contrast: R3-ALONE (branch-i Schur only, row/col NOT cleared) left a u₀₀₁² (my earlier flag);
R4 clears the pivot ROW too, so the u₀₀₁² must DISSOLVE.  We compute R3-alone AND R3+R4 to show the delta.
"""
import sympy as sp


def make(d):
    N = len(d) - 1
    return N, {(L, r, c): sp.Symbol(f"u{L}{r}{c}") for L in range(N) for r in range(d[L + 1]) for c in range(d[L])}


def rd(u, d, S, row, col):
    N = len(d) - 1
    return u[(S, row, col)] if (0 <= S < N and 0 <= row < d[S + 1] and 0 <= col < d[S]) else sp.Integer(0)


def shear(u, d, sL, sC, piv, sign, clear_rowcol):
    """R3-alone (clear_rowcol=False): branch-i Schur interior + branch-ii recoord(sign).
       R3+R4   (clear_rowcol=True):  ALSO clear pivot row/col of A_S -> 0 (the paired Q1·A_S·Q2 clear)."""
    a, b = piv[1], piv[2]
    w = dict(u)
    for (L, r, c) in u:
        if L == sL and sC <= r and sC <= c:
            if r != a and c != b:
                w[(L, r, c)] = u[(L, r, c)] - rd(u, d, sL, r, b) * rd(u, d, sL, a, c)   # Schur interior
            elif clear_rowcol and (r, c) != (a, b):
                w[(L, r, c)] = sp.Integer(0)                                            # R4: clear pivot row/col
        elif L == sL + 1 and c == a:
            w[(L, r, c)] = u[(L, r, c)] + sign * sum(
                (rd(u, d, sL, i, b) * rd(u, d, sL + 1, r, i) for i in range(d[sL + 1]) if i != c), sp.Integer(0))
    return w


def apply_edge(u, d, case, sL, sC, piv, cen, delta, sign, clear_rowcol):
    w = dict(u) if case in ("case11", "rollover") else shear(u, d, sL, sC, piv, sign, clear_rowcol)
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


def fold(d, edges, sign, clear_rowcol):
    N, u = make(d)
    v = dict(u)
    for e in reversed(edges):
        v = apply_edge(v, d, *e, sign, clear_rowcol)
    return coreGen(v, d), u


def maxdeg_in(f, xs):
    xs = [x for x in xs if x in f.free_symbols]
    return 0 if not xs else max(sum(m) for m in sp.Poly(sp.expand(f), *xs).monoms())


def report(d, edges, label):
    N, u0 = make(d)
    u001, u010 = u0[(0, 0, 1)], u0[(0, 1, 0)]
    print("=" * 82)
    print(f"{label}: d={d}   reuse-parent node = after {len(edges)} edges")
    for tag, cr in [("R3-alone (branch-i Schur, NO row/col clear)", False), ("R3+R4 (paired clear → diag)", True)]:
        ents, u = fold(d, edges, -1, cr)   # sign=-1 = council's −γ (R3)
        u001, u010 = u[(0, 0, 1)], u[(0, 1, 0)]
        print(f"\n  --- {tag} ---")
        worst_row = worst_col = 0
        for j, f in enumerate(ents):
            drow = maxdeg_in(f, [u001])
            dcol = maxdeg_in(f, [u010])
            worst_row = max(worst_row, drow); worst_col = max(worst_col, dcol)
            print(f"    slot {j}: deg_u001(row)={drow}, deg_u010(col)={dcol}")
        ml = worst_row <= 1 and worst_col <= 1
        print(f"    => MULTILINEAR clean block (deg ≤1 per pivot row AND col coord): {ml}"
              f"   [pivot-row u001 max {worst_row}, pivot-col u010 max {worst_col}]"
              + ("" if ml else "   <-- NOT multilinear"))


# (2,2,2,2) reuse-parent (canonical) + wide (2,3,2), (2,3,2,2)
report((2, 2, 2, 2), [("case2", 0, 0, (0, 0, 0), set(), 1), ("case2", 0, 1, (0, 1, 1), {(0, 1, 1)}, 0),
                      ("rollover", 0, 2, None, set(), 0)], "CANONICAL (2,2,2,2)")
report((2, 3, 2), [("case2", 0, 0, (0, 0, 0), set(), 1), ("case2", 0, 1, (0, 1, 1), {(0, 1, 1), (0, 2, 1)}, 0),
                   ("rollover", 0, 2, None, set(), 0)], "WIDE (2,3,2)")
report((2, 3, 2, 2), [("case2", 0, 0, (0, 0, 0), set(), 1), ("case2", 0, 1, (0, 1, 1), {(0, 1, 1), (0, 2, 1)}, 0),
                      ("rollover", 0, 2, None, set(), 0)], "WIDE (2,3,2,2)")


# ---- SOURCE ISOLATION: is the u001^2 from ed2's recoord reading ed1's (pre-clear) pivot-row entry? ----
print("\n" + "#" * 82)
print("SOURCE ISOLATION (why R4 does not dissolve u001^2 in the foldResid ORDER)")
print("Lean foldResid_extend_delta0: foldResid(p.extend ed)(u) = foldResid(p)(stepMap(ed,u)) — deepest edge")
print("applied FIRST, ed1 (the (0,0)-clear) OUTERMOST. So ed2's recoord reads ed1's pivot-row entry u001")
print("BEFORE ed1's clear reaches it. Test: drop ed2 (fold [ed1, rollover] only) — u001^2 should vanish.")
for lbl, edges in [("R4 with ed2 (full reuse branch)",
                    [("case2",0,0,(0,0,0),set(),1),("case2",0,1,(0,1,1),{(0,1,1)},0),("rollover",0,2,None,set(),0)]),
                   ("R4 WITHOUT ed2 (only ed1 + rollover)",
                    [("case2",0,0,(0,0,0),set(),1),("rollover",0,1,None,set(),0)])]:
    ents, u = fold((2,2,2,2), edges, -1, True)   # R4 (clear_rowcol=True), −γ
    u001 = u[(0,0,1)]
    md = max(maxdeg_in(f,[u001]) for f in ents)
    print(f"   {lbl}: max deg_u001 = {md}" + ("  <-- u001^2 PRESENT" if md>=2 else "  <-- clean (deg ≤1)"))
print("=> if ed2-present gives deg 2 and ed2-absent gives deg ≤1, the u001^2 is ed2's recoord reading")
print("   ed1's UNCLEARED pivot-row entry (fold-order effect). Whether arch-C's R4 render has ed2 read the")
print("   R4-CLEARED entry (=> no u001^2, gate PASSES) or the raw entry (=> u001^2, RE-OPEN) is THE def")
print("   question — final verdict pends arch-C's EXACT rendered branch-(ii) formula (certificate-fidelity).")
