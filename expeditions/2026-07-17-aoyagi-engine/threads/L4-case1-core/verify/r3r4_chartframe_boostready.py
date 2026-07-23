"""
THE DECISIVE INTER-EDGE CHART-FRAME test (elder's one gap; seat-L4D's exact center).

boostReady_case11 = Deg1SupportedOn the boost CENTER in the NORMALIZED-CHART frame. seat-L4D:
  center(case11) = {w = e₂ = u₀₁₁ − u₀₀₁·u₀₁₀} ∪ partialBlock (layer-1 col < runLen),  e₂ atomic in the chart.
u₀₀₁ is ENTANGLED inside e₂, so the raw-frame u₀₀₁² (my inter-edge flag) may be a benign chart-degree-1.
seat-L4D's boost_center is single-step; my u₀₀₁² is INTER-EDGE (reuse node after ed1/ed2/ed3). So run the
inter-edge R3+R4 reuse-node residual IN the chart frame and check Deg1SupportedOn the center.

METHOD (no raw expansion): extract the fold's TRANSFORMED layer-0 block L0 and layer-1 factor L1 that
coreGen reads. If L0 = diag(1, e₂) (R4 clean) then residual = A₂·L1·L0, and in the CHART coords {A₂ entries,
L1 entries (=w), e₂} it is manifestly degree ≤ 1 in the center {e₂, L1 col-0}: col-0 = A₂·L1[:,0] (center
partialBlock, deg 1), col-1 = e₂·A₂·L1[:,1] (e₂ center deg 1 × extra-block L1[:,1]). The raw u₀₀₁² is then
just the expansion of the PRODUCT e₂·L1[:,1] (both expand to carry u₀₀₁) — chart-degree-1, boostReady holds.
We VERIFY L0 = diag(1,e₂) and that the residual equals A₂·L1·L0, then read the chart-frame center-degree.
"""
import sympy as sp


def make(d):
    N = len(d) - 1
    return N, {(L, r, c): sp.Symbol(f"u{L}{r}{c}") for L in range(N) for r in range(d[L + 1]) for c in range(d[L])}


def rd(u, d, S, row, col):
    N = len(d) - 1
    return u[(S, row, col)] if (0 <= S < N and 0 <= row < d[S + 1] and 0 <= col < d[S]) else sp.Integer(0)


def shear(u, d, sL, sC, piv, sign):
    """R3+R4: R4 clears pivot row/col of A_S (r,c >= cleared) + Schur interior; R3 = branch-ii recoord(sign)."""
    a, b = piv[1], piv[2]
    w = dict(u)
    for (L, r, c) in u:
        if L == sL and sC <= r and sC <= c:
            if r != a and c != b:
                w[(L, r, c)] = u[(L, r, c)] - rd(u, d, sL, r, b) * rd(u, d, sL, a, c)
            elif (r, c) != (a, b):
                w[(L, r, c)] = sp.Integer(0)
        elif L == sL + 1 and c == a:
            w[(L, r, c)] = u[(L, r, c)] + sign * sum(
                (rd(u, d, sL, i, b) * rd(u, d, sL + 1, r, i) for i in range(d[sL + 1]) if i != c), sp.Integer(0))
    return w


def apply_edge(u, d, case, sL, sC, piv, cen, delta, sign):
    w = dict(u) if case in ("case11", "rollover") else shear(u, d, sL, sC, piv, sign)
    out = {}
    for k in u:
        if case == "rollover":
            out[k] = w[k]
        elif delta == 1:
            out[k] = sp.Integer(1) if k == piv else w[k]
        else:
            out[k] = (w[piv] if k == piv else (w[piv] * w[k] if k in cen else w[k]))
    return out


def fold_to_tuple(d, edges, sign):
    """Return the TRANSFORMED tuple v that coreGen reads (before the matrix product)."""
    N, u = make(d)
    v = dict(u)
    for e in reversed(edges):
        v = apply_edge(v, d, *e, sign)
    return N, u, v


d = (2, 2, 2, 2)
br = [("case2", 0, 0, (0, 0, 0), set(), 1), ("case2", 0, 1, (0, 1, 1), {(0, 1, 1)}, 0),
      ("rollover", 0, 2, None, set(), 0)]
N, u, v = fold_to_tuple(d, br, -1)

# transformed layer-0 block L0 (2x2) and layer-1 factor L1 (2x2) that coreGen reads
L0 = sp.Matrix(2, 2, lambda r, c: sp.expand(v[(0, r, c)]))
L1 = sp.Matrix(2, 2, lambda r, c: sp.expand(v[(1, r, c)]))
A2 = sp.Matrix(2, 2, lambda r, c: v[(2, r, c)])
e2_raw = sp.expand(u[(0, 1, 1)] - u[(0, 0, 1)] * u[(0, 1, 0)])
print("transformed layer-0 block L0 (what coreGen reads):")
sp.pprint(L0)
print(f"\nL0 == diag(1, e₂) with e₂ = u011 - u001·u010 ?  {L0 == sp.diag(1, e2_raw)}")
print(f"  L0[0][0]={L0[0,0]}, L0[0][1]={L0[0,1]}, L0[1][0]={L0[1,0]}, L0[1][1]-e₂={sp.expand(L0[1,1]-e2_raw)}")

# residual = A2 · L1 · L0 ; center (chart) = {e₂ (=L0[1][1]), L1 col-0}, extra = L1 col-1
print("\nCHART-FRAME reading: treat e₂ := L0[1][1] and w := L1 entries as ATOMIC chart coords.")
print("residual = A2·L1·diag(1,e₂):  col-0 = A2·(L1 col0);  col-1 = e₂·A2·(L1 col1).")
E2 = sp.Symbol("e2"); W = sp.Matrix(2, 2, lambda r, c: sp.Symbol(f"w1{r}{c}"))
resid_chart = A2 * W * sp.diag(1, E2)
# center chart coords: e₂ and partialBlock = L1 col-0 = {w100, w110}; extra = {w101, w111}
center = [E2, W[0, 0], W[1, 0]]
extra = [W[0, 1], W[1, 1]]
allc = [E2] + list(W)
ok = True
for i in range(2):
    for j in range(2):
        f = sp.expand(resid_chart[i, j])
        cdeg = 0 if not any(c in f.free_symbols for c in center) else \
            max(sum(m) for m in sp.Poly(f, *[c for c in center if c in f.free_symbols]).monoms())
        at0 = sp.expand(f.subs({c: 0 for c in center})) == 0
        ok = ok and cdeg <= 1 and at0
        print(f"  slot[{i}][{j}]: {f}   center-deg={cdeg} (Deg1:{cdeg<=1}), vanishes@center0:{at0}")
print(f"\n=> CHART-FRAME Deg1SupportedOn center (e₂ + L1col0): {ok}")

# and confirm the raw residual (with u001^2) EQUALS the chart residual under e₂,w := their raw values
resid_raw = sp.expand((A2 * L1 * L0))
subs_map = {E2: e2_raw}
for r in range(2):
    for c in range(2):
        subs_map[W[r, c]] = L1[r, c]
resid_chart_expanded = sp.expand(resid_chart.subs(subs_map))
match = sp.expand(resid_raw - resid_chart_expanded) == sp.zeros(2, 2)
print(f"=> raw residual == chart residual under (e₂,w):=raw ?  {match}")
print("   (if True: the raw u₀₀₁² is EXACTLY the expansion of the product e₂·(L1 col1) — a chart-frame")
print("    degree-1 term; boostReady holds in the chart frame; the u₀₀₁² is a benign raw-frame artifact.)")


# ---- WIDE witness (2,3,2,2): confirm L0 is the clean cleared block and the residual is chart-degree-1 ----
print("\n" + "=" * 78)
print("WIDE (2,3,2,2): transformed layer-0 block L0 (3x2) under R3+R4 — clean cleared block?")
d2 = (2, 3, 2, 2)
br2 = [("case2", 0, 0, (0, 0, 0), set(), 1), ("case2", 0, 1, (0, 1, 1), {(0, 1, 1), (0, 2, 1)}, 0),
       ("rollover", 0, 2, None, set(), 0)]
N2, u2, v2 = fold_to_tuple(d2, br2, -1)
L0w = sp.Matrix(3, 2, lambda r, c: sp.expand(v2[(0, r, c)]))
print("L0 (3x2):"); sp.pprint(L0w)
e2w = sp.expand(u2[(0, 1, 1)] - u2[(0, 0, 1)] * u2[(0, 1, 0)])
e3w = sp.expand(u2[(0, 2, 1)] - u2[(0, 0, 1)] * u2[(0, 2, 0)])   # candidate row-2 Schur (wide remnant)
print(f"\n  L0[0] = [{L0w[0,0]}, {L0w[0,1]}] (pivot row 0 cleared?)")
print(f"  L0[1] = [{L0w[1,0]}, {L0w[1,1]}]  (row1: expect [0, e₂]); L0[1][1]-e₂ = {sp.expand(L0w[1,1]-e2w)}")
print(f"  L0[2] = [{L0w[2,0]}, {L0w[2,1]}]  (row2 = wide remnant, NOT a pivot row)")
# is every entry of L0 that is nonzero either 1, an e-Schur (deg1 per coord), or a wide-remnant coord?
print("\n  chart-frame check: is each L0 entry degree ≤1 in the pivot-ROW coord u001 (the multilinear test)?")
u001w = u2[(0, 0, 1)]
worst = 0
for r in range(3):
    for c in range(2):
        f = sp.expand(L0w[r, c])
        dg = 0 if u001w not in f.free_symbols else sp.Poly(f, u001w).degree()
        worst = max(worst, dg)
print(f"    max deg_u001 across L0 entries = {worst}  ({'multilinear in u001' if worst<=1 else 'u001^2 in L0'})")
print("  (L0 is the CLEARED block; if it is diag(1,e₂,·)-shaped with each entry deg≤1 in u001, R4 delivers")
print("   the clean multilinear block. The residual = A2·L1·L0 is then chart-degree-1 in the center as for")
print("   (2,2,2,2): the raw u001^2 is the expansion of e₂·(extra chart coord), not a chart-frame degree-2.)")
