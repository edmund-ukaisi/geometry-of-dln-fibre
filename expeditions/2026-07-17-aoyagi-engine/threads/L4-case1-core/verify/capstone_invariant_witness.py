"""
CAPSTONE per-edge invariant WITNESS (WIP — FRAME-FINDING) — for foldResid_case11_mergeBoostSplit_canon.
Paper anchor: worked.tex:562-577 (carried invariant diag(b)·[[E_J,O],[O,D_J]]) + :400-457 (Lemma 2).

FINDING (this run): the MergeBoostSplit read-off (extra-block factors through u_{e₂}) does NOT hold with the
RAW coordinate u(0,1,1) as e₂ — the extra coeffs (e.g. 2·u₀₁₀·u₂₀₀) are not divisible by raw u₀₁₁. This is
the recurring FRAME theme: the fold writes the Schur exceptional e₂ = u₀₁₁ − u₀₁₀·u₀₀₁ into coordinate
(0,1,1) via ed1's branch-(i) shear (w[(0,1,1)] = u₀₁₁ − u₀₁₀·u₀₀₁), and the split factors through THAT
(the normalized-chart e₂), not the raw pivot coord. So the read-off is a CHART/normalized-frame statement.
The exact coordinate identification — what `canonPivotOf`/`u e₂` reads, supportAt/ed.center in the fold's
coord frame, and how foldResid's raw `u` argument relates to the chart e₂ — is Lean-def-dependent and is
what L4D's recursion-signature addendum pins. The invariant STRUCTURE (root/δ=1/δ=0/read-off) is from the
paper + npivot-certificate (frame-independent); the exact-frame read-off waits on the addendum.
(Also: (C4) born-unit at the strict-transform origin — my raw u_{piv}→1,rest→0 substitution gives 0; the
born-unit is likewise a chart-frame statement (the fresh exceptional = the blow-up coordinate), pending the
same frame pin.)
"""

import sympy as sp


def dims_coords(d):
    N = len(d) - 1
    return N, {(L, r, c): sp.Symbol(f"u_{L}_{r}_{c}") for L in range(N) for r in range(d[L + 1]) for c in range(d[L])}


def readEntry(u, d, S, row, col):
    N = len(d) - 1
    return u[(S, row, col)] if (0 <= S < N and 0 <= row < d[S + 1] and 0 <= col < d[S]) else sp.Integer(0)


def canonNormalizationOf(u, d, S, cleared, piv):
    """render 3-branch def (MonumentAtlas:906-966)."""
    a, b = piv[1], piv[2]
    phi = {}
    for (L, row, col) in u:
        if L == S and row != a and col != b and cleared <= row and cleared <= col:
            phi[(L, row, col)] = -readEntry(u, d, S, row, b) * readEntry(u, d, S, a, col)
        elif L == S + 1 and col == a:
            phi[(L, row, col)] = sum((readEntry(u, d, S, i, b) * readEntry(u, d, S + 1, row, i)
                                      for i in range(d[S + 1]) if not (i == a or i < cleared)), sp.Integer(0))
        elif L + 1 == S and row == b:
            phi[(L, row, col)] = sum((readEntry(u, d, S, a, k) * readEntry(u, d, S - 1, k, col)
                                      for k in range(d[S]) if not (k == b or k < cleared)), sp.Integer(0))
        else:
            phi[(L, row, col)] = sp.Integer(0)
    return phi


def apply_edge(u, d, case, sL, sC, piv, cen, delta):
    w = dict(u) if case in ("case11", "rollover") else {k: u[k] + canonNormalizationOf(u, d, sL, sC, piv)[k] for k in u}
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


def fold_parent(d, edges):
    N, u = dims_coords(d)
    v = dict(u)
    for e in reversed(edges):
        v = apply_edge(v, d, *e)
    return coreGen(v, d), u


def readoff(d, parent_edges, e2, center, label):
    """(R)+(I): does foldResid(parent) split as ∑_part α·u + u_e2·∑_extra β·u, α,β center-ignoring?"""
    ents, u = fold_parent(d, parent_edges)
    ue2 = u[e2]
    centercoords = {u[c] for c in center}
    # supportAt = coords actually appearing; part = support ∩ center, extra = support ∖ center
    print(f"  {label}: e₂ = u{e2}, |center|={len(center)}")
    ok_R = ok_I = True
    for j, f in enumerate(ents):
        f = sp.expand(f)
        supp = [k for k in u if u[k] in f.free_symbols]
        part = [k for k in supp if k in center]
        extra = [k for k in supp if k not in center]
        # (R) each extra coord's coefficient (deg-1 in that coord) is divisible by u_e2
        for k in extra:
            coeff = sp.expand(f.coeff(u[k], 1))
            div_by_e2 = (sp.rem(sp.Poly(coeff, ue2), sp.Poly(ue2, ue2)) == 0) if ue2 in coeff.free_symbols or coeff == 0 else (coeff == 0)
            # a cleaner test: coeff vanishes when u_e2=0  (⟺ divisible by u_e2, coeff being a polynomial)
            vanishes_at_e2_0 = sp.expand(coeff.subs(ue2, 0)) == 0
            if not vanishes_at_e2_0:
                ok_R = False
                print(f"    slot {j}: EXTRA coord u{k} coeff NOT div by u_e2 (e2=%s): {coeff}" % str(e2) + "")
        # (I) center-ignoring: the α (partial coeff) and β (extra coeff / u_e2) don't depend on center coords
        # partial coeff:
        for k in part:
            if k == e2:
                continue
            coeff = sp.expand(f.coeff(u[k], 1))
            if coeff.free_symbols & centercoords:
                # α_i may legitimately involve OTHER partial coords? no — center-ignoring means no center dep
                ok_I = False
    print(f"    (R) extra factors through u_e2: {ok_R};   (I) coeffs center-ignoring: {ok_I}")
    return ok_R


# (2,2,2,2) canonical case11: parent = [ed1 case2 δ1 (0,0,0), ed2 case2 δ0 (0,1,1), rollover]; case11 reuses (0,1,1)
BR_2222 = [("case2", 0, 0, (0, 0, 0), set(), 1), ("case2", 0, 1, (0, 1, 1), {(0, 1, 1)}, 0), ("rollover", 0, 2, None, set(), 0)]
CENTER_2222 = {(0, 1, 1), (1, 0, 0), (1, 1, 0)}   # {e₂} ∪ layer-1 partial block (col 0)
print("=" * 82)
print("(R)+(I) READ-OFF — the boost-split on the render foldResid at the case11 node:")
readoff((2, 2, 2, 2), BR_2222, (0, 1, 1), CENTER_2222, "(2,2,2,2)")
BR_2322 = [("case2", 0, 0, (0, 0, 0), set(), 1), ("case2", 0, 1, (0, 1, 1), {(0, 1, 1), (0, 2, 1)}, 0), ("rollover", 0, 2, None, set(), 0)]
CENTER_2322 = {(0, 1, 1), (1, 0, 0), (1, 1, 0)}
readoff((2, 3, 2, 2), BR_2322, (0, 1, 1), CENTER_2322, "(2,3,2,2) wide")

print("\n" + "=" * 82)
print("(C4) born-unit — case12/case2 GENUINE clear δ=1: ∃ slot with pivot-coeff at origin ≠ 0:")
for d, edges, piv in [((2, 2, 2, 2), [("case2", 0, 0, (0, 0, 0), set(), 1)], (0, 0, 0))]:
    ents, u = fold_parent(d, edges)   # child after ed1 (δ=1 genuine clear)
    # child residual at origin: strict transform u_{piv}→1, others→0; born unit = residual value at that point
    at0 = {u[k]: (1 if k == piv else 0) for k in u}
    vals = [sp.expand(f.subs(at0)) for f in ents]
    nonzero = [v for v in vals if v != 0]
    print(f"  {d} after case2-δ1 clear (0,0,0): child residual at strict-transform origin = {vals}; ∃ nonzero (born unit): {len(nonzero)>0}")
