"""
CAPSTONE KILL-CONDITION ADJUDICATION (pnp-transport, task #68/#69 — the def-owners' gate).

L4D + team-lead's binary question: with Φ_p computed DEF-EXACT (coreGen ∘ per-edge argument
transforms; split edges apply edgeShearRaw = blockShear canonNormalizationOf = the F₂ 3-branch
recoord AS MERGED, NOT a naive shear), does the extra block of foldResid(p) factor through RAW
u_{e₂} (e₂ = canonPivotOf = the reused divisor's BIRTH corner)?
  RAW-SPLIT TRUE  -> the F₂ recoord renders the block ⟨center⟩-clean in raw coords; write the cert.
  CHART-ONLY      -> factoring is through the birth Schur / per-slot different raw coords ->
                     MergeBoostSplit-with-raw-u_{e₂} + the wall's raw Deg1SupportedOn are a
                     STATEMENT-SOUNDNESS problem. STOP, escalate.

This script is the decisive re-run. Φ_p is def-exact. Corrected oracle: case11 KEEPS cleared
(DescendView), so stacked merges (double-boost) sit at the SAME node. Four properties tested per
case11 node, scoped AND unscoped:
  (A) raw-u_{e₂} divisibility of every extra coeff  [THE predicate]
  (B) degree ≤ 1 in every coord / no u_{e₂}²          [the design 'multilinear-clean' / battery claim]
  (C) does extra factor through the CHART value (Φ_p u)_{e₂}?  [L4D's chart-exceptional hypothesis]
  (D) each slot ∈ ⟨ed.center⟩ (continuous decomp, via zero-variety test)  [Deg1SupportedOn ed.center]
"""
import sympy as sp

# ---------- flat coords / render / coreGen (def-exact, from MonumentAtlas:906-966) ----------
def dims_coords(d):
    N = len(d) - 1
    u = {(L, r, c): sp.Symbol(f"u_{L}_{r}_{c}") for L in range(N)
         for r in range(d[L + 1]) for c in range(d[L])}
    return N, u

def readEntry(u, d, S, row, col):
    N = len(d) - 1
    return u[(S, row, col)] if (0 <= S < N and 0 <= row < d[S + 1] and 0 <= col < d[S]) else sp.Integer(0)

def canonNormalizationOf(u, d, S, cleared, piv, scoped=True):
    a, b = piv[1], piv[2]; lo = cleared if scoped else 0
    phi = {}
    for (L, row, col) in u:
        if L == S and row != a and col != b and cleared <= row and cleared <= col:
            phi[(L, row, col)] = -readEntry(u, d, S, row, b) * readEntry(u, d, S, a, col)
        elif L == S + 1 and col == a:
            phi[(L, row, col)] = sum((readEntry(u, d, S, i, b) * readEntry(u, d, S + 1, row, i)
                                      for i in range(d[S + 1]) if not (i == a or i < lo)), sp.Integer(0))
        elif L + 1 == S and row == b:
            phi[(L, row, col)] = sum((readEntry(u, d, S, a, k) * readEntry(u, d, S - 1, k, col)
                                      for k in range(d[S]) if not (k == b or k < lo)), sp.Integer(0))
        else:
            phi[(L, row, col)] = sp.Integer(0)
    return phi

def coreGen(u, d):
    N = len(d) - 1
    P = sp.Matrix(d[N], d[N - 1], lambda r, c: u[(N - 1, r, c)])
    for L in range(N - 2, -1, -1):
        P = P * sp.Matrix(d[L + 1], d[L], lambda r, c: u[(L, r, c)])
    return [P[i, j] for i in range(P.rows) for j in range(P.cols)]

def apply_edge(u, d, case, sL, sC, piv, cen, delta, scoped=True):
    # edgeShearRaw: id at case11/rollover, blockShear canonNormalizationOf at case2/case12
    if case in ("case11", "rollover"):
        w = dict(u)
    else:
        phi = canonNormalizationOf(u, d, sL, sC, piv, scoped)
        w = {k: u[k] + phi[k] for k in u}
    out = {}
    for k in u:
        if case == "rollover":
            out[k] = w[k]
        elif delta == 1:                                  # blockBlowupCoordQuot(pivot): pivot->1
            out[k] = sp.Integer(1) if k == piv else w[k]
        else:                                              # blockBlowupMap(center,pivot)
            out[k] = (w[piv] if k == piv else (w[piv] * w[k] if k in cen else w[k]))
    return out

def Phi_p(u, d, parent_edges, scoped=True):
    v = dict(u)
    for e in reversed(parent_edges):                       # root edge outermost = applied last
        v = apply_edge(v, d, *e, scoped)
    return v

# ---------- geometry ----------
def wmu(d, n):
    N = len(d) - 1
    return min(d[i] for i in range(0, min(n, N - 1) + 1))
def cornerToFlat(d, S, J): return (S, J, J)
def blockCoords(d, S): return {(S, r, c) for r in range(d[S + 1]) for c in range(d[S]) if c < wmu(d, S)}
def canonCenter11(d, S, J, runLen, pivFlat):
    return {pivFlat} | {(S, r, c) for r in range(d[S + 1]) for c in range(d[S]) if r >= J and J <= c < J + runLen}

# ---------- CORRECTED oracle: case11 KEEPS cleared (DescendView) ----------
def oracle_edges(d):
    N = len(d) - 1; Lmax = N - 1
    layer, cleared, numDiv = 0, 0, 0
    divTilde, birth = [], []
    edges, meta = [], []
    for _ in range(400):
        if Lmax <= layer:
            edges.append(("terminal", layer, cleared, None, set(), 0)); meta.append({}); break
        if wmu(d, layer + 1) <= cleared:
            edges.append(("rollover", layer, cleared, None, set(), 1 if cleared == 0 else 0)); meta.append({})
            layer, cleared = layer + 1, 0; continue
        occ = sorted({divTilde[k] for k in range(numDiv) if cleared + 1 <= divTilde[k] <= wmu(d, layer) - 1})
        delta = 1 if cleared == 0 else 0
        if occ:
            target = occ[0]; f = [k for k in range(numDiv) if divTilde[k] == target][0]
            runLen = target - cleared
            pivFlat = cornerToFlat(d, birth[f][0], birth[f][1])
            cen = canonCenter11(d, layer, cleared, runLen, pivFlat)
            edges.append(("case11", layer, cleared, pivFlat, cen, delta))
            meta.append(dict(runLen=runLen, f=f, birth_f=birth[f], pivFlat=pivFlat))
            divTilde[f] = cleared                          # KEEP cleared, KEEP numDiv
        else:
            pivFlat = cornerToFlat(d, layer, cleared)
            cen = {(layer, r, c) for r in range(d[layer + 1]) for c in range(d[layer])
                   if r >= cleared and cleared <= c < wmu(d, layer)}
            edges.append(("case2", layer, cleared, pivFlat, cen, delta))
            meta.append({})
            divTilde.append(cleared); birth.append((layer, cleared)); numDiv += 1; cleared += 1
    return edges, meta

# ---------- property tests ----------
def coeff_in_support(fe, u, support, i):
    return sp.expand(fe.coeff(u[i], 1))

def test_node(d, edges, meta, idx, scoped, label):
    N, u = dims_coords(d)
    ce = edges[idx]; parent = edges[:idx]; cm = meta[idx]
    S, J = ce[1], ce[2]; e2 = ce[3]; center = ce[4]
    support = blockCoords(d, S)
    part = support & center; extra = support - center
    v = Phi_p(u, d, parent, scoped)                        # def-exact Φ_p
    fr = coreGen(v, d)                                      # foldResid(p) = coreGen(Φ_p u)
    ue2 = u[e2]
    chart_e2 = sp.expand(v[e2])                            # (Φ_p u)_{e₂}: the CHART value at e₂
    support_syms = {u[c] for c in support}
    # (A) raw-u_{e₂} divisibility of extra coeffs
    A = True
    for f in fr:
        fe = sp.expand(f)
        for i in extra:
            ci = coeff_in_support(fe, u, support, i)
            if ci != 0 and sp.expand(ci.subs(ue2, 0)) != 0:
                A = False
    # (B) degree <= 1 in every coord (no square of ANY coord, incl u_{e₂})
    B = True
    for f in fr:
        fe = sp.expand(f)
        for sym in fe.free_symbols:
            if sp.degree(sp.Poly(fe, sym), sym) > 1:
                B = False; break
    # (C) does extra factor through the CHART value chart_e2? (test each extra coeff ∈ (chart_e2))
    #     only meaningful if chart_e2 is a nonunit polynomial; report divisibility by setting chart_e2's vars.
    # (D) each slot ∈ ⟨center⟩: zero-variety test — set all center coords = 0, slot must vanish.
    zero_sub = {u[c]: 0 for c in center}
    D = all(sp.expand(sp.expand(f).subs(zero_sub)) == 0 for f in fr)
    # obstruction coords: for a failing extra coeff, which single raw coord divides it?
    obstruct = {}
    for j, f in enumerate(fr):
        fe = sp.expand(f)
        for i in extra:
            ci = coeff_in_support(fe, u, support, i)
            if ci != 0 and sp.expand(ci.subs(ue2, 0)) != 0:
                divs = sorted(k for k in u if sp.expand(ci.subs(u[k], 0)) == 0)
                obstruct[(j, i)] = divs
    print(f"  [{label} idx{idx} S{S}J{J} e₂={e2} runLen={cm.get('runLen')} reuse{cm.get('birth_f')}] "
          f"scoped={scoped}")
    print(f"      center={sorted(center)}  extra={sorted(extra)}")
    print(f"      (A) raw-u_e₂ split: {A}   (B) deg≤1 all coords: {B}   (D) slots∈⟨center⟩: {D}")
    if not A:
        samp = list(obstruct.items())[:2]
        print(f"      obstruction (extra coeff NOT ÷ u_e₂; single raw divisors): {samp}")
    print(f"      chart value (Φ_p u)_e₂ = {chart_e2}")
    return dict(A=A, B=B, D=D)

def run(d, label):
    print("=" * 90)
    print(f"WITNESS {label}: d={d}")
    edges, meta = oracle_edges(d)
    print("  branch:", [(e[0], e[1], e[2]) for e in edges])
    c11 = [i for i, e in enumerate(edges) if e[0] == "case11"]
    res = []
    for idx in c11:
        for scoped in (True, False):
            res.append(test_node(d, edges, meta, idx, scoped, label))
    return res

if __name__ == "__main__":
    allres = []
    allres += run((2, 2, 2, 2), "MINIMAL")
    allres += run((3, 3, 3, 2), "WIDE-INTERIOR")
    allres += run((3, 3, 2, 2), "DOUBLE-BOOST")
    print("=" * 90)
    anyA = any(r["A"] for r in allres)
    allB = all(r["B"] for r in allres)
    noA = not any(r["A"] for r in allres)
    print("VERDICT SUMMARY")
    print(f"  raw-u_e₂ split holds on ANY case11 node/scope: {anyA}")
    print(f"  degree≤1 (design 'multilinear-clean') holds EVERYWHERE: {allB}")
    print(f"  => {'RAW-SPLIT TRUE somewhere' if anyA else 'CHART-ONLY (raw-split FALSE on all real case11 nodes)'}")
