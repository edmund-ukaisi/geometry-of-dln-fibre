"""
CERT (i) STATEMENT-SOUNDNESS COUNTEREXAMPLE — the 27th statement-class catch (seat-CFF, 2026-07-23).

The Lean lemma `canonNormalizationOf_vanishes_on_couplingCoords` was STATED for a GENERAL edge with
no case restriction and no pivot pin:
    ∀ k ∈ couplingCoords d p,
      canonNormalizationOf d p.conState ed.pivot (couplingClear d (p.extend ed) u) k = 0.
This script shows that statement is FALSE, and pins EXACTLY the extra hypothesis that restores it —
which coincides with the #87 pivot-pin `pivot.col = s.cleared`. It reconciles with pnp cert (i)
`3ec969d8f`, which ran on CANONICAL witnesses (col = cleared) and was witness-true: the same
canonical-vs-general gap as the 22nd/23rd catches.

Self-contained: the model (oracle, canonNormalizationOf, couplingCoords, couplingClear, belowPivotCol)
is ported def-exact from `capstone_adjudication.py` / `capstone_locus_core.py` (MonumentAtlas:888-984,
SourceClearedResid:54-82). Re-runnable with `python3 cert_i_counterexample.py` (needs sympy only).

RESULT (the gate re-runs this):
  1. GENERAL statement FALSE at every case11 edge (6 witnesses): the pivot is a birth corner
     (col != cleared), branch (iii)/(i) fires and reads two non-coupling coords -> nonzero write.
  2. Also FALSE at case2 with an off-diagonal (col > cleared) fan pivot -- current IsRealBranch
     rule-(b) `pivot in canonCenterOf` alone permits this.
  3. RESTORED (all edges OK) once `pivot.col = cleared` is imposed (row FREE) -- the #87 pin. That
     is the exact strengthening cert (i)'s render consumes (case2/case12 + pivot.col = cleared).
"""
import sympy as sp

# ---------- flat coords ----------
def dims_coords(d):
    N = len(d) - 1
    u = {(L, r, c): sp.Symbol(f"u_{L}_{r}_{c}") for L in range(N)
         for r in range(d[L + 1]) for c in range(d[L])}
    return N, u

def readEntry(u, d, S, row, col):
    N = len(d) - 1
    return u[(S, row, col)] if (0 <= S < N and 0 <= row < d[S + 1] and 0 <= col < d[S]) else sp.Integer(0)

# canonNormalizationOf (MonumentAtlas:939-984), scoped
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

def wmu(d, n):
    N = len(d) - 1
    return min(d[i] for i in range(0, min(n, N - 1) + 1))
def cornerToFlat(d, S, J): return (S, J, J)

# oracle (capstone_adjudication.oracle_edges): case11 KEEPS cleared (DescendView)
def oracle_edges(d):
    N = len(d) - 1; Lmax = N - 1
    layer, cleared, numDiv = 0, 0, 0
    divTilde, birth = [], []
    edges = []
    for _ in range(400):
        if Lmax <= layer:
            edges.append(("terminal", layer, cleared, None, set(), 0)); break
        if wmu(d, layer + 1) <= cleared:
            edges.append(("rollover", layer, cleared, None, set(), 1 if cleared == 0 else 0))
            layer, cleared = layer + 1, 0; continue
        occ = sorted({divTilde[k] for k in range(numDiv) if cleared + 1 <= divTilde[k] <= wmu(d, layer) - 1})
        delta = 1 if cleared == 0 else 0
        if occ:
            target = occ[0]; f = [k for k in range(numDiv) if divTilde[k] == target][0]
            runLen = target - cleared
            pivFlat = cornerToFlat(d, birth[f][0], birth[f][1])
            cen = {pivFlat} | {(layer, r, c) for r in range(d[layer + 1]) for c in range(d[layer])
                               if r >= cleared and cleared <= c < cleared + runLen}
            edges.append(("case11", layer, cleared, pivFlat, cen, delta))
            divTilde[f] = cleared
        else:
            pivFlat = cornerToFlat(d, layer, cleared)
            cen = {(layer, r, c) for r in range(d[layer + 1]) for c in range(d[layer])
                   if r >= cleared and cleared <= c < wmu(d, layer)}
            edges.append(("case2", layer, cleared, pivFlat, cen, delta))
            divTilde.append(cleared); birth.append((layer, cleared)); numDiv += 1; cleared += 1
    return edges

# belowPivotCol / couplingCoords / couplingClear (SourceClearedResid:54-82), pivot-keyed
def belowPivotCol(pivot, coords):
    L, a, b = pivot
    return {(LL, r, c) for (LL, r, c) in coords if LL == L and c == b and r > a}
def couplingCoords(edges, coords):
    S = set()
    for (case, sL, sC, piv, cen, delta) in edges:
        if case in ("case2", "case12"):
            S |= belowPivotCol(piv, coords)
    return S
def couplingClear(edges, u, coords):
    cc = couplingCoords(edges, coords)
    return {k: (sp.Integer(0) if k in cc else u[k]) for k in u}

# ---------- the three checks ----------
def check(d, pivot_mode):
    """pivot_mode: 'oracle' (canonical, col=cleared), 'fan_offdiag' (case2 col>cleared), 'colpin' (col=cleared, row hi)."""
    N, u = dims_coords(d); coords = set(u.keys()); edges = oracle_edges(d)
    br = [e for e in edges if e[0] != "terminal"]
    br2 = []
    for e in br:
        case, sL, sC, piv, cen, delta = e
        if case == "case2" and pivot_mode == "fan_offdiag":
            cand = sorted([c for c in cen if c[1] != c[2] and c[1] >= sC and c[2] >= sC and c[2] > sC])
            if cand: piv = cand[0]
        elif case == "case2" and pivot_mode == "colpin":
            cand = sorted([c for c in cen if c[2] == sC and c[1] > sC])  # col=cleared, row high
            if cand: piv = cand[-1]
        br2.append((case, sL, sC, piv, cen, delta))
    fails = []
    for i, ed in enumerate(br2):
        case, sL, sC, piv, cen, delta = ed
        if case in ("rollover",):
            continue
        v = couplingClear(br2[:i + 1], u, coords)
        phi = canonNormalizationOf(v, d, sL, sC, piv, True)
        for k in couplingCoords(br2[:i], coords):
            if sp.expand(sp.sympify(phi.get(k, 0))) != 0:
                fails.append((i, case, piv, k, sp.expand(phi[k])))
    return fails

def run():
    ds = [(2, 2, 2, 2), (3, 3, 2, 2), (2, 3, 3, 3), (2, 2, 2, 2, 2), (3, 2, 3, 2), (2, 3, 2, 3)]
    print("=== 1. GENERAL statement (oracle pivots): case11 edges FALSIFY it ===")
    any_case11_fail = True
    for d in ds:
        f = check(d, "oracle")
        c11 = [x for x in f if x[1] == "case11"]
        print(f"  d={d}: {len(c11)} case11 failure(s)" + (f"  e.g. edge{c11[0][0]} k={c11[0][3]} -> {c11[0][4]}" if c11 else ""))
        any_case11_fail &= (len(c11) >= 1)
    assert any_case11_fail, "expected a case11 failure on every witness"

    print("\n=== 2. case2 with off-diagonal (col>cleared) fan pivot ALSO FALSIFIES it ===")
    any_fan_fail = False
    for d in [(2, 3, 3, 3), (3, 3, 3, 3), (2, 4, 4, 4)]:
        f = check(d, "fan_offdiag")
        c2 = [x for x in f if x[1] == "case2"]
        print(f"  d={d}: {len(c2)} case2 fan-pivot failure(s)" + (f"  e.g. edge{c2[0][0]} piv={c2[0][2]} k={c2[0][3]} -> {c2[0][4]}" if c2 else ""))
        any_fan_fail |= (len(c2) >= 1)
    assert any_fan_fail, "expected an off-diagonal case2 failure"

    print("\n=== 3. RESTORED under pivot.col = cleared (row FREE) -- the #87 pin ===")
    all_ok = True
    for d in [(2, 4, 4, 4), (3, 4, 4, 4), (2, 5, 5, 5), (3, 3, 3, 3)]:
        f = check(d, "colpin")
        print(f"  d={d}: {'OK (no failures)' if not f else f'STILL FAILS: {f[:2]}'}")
        all_ok &= (len(f) == 0)
    assert all_ok, "col-pin should restore truth on all witnesses"
    print("\nALL THREE CONFIRMED: general FALSE (case11 + off-diag case2); pivot.col=cleared RESTORES.")

if __name__ == "__main__":
    run()
