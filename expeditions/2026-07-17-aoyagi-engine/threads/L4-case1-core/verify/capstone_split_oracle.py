"""
CAPSTONE SPLIT — ORACLE-DRIVEN, FULL 3-BRANCH RENDER (pnp-transport, task #68).

Definitive experiment.  Prior scripts used (a) raw coreGen [frame-wrong] or (b) a simplified
interior-only shear [render-wrong].  This one:
  * DRIVES THE ORACLE (npivot_bchain_M.py logic) to get the REAL canonical branch — so the
    case11 edge and its parent path are the construction's, not hand-written;
  * composes foldResid(parent) with the FULL 3-branch canonNormalizationOf (MonumentAtlas:906-966,
    scoped), including branch-(ii) [+γ output recoord into layer S+1] and branch-(iii) [Q₂⁻¹ input];
  * for the case11 child, computes e₂=canonPivotOf, center=canonCenterOf(case11),
    part=supportAt∩center, extra=supportAt∖center, and SEARCHES which single e₂ the extra factors
    through (across ALL slots) — reconciling the empirical e₂ with the def's canonPivotOf.
"""
import sympy as sp
from itertools import count

# ================= flat coords, render, coreGen =================
def dims_coords(d):
    N = len(d) - 1
    u = {(L, r, c): sp.Symbol(f"u_{L}_{r}_{c}") for L in range(N)
         for r in range(d[L + 1]) for c in range(d[L])}
    return N, u

def readEntry(u, d, S, row, col):
    N = len(d) - 1
    return u[(S, row, col)] if (0 <= S < N and 0 <= row < d[S + 1] and 0 <= col < d[S]) else sp.Integer(0)

def canonNormalizationOf(u, d, S, cleared, piv, scoped=True):
    """EXACT rendered 3-branch def (MonumentAtlas:906-966). piv=(layer,a,b)."""
    a, b = piv[1], piv[2]
    lo = cleared if scoped else 0
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
    if case in ("case11", "rollover"):
        w = dict(u)
    else:
        phi = canonNormalizationOf(u, d, sL, sC, piv, scoped)
        w = {k: u[k] + phi[k] for k in u}
    out = {}
    for k in u:
        if case == "rollover":
            out[k] = w[k]
        elif delta == 1:
            out[k] = sp.Integer(1) if k == piv else w[k]
        else:
            out[k] = (w[piv] if k == piv else (w[piv] * w[k] if k in cen else w[k]))
    return out

def foldResid_parent(u, d, parent_edges, scoped=True):
    v = dict(u)
    for e in reversed(parent_edges):
        v = apply_edge(v, d, *e, scoped)
    return coreGen(v, d)

# ================= geometry =================
def widthMinUpto(d, n):
    N = len(d) - 1
    return min(d[i] for i in range(0, min(n, N - 1) + 1))

def cornerToFlat(d, S, J):                 # diagonal corner (S,J,J)
    return (S, J, J)

def blockCoords(d, S):
    wmu = widthMinUpto(d, S)
    return {(S, r, c) for r in range(d[S + 1]) for c in range(d[S]) if c < wmu}

def layerCoords(d, S):
    return {(S, r, c) for r in range(d[S + 1]) for c in range(d[S])}

def supportAt(d, S, J):
    N = len(d) - 1
    if J == 0:
        return blockCoords(d, S)
    elif S + 1 < N:
        return layerCoords(d, S + 1)
    return set()

def canonCenter_case2(d, S, J):
    wmu = widthMinUpto(d, S)
    return {(S, r, c) for r in range(d[S + 1]) for c in range(d[S]) if r >= J and J <= c < wmu}

def canonCenter_case11(d, S, J, runLen, pivotFlat):
    part = {(S, r, c) for r in range(d[S + 1]) for c in range(d[S]) if r >= J and J <= c < J + runLen}
    return {pivotFlat} | part

# ================= the ORACLE (npivot_bchain_M.py logic), emitting FULL edges =================
def oracle_edges(d):
    """Returns the ordered list of edges (case, layer, cleared_before, pivotFlat, center, delta)
       plus per-edge metadata (target/runLen/f for case11)."""
    N = len(d) - 1
    Lmax = N - 1
    layer, cleared, numDiv = 0, 0, 0
    divTilde, birth = [], []
    edges = []
    meta = []
    for _ in range(200):
        if Lmax <= layer:
            edges.append(("terminal", layer, cleared, None, set(), 0)); meta.append({}); break
        if widthMinUpto(d, layer + 1) <= cleared:
            edges.append(("rollover", layer, cleared, None, set(), 1 if cleared == 0 else 0)); meta.append({})
            layer, cleared = layer + 1, 0; continue
        occ = sorted({divTilde[k] for k in range(numDiv)
                      if cleared + 1 <= divTilde[k] <= widthMinUpto(d, layer) - 1})
        delta = 1 if cleared == 0 else 0
        if occ:
            target = occ[0]; runLen = target - cleared
            f = [k for k in range(numDiv) if divTilde[k] == target][0]
            pivFlat = cornerToFlat(d, birth[f][0], birth[f][1])
            cen = canonCenter_case11(d, layer, cleared, runLen, pivFlat)
            edges.append(("case11", layer, cleared, pivFlat, cen, delta))
            meta.append(dict(target=target, runLen=runLen, f=f, birth_f=birth[f], pivFlat=pivFlat))
            divTilde[f] = cleared
            # NOTE: case11 KEEPS cleared (does not advance); to make the branch finite we advance
            # the oracle past it only for TRACE purposes — but for the WITNESS we stop at the FIRST
            # case11 and split foldResid(parent).  Here we continue by advancing cleared to avoid a loop.
            cleared += runLen if runLen > 0 else 1
        else:
            pivFlat = cornerToFlat(d, layer, cleared)
            cen = canonCenter_case2(d, layer, cleared)
            edges.append(("case2", layer, cleared, pivFlat, cen, delta))
            meta.append(dict(M=(widthMinUpto(d, layer) - cleared) * (d[layer + 1] - cleared)))
            divTilde.append(cleared); birth.append((layer, cleared)); numDiv += 1; cleared += 1
    return edges, meta

# ================= split search =================
def analyse_case11(d, label):
    print("=" * 84)
    print(f"WITNESS {label}: d={d}")
    N, u = dims_coords(d)
    edges, meta = oracle_edges(d)
    # find FIRST case11 edge
    idx = next((i for i, e in enumerate(edges) if e[0] == "case11"), None)
    if idx is None:
        print("  no case11 in canonical branch — skip"); return None
    ce = edges[idx]; cm = meta[idx]
    parent_edges = edges[:idx]
    S, J = ce[1], ce[2]
    e2 = ce[3]                                  # canonPivotOf = reused divisor's birth corner
    center = ce[4]
    support = supportAt(d, S, J)
    part = support & center
    extra = support - center
    print(f"  branch to parent: {[(e[0], e[1], e[2]) for e in parent_edges]}")
    print(f"  case11 edge: layer S={S}, cleared J={J}, runLen={cm['runLen']}, reused f={cm['f']} born {cm['birth_f']}")
    print(f"  e₂=canonPivotOf={e2}, center={sorted(center)}")
    print(f"  support(=supportAt {S},{J})={sorted(support)}")
    print(f"  part={sorted(part)}  extra={sorted(extra)}")
    assert e2 in center and e2 not in part and not (extra & center), "index-set sanity FAILED"

    fr = foldResid_parent(u, d, parent_edges, scoped=True)
    support_syms = {u[c] for c in support}

    # per-slot: c_i = coeff of u_i (linear in support); collect for extra the set of coords each c_i factors through
    print("  -- per-slot coefficient structure (extra coords only) --")
    per_slot_divs = []          # for each slot, dict extra-coord -> set of single coords dividing c_i
    lin_all = True
    for j, f in enumerate(fr):
        fe = sp.expand(f)
        if fe == 0 or fe == 1:
            continue
        recon = sum((sp.expand(fe.coeff(u[i], 1)) * u[i] for i in support), sp.Integer(0))
        lin = sp.expand(fe - recon) == 0
        lin_all = lin_all and lin
        divs = {}
        for i in extra:
            ci = sp.expand(fe.coeff(u[i], 1))
            # which single coords g satisfy ci|u_g (i.e. ci.subs(u_g,0)==0)?
            gdiv = {k for k in u if sp.expand(ci.subs(u[k], 0)) == 0 and ci != 0}
            divs[i] = gdiv
        per_slot_divs.append(divs)
    # intersect over all slots and all extra coords: which single g divides EVERY extra coeff?
    common = None
    for divs in per_slot_divs:
        for i, gd in divs.items():
            common = gd if common is None else (common & gd)
    common = common or set()
    common_flat = sorted(k for k in common)
    print(f"  linear-in-support (all slots): {lin_all}")
    print(f"  single coords dividing EVERY extra coefficient across ALL slots: {common_flat}")
    print(f"  is canonPivotOf={e2} among them? {e2 in common}")
    return dict(e2=e2, center=center, part=part, extra=extra, common=common_flat, lin=lin_all)

if __name__ == "__main__":
    for d in [(2, 2, 2, 2), (3, 3, 2, 2)]:
        analyse_case11(d, str(d))
