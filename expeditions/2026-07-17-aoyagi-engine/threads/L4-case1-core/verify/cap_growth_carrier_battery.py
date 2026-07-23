"""
GROWTH-V3 CARRIER — fidelity battery (measured-pace, precision-first).

Before formulating the descent carrier for seat-descent, STRESS-TEST whether the multi-layer ∏A descent
actually bottoms out cleanly on configs pnp-transport's witnesses did NOT exercise:
  * d_0 > wmu(1)  (layer 0 has UNCLEARED output cols — the recursion could hit A_0[·,k≥wmu(1)] with no
    layer -1 to recurse into);
  * interior wmu drops / multiple consecutive wide layers (deep recursion).

For each interior layer S, build the REAL diagonal branch to the last clear of layer S (the child node
where escapedCol(S+1) enters), compute the REAL foldResid (blow-ups + shears), and check: every escaped
layer-(S+1) coefficient is killed by couplingClear over the ACCUMULATED all-layer couplingCoords.

couplingClear (capstone §0 / #82): for each ancestor clear of diagonal pivot (a,b) at layer L,
zero u_(L,r,b) for r>a.  Accumulated = union over all clears so far.

Exit 0 = the carrier holds on EVERY witness/interior-layer (⟹ formulate it). A SURVIVOR ⟹ statement-class
gap pnp-transport's witnesses missed ⟹ STOP + report.
"""
import sympy as sp
from cap_frontier_sufficiency import make, widthMinUpto, layerCoords, real_foldResid

def cc(d, S, J):   # canonCenterOf case2/case12
    cap = widthMinUpto(d, S)
    return {(L, r, c) for (L, r, c) in make(d)[1] if L == S and J <= r and J <= c and c < cap}

def branch_to_last_clear(d, S):
    """Real diagonal branch: clear layers 0..S-1 fully (wmu(L+1) pivots each) + rollover, then clear
       layer S up to its last pivot (col wmu(S+1)-1). Returns edges (root-first) + cleared pivot list."""
    edges = []; pivots = []
    for L in range(S + 1):
        nclear = widthMinUpto(d, L + 1)          # pivots cleared in layer L
        last = nclear if L < S else nclear       # clear all in layers <S; in layer S clear all too
        for J in range(nclear):
            delta = 1 if (L, J) != (L, 0) or True and J == 0 else 0
            delta = 1 if J == 0 else 0            # δ = [cleared==0]
            piv = (L, J, J)
            edges.append(("case2", L, J, piv, cc(d, L, J), delta))
            pivots.append(piv)
        if L < S:
            edges.append(("rollover", L, nclear, (L + 1, 0, 0), set(), 0))
    return edges, pivots

def couplingCoords(d, pivots):
    S = set()
    for (pL, pa, pb) in pivots:
        S |= {(pL, r, pb) for r in range(d[pL + 1]) if r > pa}
    return S

def check(d):
    N = len(d) - 1
    results = []
    for S in range(N - 1):                        # interior: escaped at S+1 must be a real layer (S+1 < N)
        wmuS1 = widthMinUpto(d, S + 1)
        escaped = sorted(k for k in make(d)[1] if k[0] == S + 1 and k[2] >= wmuS1)
        if not escaped:                            # no escaped col at S+1 (d_{S+1} = wmu(S+1))
            continue
        edges, pivots = branch_to_last_clear(d, S)
        N2, u = make(d)
        resid = real_foldResid(u, d, edges)
        cpl = couplingCoords(d, pivots)
        zc = {u[k]: 0 for k in cpl}
        survivors = []
        for j, f in enumerate(resid):
            f = sp.expand(f)
            for m in escaped:
                cm = sp.expand(f.coeff(u[m], 1))
                if cm != 0 and sp.expand(cm.subs(zc)) != 0:
                    survivors.append((j, m, sp.expand(cm.subs(zc))))
        d0_wide = d[0] > wmuS1 if False else d[0] > widthMinUpto(d, 1)
        results.append((S, len(escaped), len(survivors), survivors,
                        d[S] > wmuS1, d[0] > widthMinUpto(d, 1)))
    return results

WITNESSES = [
    (2, 3, 3, 3),   # pnp-transport control (d0=2=wmu1)
    (3, 2, 3, 3),   # d0=3>wmu1=2: layer 0 has uncleared output col
    (3, 4, 4, 4),   # 2-level recursion (layer1->layer0), layer0 full (d0=3=wmu1)
    (3, 4, 4, 2),   # d0=3=wmu1 but wide interior
    (4, 3, 4, 4),   # d0=4>wmu1=3: layer 0 uncleared cols, wide interior
    (3, 5, 5, 5),   # d0=3, wide interior (deep recursion candidate)
    (2, 4, 4, 4, 4),  # N=4: S=2 last clear ⟹ depth-3 recursion (layer2->1->0)
    (3, 4, 4, 4, 4),  # N=4, d0=3: depth-3 recursion with d0>wmu1 at the bottom
]
allok = True
for d in WITNESSES:
    res = check(d)
    for (S, nesc, nsurv, survs, dS_wide, d0_wide) in res:
        tag = f"d0>wmu1={d0_wide}, d[S]>wmu(S+1)={dS_wide}"
        print(f"d={d} last-clear S={S}: escaped={nesc}, survivors={nsurv}  [{tag}]")
        if nsurv:
            allok = False
            for (j, m, ex) in survs[:3]:
                print(f"    SURVIVOR slot{j} u_{m}: {ex}")
print(f"\nCarrier holds on every witness/interior-layer? {allok}")
if not allok:
    print("*** STATEMENT-CLASS GAP — the descent does NOT bottom cleanly on some config; STOP + report ***")
else:
    print("OK: every escaped coeff ∈ ⟨accumulated all-layer couplingCoords⟩ — carrier is sound; formulate it.")
