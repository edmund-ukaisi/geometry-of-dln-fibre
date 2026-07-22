"""
THE EMPIRICAL INVARIANT TABLE (pnp-transport, for the elder's consolidated carried-invariant ruling).

Computes foldResid at EVERY node of the real (canonical) branch for two witnesses:
  (2,2,2,2)  — the standard NON-WIDE reference,
  (2,3,2,2)  — the smallest WIDE-with-descent (d_1=3 > widthMinUpto(0)=2).
Per residual slot, at each node, we record (recording what is TRUE, defect rows included):
  (i)   the EXACT monomial support (flat coords appearing LINEARLY), flagged in-cap vs out-of-cap
        (blockCoords(supportLayer) = {layer, col < widthMinUpto} vs layerCoords = {layer, any col});
  (ii)  the FACTORING of each EXTRA-BLOCK coefficient: does it vanish at the relevant BIRTH pivot's
        u = 0 (the b-chain, as it actually appears)? which pivot?
  (iii) per-layer total degrees (the PerLayerDeg1From grade).

MODEL: the `canonShearOf` fold (blockBlowupMap/quotient . canonShearOf) — the SAME model the
transport-table certificate rides on (unambiguous; no recoord-direction modelling). The FAITHFUL
(N_p, with the deeper recoord) difference at the boost/descent nodes is computed separately below
(the b-chain the current model lacks). coreGen = entries of A_{N-1}...A_1 A_0 (last layer leftmost).
"""
import sympy as sp

# ---------------- flat coords, coreGen ----------------
def build(d):
    N = len(d) - 1
    u = {}
    for L in range(N):
        for r in range(d[L + 1]):
            for c in range(d[L]):
                u[(L, r, c)] = sp.Symbol(f"u{L}{r}{c}")
    return N, u

def mat(u, d, L):
    return sp.Matrix(d[L + 1], d[L], lambda r, c: u[(L, r, c)])

def coreGen(u, d):
    N = len(d) - 1
    M = mat(u, d, N - 1)
    for L in range(N - 2, -1, -1):
        M = M * mat(u, d, L)
    return [M[i, j] for i in range(M.rows) for j in range(M.cols)]

def widthMinUpto(d, n):
    N = len(d) - 1
    return min(d[i] for i in range(0, min(n, N - 1) + 1))

# ---------------- fold maps (canonShearOf model) ----------------
def canonShear(u, d, s_layer, s_cleared):
    """+phi: interior (layer=s_layer, row>cleared, col>cleared) gets -u_gamma*u_beta."""
    out = dict(u)
    N = len(d) - 1
    if s_layer < N:
        for r in range(d[s_layer + 1]):
            for c in range(d[s_layer]):
                if r > s_cleared and c > s_cleared:
                    out[(s_layer, r, c)] = (u[(s_layer, r, c)]
                                            - u[(s_layer, r, s_cleared)] * u[(s_layer, s_cleared, c)])
    return out

def apply_edge(u, d, case, s_layer, s_cleared, pivot, center, delta):
    """returns the coords coreGen reads at the CHILD (foldResid child = coreGen(this))."""
    w = u if case in ("case11", "rollover") else canonShear(u, d, s_layer, s_cleared)
    out = {}
    for k in u:
        if case == "rollover":
            out[k] = w[k]
        elif delta == 1:            # quotient: pivot -> 1, else shear value
            out[k] = sp.Integer(1) if k == pivot else w[k]
        else:                        # delta 0: blockBlowupMap(center,pivot)
            if k == pivot:
                out[k] = w[pivot]
            elif k in center:
                out[k] = w[pivot] * w[k]
            else:
                out[k] = w[k]
    return out

def compose_to_node(u, d, edges):
    """foldResid(node)(u) = coreGen(map_e1(map_e2(...map_en(u)))), e1 outermost => applied last."""
    v = dict(u)
    for (case, sl, sc, piv, cen, delta) in reversed(edges):
        v = apply_edge(v, d, case, sl, sc, piv, cen, delta)
    return coreGen(v, d)

# ---------------- per-slot analysis ----------------
def layer_of(coord):
    return coord[0]

def analyse(f, u, d, support_layer, birth_pivots):
    """returns (support coords, out-of-cap coords, per-layer degrees, extra-block factoring)."""
    f = sp.expand(f)
    fs = f.free_symbols
    # support = coords appearing (in the support layer, linearly); flag in/out of cap
    wmu = widthMinUpto(d, support_layer)
    support, outcap = [], []
    for coord, sym in u.items():
        if sym in fs and coord[0] == support_layer:
            support.append(coord)
            if coord[2] >= wmu:          # col >= widthMinUpto => OUT-OF-CAP
                outcap.append(coord)
    # per-layer total degree
    N = len(d) - 1
    degs = {}
    for L in range(N):
        layersyms = [u[(L, r, c)] for r in range(d[L + 1]) for c in range(d[L]) if u[(L, r, c)] in fs]
        degs[L] = 0 if not layersyms else max(sum(m) for m in sp.Poly(f, *layersyms).monoms())
    # extra-block coefficient factoring: for each support coord in the support layer, its coeff;
    # does it vanish at each birth pivot's u=0?
    fac = {}
    for coord in support:
        coeff = sp.expand(f.coeff(u[coord], 1))
        vanish = {}
        for name, pv in birth_pivots.items():
            if pv in u:
                vanish[name] = (sp.expand(coeff.subs(u[pv], 0)) == 0)
        fac[coord] = vanish
    return support, outcap, degs, fac

# ---------------- table driver ----------------
def run(d, branch, child_states, runlens, label, birth_pivots):
    print("=" * 78)
    print(f"WITNESS {label}: d={d}   (widthMinUpto(0)={widthMinUpto(d,0)}, widthMinUpto(1)={widthMinUpto(d,1)})")
    N, u = build(d)
    print(f"  birth pivots (reused-divisor birth corners): { {k: v for k,v in birth_pivots.items()} }")
    for ni in range(len(branch) + 1):
        edges = branch[:ni]
        clayer, ccleared = child_states[ni]
        sl = clayer if ccleared == 0 else clayer + 1     # supportLayerOf(child state)
        wmu = widthMinUpto(d, sl)
        runLen = runlens[ni]                             # for a case11 boost node: extraBlock = col >= runLen
        node_state = "root" if ni == 0 else f"after {branch[ni-1][0]}(L{branch[ni-1][1]},cl{branch[ni-1][2]},d={branch[ni-1][5]})"
        resid = compose_to_node(u, d, edges)
        print(f"\n  NODE {ni}: {node_state}  |  child state (L{clayer},cl{ccleared}), supportLayer={sl}, "
              f"widthMinUpto={wmu}" + (f", runLen={runLen}" if runLen is not None else ""))
        for j, f in enumerate(resid):
            fe = sp.expand(f)
            if fe == 1:
                print(f"    slot {j}: = 1 (terminal/unit)"); continue
            support, outcap, degs, fac = analyse(fe, u, d, sl, birth_pivots)
            cols = sorted(set(c for (a, b, c) in support))
            oc = "  **OUT-OF-CAP** " + str([f"(L{a},r{b},c{c})" for (a, b, c) in outcap]) if outcap else ""
            print(f"    slot {j}: support-layer-{sl} cols {cols}{oc}; per-layer deg {degs}")
            # b-chain: for extra-block support coords (col >= runLen if a boost node, else all), the coeff
            for coord in support:
                is_extra = (runLen is None) or (coord[2] >= runLen)
                divs = [nm for nm, vv in fac[coord].items() if vv]
                tag = " [EXTRA-block]" if (runLen is not None and coord[2] >= runLen) else ""
                if divs:
                    print(f"        coeff of u{coord[0]}{coord[1]}{coord[2]}{tag}: vanishes at u=0 of {divs}")
                elif runLen is not None and coord[2] >= runLen:
                    print(f"        coeff of u{coord[0]}{coord[1]}{coord[2]}{tag}: does NOT vanish at any birth pivot "
                          f"(b-chain ABSENT — the 'form too weak' defect)")

# (2,2,2,2): branch (case, layer, cleared, pivot, center, delta)
d1 = (2, 2, 2, 2)
_, u1 = build(d1)
br1 = [
    ("case2", 0, 0, (0, 0, 0), set(), 1),
    ("case2", 0, 1, (0, 1, 1), {(0, 1, 1)}, 0),
    ("rollover", 0, 2, None, set(), 0),
    ("case11", 1, 0, (0, 1, 1), {(0, 1, 1), (1, 0, 0), (1, 1, 0)}, 1),
]
# child state (layer,cleared) at each node; runLen at the case11 boost PARENT (node 3) = 1
cs1 = [(0, 0), (0, 1), (0, 2), (1, 0), (1, 0)]
rl1 = [None, None, None, 1, None]     # node 3 = boost parent (case11 fires from here), extraBlock = col >= 1
run(d1, br1, cs1, rl1, "(2,2,2,2)", {"div0@(0,0,0)": (0, 0, 0), "div1@(0,1,1)": (0, 1, 1)})

# (2,3,2,2): A_0=3x2, A_1=2x3, A_2=2x2. layer-0 wide (d_1=3 > wMU(0)=2). branch: case2 x2 (clear layer0), rollover, ...
d2 = (2, 3, 2, 2)
br2 = [
    ("case2", 0, 0, (0, 0, 0), set(), 1),
    ("case2", 0, 1, (0, 1, 1), {(0, 1, 1), (0, 2, 1)}, 0),   # 2nd clear; center = the running-min block at cleared1
    ("rollover", 0, 2, None, set(), 0),
]
cs2 = [(0, 0), (0, 1), (0, 2), (1, 0)]
rl2 = [None, None, None, None]        # layer-0 clears + rollover (the descent to layer 1); no case11 here
run(d2, br2, cs2, rl2, "(2,3,2,2)", {"div0@(0,0,0)": (0, 0, 0), "div1@(0,1,1)": (0, 1, 1)})
