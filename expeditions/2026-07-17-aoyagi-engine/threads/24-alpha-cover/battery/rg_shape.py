#!/usr/bin/env python3
# pnp-rg (thread 24): the COMPLETED alpha (interior Schur + pivot-col Lg + pivot-row Rg) and the
# cross-layer Rg SHAPE. Two questions:
#   (b) does the completed alpha make prod EXACTLY diagonal at a leaf (the fix works)?
#   (c) which C^{(S+1)} coords does each edge's Rg WRITE, and do consecutive edges OVERLAP?
# Exact symbolic (sympy). Builds on pnp-diag's VERIFIED chart primitives (diag_mech.py): beta_blowup
# (max-modulus, geoChartMap) + alpha_interior (residualSchurShear, the Lean gauge). MC never used.
#
# Faithful chart model (source -> old), full params = ALL layers' cells (so cross-layer writes are
# representable, exactly as the Lean alphaGauge : GeoChart -> Params -> Params acts on all flat coords).
import sympy as sp

# ----------------------------------------------------------------------------------------------
# Params = dict keyed (s,i,j) over all layers; a layer matrix is a view.
# ----------------------------------------------------------------------------------------------
def init_params(M):
    L = len(M) - 1
    P = {}
    for s in range(L):
        for i in range(M[s]):
            for j in range(M[s+1]):
                P[(s, i, j)] = sp.Symbol(f'a{s}_{i}{j}', real=True)
    return P

def layer_mat(P, M, s):
    return sp.Matrix(M[s], M[s+1], lambda i, j: P[(s, i, j)])

def prod_of(P, M):
    L = len(M) - 1
    Pr = layer_mat(P, M, 0)
    for s in range(1, L):
        Pr = Pr * layer_mat(P, M, s)
    return sp.simplify(Pr)

def is_diag(Pr):
    m, n = Pr.shape
    return all(sp.simplify(Pr[i, j]) == 0 for i in range(m) for j in range(n) if i != j)

def offdiag(Pr):
    m, n = Pr.shape
    return {(i, j): sp.factor(sp.simplify(Pr[i, j]))
            for i in range(m) for j in range(n) if i != j and sp.simplify(Pr[i, j]) != 0}

# ----------------------------------------------------------------------------------------------
# Per-node source->old maps on full params. Each returns (newP, writeset). writeset = coords written.
# ----------------------------------------------------------------------------------------------
def beta_blowup(P, M, s, c):
    """max-modulus blow-up of layer s at corner (c,c): pivot cell free = u; every other layer-s cell
       scaled by u. (Lean geoChartMap; pnp-diag beta_blowup, extended to full params.)"""
    u = P[(s, c, c)]
    newP = dict(P)
    writ = set()
    for i in range(M[s]):
        for j in range(M[s+1]):
            if (i, j) == (c, c):
                continue
            newP[(s, i, j)] = u * P[(s, i, j)]
            writ.add((s, i, j))
    return newP, writ

def alpha_interior(P, M, s, c):
    """INTERIOR-only Schur (Lean residualSchurShear): interior (i,j), i,j>c: -= (i,c)*(c,j). SAME layer."""
    newP = dict(P)
    writ = set()
    for i in range(c+1, M[s]):
        for j in range(c+1, M[s+1]):
            newP[(s, i, j)] = P[(s, i, j)] - P[(s, i, c)] * P[(s, c, j)]
            writ.add((s, i, j))
    return newP, writ

def alpha_Lg(P, M, s, c):
    """pivot-COLUMN clear (Aoyagi Lg-remainder), SAME layer: row op clearing col c below corner.
       for i>c: row_i -= (a[i,c]/a[c,c]) row_c  (over cols c..).  Includes the interior update, so
       the completed same-layer part = Lg (which SUBSUMES alpha_interior). Corner a[c,c] kept."""
    newP = dict(P)
    writ = set()
    p = P[(s, c, c)]
    for i in range(c+1, M[s]):
        f = P[(s, i, c)] / p
        for j in range(c, M[s+1]):
            newP[(s, i, j)] = P[(s, i, j)] - f * P[(s, c, j)]
            writ.add((s, i, j))
    return newP, writ

def alpha_Rg_crosslayer(P, M, s, c):
    """pivot-ROW clear (Aoyagi Rg), CROSS-LAYER. Rg is a col op on layer s clearing row c (cols j>c):
         col_j -= (a[c,j]/a[c,c]) col_c   (right-mult layer s by R, |det R|=1)
       compensated by C^{(s+1)} -> R^{-1} C^{(s+1)} (left-mult, row op on layer s+1):
         row_c(C^{s+1}) += sum_{j>c} (a[c,j]/a[c,c]) row_j(C^{s+1}).
       Returns writes to BOTH layer s (its own pivot row) and layer s+1 (the compensation)."""
    newP = dict(P)
    writ = set()
    p = P[(s, c, c)]
    # coefficients f_j read from layer s (BEFORE clearing), j>c
    f = {j: P[(s, c, j)] / p for j in range(c+1, M[s+1])}
    # (i) clear layer-s pivot row (cols j>c): col op on layer s
    for j in range(c+1, M[s+1]):
        for i in range(M[s]):
            newP[(s, i, j)] = P[(s, i, j)] - f[j] * P[(s, i, c)]
            writ.add((s, i, j))
    # (ii) compensation on layer s+1 (if it exists): row c += sum_{j>c} f_j row_j
    if s + 1 < len(M) - 1:
        for k in range(M[s+2]):
            add = sum(f[j] * P[(s+1, j, k)] for j in range(c+1, M[s+1]))
            newP[(s+1, c, k)] = P[(s+1, c, k)] + add
            writ.add((s+1, c, k))
    return newP, writ

# ----------------------------------------------------------------------------------------------
# The spine (root->leaf) of the layer-0..L-1 clearing, then compose LEAF-FIRST (tree order:
# root = first blow-up = applied LAST; deepest = applied FIRST). Each node = (S, c).
# ----------------------------------------------------------------------------------------------
def spine(M):
    """root->leaf list of (S,c) nodes. Layer S cleared over c=0..wmin(S+1)-1, then rollover to S+1.
       Layer 0 pivot 0 is the ROOT; deepest node is the LEAF."""
    L = len(M) - 1
    def wmin(n): return min(M[:n+1])
    nodes = []
    for S in range(L):
        for c in range(wmin(S+1)):
            nodes.append((S, c))
    return nodes

def build_chart(M, node_map, order_mode="leaf_first"):
    """Compose node maps. order_mode: 'leaf_first' = deepest applied FIRST to source (tree source->leaf
       composition; root=first-blowup applied LAST); 'root_first' = the reverse (Aoyagi's reduction order:
       layer 0 processed first). node_map(P,M,S,c) -> (newP, writeset)."""
    P = init_params(M)
    sp_nodes = spine(M)
    order = list(reversed(sp_nodes)) if order_mode == "leaf_first" else list(sp_nodes)
    writesets = {}
    for (S, c) in order:
        P, w = node_map(P, M, S, c)
        writesets[(S, c)] = w
    return P, writesets

# node maps: interior-only (Lean) vs completed (Lg + cross-layer Rg), each with beta.
def node_interior(P, M, S, c):
    w = set()
    P, w1 = alpha_interior(P, M, S, c); w |= w1
    P, w2 = beta_blowup(P, M, S, c);    w |= w2
    return P, w

def node_completed(P, M, S, c):
    w = set()
    P, w1 = alpha_Lg(P, M, S, c);            w |= w1   # same-layer: interior Schur + pivot-col
    P, w2 = alpha_Rg_crosslayer(P, M, S, c); w |= w2   # cross-layer: pivot-row -> C^{(S+1)}
    P, w3 = beta_blowup(P, M, S, c);         w |= w3
    return P, w

if __name__ == "__main__":
    for M in [[2, 2, 2], [2, 2, 2, 2]]:
        print("=" * 84)
        print(f"M = {tuple(M)}   spine (root->leaf) = {spine(M)}")
        print("=" * 84)
        for tag, nm in [("INTERIOR-only (Lean alphaGauge)", node_interior),
                        ("COMPLETED alpha (Lg + cross-layer Rg)", node_completed)]:
            for om in ["leaf_first", "root_first"]:
                P, ws = build_chart(M, nm, om)
                Pr = prod_of(P, M)
                d = is_diag(Pr)
                print(f"\n  [{tag}] [{om}] prod diagonal at leaf? {d}")
                if not d:
                    od = offdiag(Pr)
                    (ij, v) = next(iter(od.items()))
                    print(f"      surviving off-diag {ij} = {v}   (# nonzero off-diag = {len(od)})")
                else:
                    print(f"      diagonal = {[sp.factor(Pr[i,i]) for i in range(min(Pr.shape))]}")
