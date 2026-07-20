#!/usr/bin/env python3
# pnp-diag: does prod M (chartMap w) diagonalize at a leaf under the INTERIOR-ONLY alpha
# (residualSchurShear = alphaGauge), faithful to the Lean chart geoChartMapNorm = beta o S o alpha
# (source -> old). Exact symbolic. Compares against Aoyagi's FULL Q,P (Lg,Rg).
import sympy as sp

def gen(tag, m, n):
    return sp.Matrix(m, n, lambda i, j: sp.Symbol(f'{tag}{i}{j}', real=True))

# ---- the Lean chart pieces, on a single layer's cells, source -> old ----
def beta_blowup(C, piv):
    """max-modulus blow-up: pivot cell free = u; every other cell scaled by u. (Lean geoChartMap.)"""
    pi, pj = piv
    u = C[pi, pj]
    m, n = C.shape
    return sp.Matrix(m, n, lambda i, j: u if (i, j) == piv else u * C[i, j])

def alpha_interior(C, cleared):
    """INTERIOR-ONLY Schur (Lean residualSchurShear/schurCells): for interior cell (i,j) with
       i,j > cleared, C[i,j] -= C[i,cleared]*C[cleared,j].  Pivot row/col (index=cleared) UNTOUCHED
       (schurCells_snd_ne: they pass through the fold unchanged). Applied to SOURCE (before beta)."""
    m, n = C.shape
    C = C.as_mutable()
    piv = cleared
    for i in range(piv+1, m):
        for j in range(piv+1, n):
            C[i, j] = C[i, j] - C[i, piv]*C[piv, j]
    return C

def full_QP(C, cleared):
    """Aoyagi's FULL Q,P: clear pivot COL and pivot ROW too (Lg,Rg), then Schur.  Control."""
    m, n = C.shape
    C = C.as_mutable()
    piv = cleared
    p = C[piv, piv]
    # Lg: clear pivot column (rows below), full row op
    for i in range(m):
        if i != piv:
            f = C[i, piv]/p
            for j in range(n):
                C[i, j] = C[i, j] - f*C[piv, j]
    # Rg: clear pivot row (cols right), full col op
    for j in range(n):
        if j != piv:
            f = C[piv, j]/p
            for i in range(m):
                C[i, j] = C[i, j] - f*C[i, piv]
    return C

def process_layer(C, gauge, nclear):
    """Process ONE layer matrix by clearing pivots 0..nclear-1 (the layer's spine), each step:
       (source-level) gauge-clear the residual at 'cleared', then blow up the (cleared,cleared) corner.
       gauge in {'interior','fullQP'}.  Returns the OLD (transformed) layer matrix as a function of source."""
    C = C.as_mutable()
    for c in range(nclear):
        if gauge == 'interior':
            C = alpha_interior(C, c)          # alpha on source
        else:
            C = full_QP(C, c)
        C = beta_blowup(C, (c, c))            # beta: blow up the diagonal corner (pivot=diag, S=id)
    return sp.simplify(C)

def is_diag(P):
    m, n = P.shape
    return all(sp.simplify(P[i, j]) == 0 for i in range(m) for j in range(n) if i != j)

def offdiag(P):
    m, n = P.shape
    return {(i, j): sp.factor(sp.simplify(P[i, j])) for i in range(m) for j in range(n)
            if i != j and sp.simplify(P[i, j]) != 0}

def run_chain(M, gauge):
    """Build prod = C^(0)...C^(L-1) under the per-layer chart; clearing widthMinUpto per layer."""
    L = len(M)-1
    def wmin(n): return min(M[:n+1])
    Cs = []
    for s in range(L):
        C = gen(f'a{s}_', M[s], M[s+1])
        ncl = wmin(s+1)                        # pivots cleared in layer s (= running-min width)
        Cs.append(process_layer(C, gauge, ncl))
    P = Cs[0]
    for s in range(1, L):
        P = P * Cs[s]
    return sp.simplify(P)

print("="*80)
print("Q2 MECHANISM TEST: does prod diagonalize under INTERIOR-ONLY alpha (the Lean alphaGauge)?")
print("="*80)
for M in [[2,2,2], [2,2,2,2]]:
    print(f"\n--- M = {tuple(M)} ---")
    for gauge in ['interior', 'fullQP']:
        P = run_chain(M, gauge)
        d = is_diag(P)
        tag = 'INTERIOR-only alpha (Lean)' if gauge=='interior' else 'FULL Q,P (Aoyagi control)'
        print(f"  [{tag}] prod diagonal at leaf? {d}")
        if not d:
            od = offdiag(P)
            # show one surviving off-diagonal
            (ij, val) = next(iter(od.items()))
            print(f"        SURVIVING off-diag {ij} = {val}")
            print(f"        (# nonzero off-diag entries = {len(od)})")

# ---- width-drop instance: mechanism (i-a) test ----
print("\n" + "="*80)
print("Mechanism (i-a) RANK-DROP test: width-drop M=(3,2,3) — does the drop zero the cross?")
print("="*80)
for M in [[3,2,3]]:
    print(f"\n--- M = {tuple(M)} (running-min widths {[min(M[:n+1]) for n in range(len(M))]}) ---")
    P = run_chain(M, 'interior')
    d = is_diag(P)
    print(f"  [INTERIOR-only alpha] prod diagonal at leaf? {d}")
    od = offdiag(P)
    print(f"  # nonzero off-diag = {len(od)}")
    # rank ceiling = min over all = 2; row 2 should be a DROPPED (zero) row
    m, n = P.shape
    for i in range(m):
        rowzero = all(sp.simplify(P[i, j]) == 0 for j in range(n))
        print(f"    row {i}: all-zero(dropped)={rowzero}")
    # focus: cleared rows 0,1 — are their off-diagonals zero?
    print("  cleared-row off-diagonals (rows 0,1 must be diagonal for InvVal3):")
    for i in [0, 1]:
        for j in range(n):
            if i != j and sp.simplify(P[i, j]) != 0:
                print(f"    (row {i}, col {j}) = {sp.factor(P[i,j])}   <-- NONZERO off-diag in a CLEARED row")
