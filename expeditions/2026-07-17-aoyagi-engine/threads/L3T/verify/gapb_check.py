import sympy as sp
from itertools import product

def build(d):
    # d = (d_0,...,d_N). Layer l = matrix A_{l+1}: d_{l+1} rows x d_l cols, l=0..N-1
    N = len(d)-1
    A = []
    coords = {}   # (layer, row, col) -> symbol
    for l in range(N):
        rows, cols = d[l+1], d[l]
        M = sp.zeros(rows, cols)
        for i in range(rows):
            for j in range(cols):
                s = sp.Symbol(f"a{l}_{i}_{j}")
                M[i,j] = s
                coords[(l,i,j)] = s
        A.append(M)
    # product A_N ... A_1  => A[N-1]*...*A[0]
    P = A[-1]
    for l in range(N-2,-1,-1):
        P = P*A[l]
    return N, A, coords, P

def widthMinUpto(d, l):
    return min(d[:l+2][:l+1]) if False else min(d[i] for i in range(l+1))  # min(d_0..d_l)

def layer_syms(coords, l):
    return [s for (ll,i,j),s in coords.items() if ll==l]

def block_syms(coords, l, wmu):
    return [s for (ll,i,j),s in coords.items() if ll==l and j < wmu]

def check(d):
    N, A, coords, P = build(d)
    t = sp.Symbol('t')
    entries = [P[i,j] for i in range(P.rows) for j in range(P.cols)]
    print(f"d={d}  N={N}  coreGen entries (product {P.rows}x{P.cols}):")
    for e in entries:
        print("   ", sp.expand(e))
    for l in range(N):
        wmu = min(d[i] for i in range(l+1))   # min(d_0..d_l)
        ls = layer_syms(coords,l); bs = block_syms(coords,l,wmu)
        # homogeneity over layerCoords: substitute each layer sym s -> t*s
        subL = {s: t*s for s in ls}
        subB = {s: t*s for s in bs}
        # vanishing: set layer syms to 0
        zL = {s:0 for s in ls}; zB={s:0 for s in bs}
        homL = all(sp.simplify(sp.expand(e.subs(subL)) - t*sp.expand(e)) == 0 for e in entries)
        vanL = all(sp.simplify(e.subs(zL))==0 for e in entries)
        # blockCoords: check if homogeneous deg1 AND vanishing
        homB = all(sp.simplify(sp.expand(e.subs(subB)) - t*sp.expand(e)) == 0 for e in entries)
        vanB = all(sp.simplify(e.subs(zB))==0 for e in entries)
        capBites = (wmu < d[l])  # blockCoords strictly smaller than layerCoords
        print(f"  layer {l}: widthMinUpto={wmu} d_l={d[l]} capBites={capBites} "
              f"| layerCoords: homog1={homL} vanish={vanL} "
              f"| blockCoords: homog1={homB} vanish={vanB}")
        if not vanB:
            # show a surviving term
            for e in entries:
                r = sp.expand(e.subs(zB))
                if r != 0:
                    print(f"      -> zeroing blockCoords leaves nonzero: {r}")
                    break

for d in [(1,2,1),(1,2,2),(2,3,1),(2,2,2),(1,3,2,1),(2,1,2)]:
    check(d)
    print()
