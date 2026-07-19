#!/usr/bin/env python3
# EXPLORATORY (not the final battery): disambiguate the geometric fold's direction + the
# case-1(2)/case-1(1) threading by DIRECT symbolic composition of max-modulus blow-up charts.
#
# Model (faithful to Lean geoChartMap): a chart is a max-modulus blow-up with center C (a set of
# flat cells) and pivot pi in C:
#     z_pi   |-> z_pi                    (pivot free)
#     z_c    |-> z_pi * z_c   (c in C, c != pi)   (other center cells scaled by pivot)
#     z_c    |-> z_c          (c not in C)         (spectators fixed)
# The path composite is fold order: chart_root ∘ ... ∘ chart_leafadj  (root OUTERMOST, applied last).
# We compute |det D(composite)| over the union of center cells and factor it.
import sympy as sp

def chart(point, center, pivot):
    """Apply one max-modulus blow-up chart to `point` (dict cell->expr)."""
    piv = point[pivot]
    out = dict(point)
    for c in center:
        if c == pivot:
            out[c] = piv
        else:
            out[c] = piv * point[c]
    return out

def compose(path, cells):
    """path = list of (center, pivot) ordered ROOT-FIRST (root=path[0]).
       Fold order: root applied LAST (outermost). So we apply the DEEPEST (last in list) first.
       Returns dict cell->expr in terms of source symbols z_<cell>."""
    src = {c: sp.Symbol('z_'+c, real=True) for c in cells}
    pt = dict(src)
    # apply innermost (deepest = path[-1]) first, up to root (path[0]) last
    for (center, pivot) in reversed(path):
        pt = chart(pt, center, pivot)
    return src, pt

def jac_det(path, cells):
    src, pt = compose(path, cells)
    order = list(cells)
    J = sp.Matrix([[sp.diff(pt[r], src[c]) for c in order] for r in order])
    return sp.factor(J.det()), src

def show(name, path, cells):
    d, src = jac_det(path, cells)
    print(f"--- {name} ---")
    for i,(center,pivot) in enumerate(path):
        print(f"   node {i} (root={i==0}): center={center} pivot={pivot}")
    print(f"   |det D composite| = {d}")
    return d, src

if __name__ == "__main__":
    # EXPERIMENT 1: depth-2, root=case-2 birth of divisor A at cell 'A' (2x2 residual block A,b,c,d),
    #   child=case-1(1) merge INTO A (pivot = A's cell), d-block of size 1x1 = {'e'}.
    # cells: A (the divisor/u-corner), b,c,d (root residual ratios), e (child d-block)
    # root center (case-2, 2x2): {A,b,c,d}, pivot A  -> births A, dCN=4, exp 4
    # child center (case-1(1)): {A, e}, pivot A       -> merge into A, dCN=2, atom exp 1
    cells1 = ['A','b','c','d','e']
    p1 = [ (['A','b','c','d'], 'A'),   # root case-2, pivot A
           (['A','e'], 'A') ]          # child case-1(1) merge into A
    d1,_ = show("EXP1 depth-2 case2(birth A)+case11(merge A)", p1, cells1)
    # expected if identity holds: A gets exp (4-1)+(2-1)=3+1=4  -> z_A^4 ; check:
    print("   expect z_A^4 (ledger: divExp(A)=4+1=5 ->  exp 4).  factor match:",
          sp.simplify(d1 - sp.Symbol('z_A',real=True)**4)==0)
    print()

    # EXPERIMENT 2: depth-2, root=case-2 birth A, child=case-1(2) SPLIT off A (new pivot 'e'),
    #   child center = {A (u-corner), e (new d-pivot)}, pivot e.  dCN=2, atom exp 1.
    cells2 = ['A','b','c','d','e']
    p2 = [ (['A','b','c','d'], 'A'),   # root case-2, pivot A, births A (exp 4)
           (['A','e'], 'e') ]          # child case-1(2): pivot e (new), scales A by e
    d2,_ = show("EXP2 depth-2 case2(birth A)+case12(split new e off A)", p2, cells2)
    # ledger: A stays exp 4 (divExp-1=3); new e exp = divExp(A)+runLen*resCols = 4+1=5 (divExp-1=4)
    # candidate ledger monomial at SOURCE w: z_A^3 * z_e^4
    zA,ze = sp.Symbol('z_A',real=True), sp.Symbol('z_e',real=True)
    print("   candidate ledger z_A^3 * z_e^4 ;  match:", sp.simplify(d2 - zA**3*ze**4)==0)
    print("   also try z_A^3 * z_e^1 (naive fresh):", sp.simplify(d2 - zA**3*ze**1)==0)
    print()

    # EXPERIMENT 3: depth-3 to see inheritance across a level.
    # root case-2 births A (2x2 {A,b,c,d}); child case-1(2) splits e off A ({A,e} pivot e);
    # grandchild case-1(1) merges into e ({e,f} pivot e).
    cells3 = ['A','b','c','d','e','f']
    p3 = [ (['A','b','c','d'], 'A'),
           (['A','e'], 'e'),
           (['e','f'], 'e') ]
    d3,_ = show("EXP3 depth-3 case2(A)+case12(e off A)+case11(merge e)", p3, cells3)
    print()
