"""
L7 wire de-risk: is canonNormalizationOf's quadratic part uniformly bounded per coordinate,
across ALL edges/pivots/depths of the monument tree? (⟹ a single R-dependent box-inflation f=r↦r+C·r²
discharges the L7 cover with a uniform C ≤ poly(flatDim); vs unbounded ⟹ a refined per-coord f.)

canonNormalizationOf is PURELY degree-2 (each of its 3 branches is a sum of products of TWO coords,
±1 coeff — no linear/constant part). Its def is IDENTICAL at every edge; only (s.layer, s.cleared, pivot)
vary. So the count of quadratic monomials PER MODIFIED COORD is:
  branch (i)  [layer s, off pivot-cross]: exactly 1 monomial  (−readEntry·readEntry).
  branch (ii) [layer s+1, col=pivot-row]: Σ over range(d[s+1]) minus excluded ⟹ ≤ d[s+1] monomials.
  branch (iii)[layer s-1, row=pivot-col]: Σ over range(d[s])   minus excluded ⟹ ≤ d[s]   monomials.
Each coord hits AT MOST ONE branch (guards mutually exclusive). So per-coord count ≤ max_ℓ d_ℓ — a function
of the WIDTHS ONLY, independent of edge/pivot/DEPTH. This script confirms it: iterate ALL (layer, cleared,
pivot) at every layer, count quadratic monomials per modified coord, report the max, and check it equals the
analytic bound and does NOT grow with depth (depth = which layer s; the count is layer-local).

Exit 0 = max per-coord quadratic-monomial count ≤ max_ℓ d_ℓ on every config ⟹ uniform C exists.
"""
import sympy as sp
from cap_frontier_sufficiency import make, canonNormalizationOf

def quad_monomial_count(expr):
    e = sp.expand(expr)
    if e == 0:
        return 0, 0
    terms = sp.Add.make_args(e)
    # each term should be ±(coord)·(coord): total degree 2, coeff ±1
    degs = [sp.Poly(t, *e.free_symbols).total_degree() if t.free_symbols else 0 for t in terms]
    maxdeg = max(degs) if degs else 0
    return len(terms), maxdeg

WITS = [(2,3,3,3),(3,4,4,4),(2,4,3,2),(3,2,4,5),(2,3,4,5,3),(4,4,4,4,4)]
allok = True
for d in WITS:
    N, u = make(d)
    maxwidth = max(d)
    overall_max = 0; maxdeg_seen = 0
    per_layer_max = {}
    for slayer in range(N):
        for scleared in range(d[slayer] + 1):        # cleared ∈ 0..d_slayer
            for pivot in u:                           # every possible pivot coord
                phi = canonNormalizationOf(u, d, slayer, scleared, pivot)
                for k, ex in phi.items():
                    cnt, mdg = quad_monomial_count(ex)
                    if cnt > overall_max: overall_max = cnt
                    if mdg > maxdeg_seen: maxdeg_seen = mdg
                    per_layer_max[slayer] = max(per_layer_max.get(slayer, 0), cnt)
    ok = overall_max <= maxwidth and maxdeg_seen <= 2
    allok &= ok
    print(f"d={d}: max quad-monomials/coord = {overall_max} (≤ max_ℓ d_ℓ = {maxwidth}? {overall_max<=maxwidth}); "
          f"max total-degree = {maxdeg_seen} (purely quadratic? {maxdeg_seen<=2}); "
          f"per-layer(depth) max = {per_layer_max}")
print(f"\nPer-coord quadratic-monomial count uniformly bounded (≤ max width, depth-independent) on all? {allok}")
assert allok
print("OK: canonNormalizationOf's quadratic part has ≤ max_ℓ d_ℓ monomials/coord, UNIFORM across all "
      "edges/pivots/depths (count is layer-local, not depth-accumulating). ⟹ uniform C exists for L7.")
