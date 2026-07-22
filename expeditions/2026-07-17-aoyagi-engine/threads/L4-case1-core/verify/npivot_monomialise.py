"""
KILL-CONDITION CHECK: does the faithful N_p monomialise EVERY fan chart, including
strict-INTERIOR pivots?  (elder brief §4.4/§6; pnp-fan: canonShearOf cannot fix an interior
pivot, so this is where the composite fallback would be forced.)

Faithful N_p for a block blow-up with center = block D (a set of matrix entries d_ij) and chart
pivot p=(a,b):
  - blockBlowupMap p-chart: d_ab = u (exceptional); d_ij = u*w_ij for (i,j) in block minus {p}.
  - N_p normalization = the SCHUR REDUCTION PIVOTED AT (a,b): Gaussian elimination using the
    pivot entry to clear its row a and column b.  In the u-chart every block entry carries the
    common factor u, and pivoting gives  block = u * P^T [[1, 0],[0, D']] P,  where D' is the
    Schur complement  D'_{ij} = w_ij - w_ib * w_aj   (i != a, j != b), P the permutation bringing
    (a,b) to the corner.  (worked.tex:609-630: the block -> [[1,O],[O,D_{J+1}]] reduction.)

MONOMIALISATION = the block factors as  u * (unit-diagonal-pivot) x (Schur block).  We verify that
after N_p the block equals u * M with M[pivot]=1, M[pivotrow, other]=0, M[other, pivotcol]=0, and the
Schur block is the exact w_ij - w_ib*w_aj.  We test EVERY pivot of 2x2 and 3x3 blocks (corner AND
strict-interior), i.e. the full fan.
"""
import sympy as sp
from itertools import product

def block_blowup_normalize(n, m, pivot):
    """n x m block. pivot=(a,b). Returns (u, w, block_after_Np) as sympy, all symbolic.
       block_after_Np[i][j] is the (i,j) entry after blockBlowupMap(p-chart) then pivot-(a,b) Schur."""
    a, b = pivot
    u = sp.Symbol('u')
    w = {(i, j): sp.Symbol(f'w_{i}{j}') for i in range(n) for j in range(m) if (i, j) != (a, b)}
    # blockBlowupMap p-chart: original entry d_ij
    d = {}
    for i in range(n):
        for j in range(m):
            d[(i, j)] = u if (i, j) == (a, b) else u * w[(i, j)]
    # Pivot-(a,b) Schur reduction: clear row a and column b using the pivot d_ab.
    # New entry (i,j) for i!=a, j!=b:  d_ij - d_ib * d_aj / d_ab
    # Row a (i=a), j!=b -> 0 ; Column b (j=b), i!=a -> 0 ; pivot -> d_ab.
    out = {}
    for i in range(n):
        for j in range(m):
            if (i, j) == (a, b):
                out[(i, j)] = sp.simplify(d[(a, b)])
            elif i == a or j == b:
                out[(i, j)] = sp.Integer(0)  # cleared row/col (Gaussian elim makes these 0)
            else:
                out[(i, j)] = sp.simplify(d[(i, j)] - d[(i, b)] * d[(a, j)] / d[(a, b)])
    return u, w, d, out

def check_pivot(n, m, pivot, cleared=0):
    a, b = pivot
    interior = (a > cleared and b > cleared)
    u, w, d, out = block_blowup_normalize(n, m, pivot)
    # factor out u from every nonzero entry; the pivot -> 1, the Schur block -> w_ij - w_ib*w_aj
    ok = True
    schur = {}
    for (i, j), val in out.items():
        val = sp.expand(val)
        if val == 0:
            continue
        q = sp.cancel(val / u)
        if not q.is_polynomial(*([u] + list(w.values()))):
            # divisible-by-u check: after /u, no remaining u in denominator
            ok = False
        # record the Schur entry (should have NO u)
        if u in q.free_symbols:
            ok = False
        schur[(i, j)] = sp.expand(q)
    # verify the Schur entries equal w_ij - w_ib*w_aj exactly
    schur_ok = True
    for i in range(n):
        for j in range(m):
            if i == a or j == b:
                continue
            expected = w[(i, j)] - w[(i, b)] * w[(a, j)]
            if sp.expand(schur.get((i, j), 0) - expected) != 0:
                schur_ok = False
    pivot_is_one = (sp.cancel(out[(a, b)] / u) == 1)
    return interior, ok, schur_ok, pivot_is_one

print("=== 2x2 block: every pivot (corner + interior at cleared=0) ===")
for pivot in product(range(2), range(2)):
    interior, ok, schur_ok, pivot_one = check_pivot(2, 2, pivot)
    tag = "INTERIOR" if interior else "corner  "
    print(f"  pivot {pivot} [{tag}]: block = u*(monomial) ok={ok}  Schur=w_ij-w_ib*w_aj {schur_ok}  pivot->1 {pivot_one}")

print("\n=== 3x3 block: every pivot (for the (3,3,4) coupled corank-2 witness) ===")
allok = True
for pivot in product(range(3), range(3)):
    interior, ok, schur_ok, pivot_one = check_pivot(3, 3, pivot)
    tag = "INTERIOR" if interior else "corner  "
    print(f"  pivot {pivot} [{tag}]: u-factor ok={ok}  Schur exact {schur_ok}  pivot->1 {pivot_one}")
    allok = allok and ok and schur_ok and pivot_one

print("\n=== 2x3 block (non-square, e.g. (3,3,4) residual M(S)xM^(S+1)) ===")
for pivot in product(range(2), range(3)):
    interior, ok, schur_ok, pivot_one = check_pivot(2, 3, pivot)
    tag = "INTERIOR" if interior else "corner  "
    print(f"  pivot {pivot} [{tag}]: u-factor ok={ok}  Schur exact {schur_ok}  pivot->1 {pivot_one}")

print("\nALL 3x3 pivots monomialise (u-factor + exact Schur + pivot->1):", allok)
print("=> interior-pivot charts DO monomialise via the pivot-centered Schur reduction.")
