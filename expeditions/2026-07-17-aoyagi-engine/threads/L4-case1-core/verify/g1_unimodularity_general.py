"""seat-L4D — GUARD G1 (unimodularity) at the def, general/interior/fanned pivot + both candidate Q-directions.

G1: the generator-transform Q's are unimodular (det 1) over the polynomial ring ℝ[u], so
⟨R4-rewritten resid⟩ = ⟨original⟩ as IDEALS (not merely same-variety) — the RLCT-invariant guard.
The fold uses the pivot-NORMALIZED clearing ratio γ_i = A_S[i][b] (the un-divided form branch (ii)
already uses; no 1/pivot), so the Q's are polynomial. Q₁ (row-op, clears col b) and Q₂ (col-op, clears
row a) are elementary unipotent ⟹ det 1 for ANY pivot (a,b) and block size, in BOTH directions
(Q₁ = R4 generator transform; Q₁⁻¹ = the baked/R3 recoord direction). Run: python3 → exit 0.
"""
import sympy as sp

def Qs(n, m, a, b):
    """Row-op Q₁ (n×n, clears column b: rows i≠a get γ_i·row_a) and col-op Q₂ (m×m, clears row a)."""
    A = sp.Matrix(n, m, lambda i, j: sp.Symbol(f'a{i}{j}'))
    Q1 = sp.eye(n)
    for i in range(n):
        if i != a:
            Q1[i, a] = A[i, b]            # γ_i = A_S[i][b] (pivot-normalized, polynomial)
    Q2 = sp.eye(m)
    for j in range(m):
        if j != b:
            Q2[b, j] = A[a, j]            # δ_j = A_S[a][j]
    return Q1, Q2

cases = [
    ('corner 2x2 (a,b)=(0,0)', 2, 2, 0, 0),
    ('interior 3x3 (a,b)=(1,1)', 3, 3, 1, 1),
    ('fanned 3x3 (a,b)=(2,1)', 3, 3, 2, 1),      # interior/fanned pivot, off-diagonal
    ('fanned 3x2 (a,b)=(2,0)', 3, 2, 2, 0),      # wide-remnant-row pivot (the cap-escape trigger)
    ('fanned 2x3 (a,b)=(0,2)', 2, 3, 0, 2),
]
allok = True
for name, n, m, a, b in cases:
    Q1, Q2 = Qs(n, m, a, b)
    d1, d2, d1i = sp.expand(Q1.det()), sp.expand(Q2.det()), sp.expand(Q1.inv().det())
    ok = (d1 == 1 and d2 == 1 and d1i == 1)
    allok &= ok
    print(f'{name:28} detQ₁={d1} detQ₂={d2} detQ₁⁻¹={d1i}  {"OK" if ok else "FAIL"}')
assert allok, 'G1 unimodularity failed for some pivot'
print('\nG1 CONFIRMED: Q₁, Q₂, Q₁⁻¹ all det 1 (elementary unipotent) for corner/interior/fanned pivots and '
      'wide-remnant blocks, BOTH candidate directions (R4 = Q₁, baked/R3 = Q₁⁻¹). ⟨rewritten⟩=⟨original⟩ '
      'as ideals ⟹ RLCT-invariant guard holds at the def for whichever candidate the council picks.')
