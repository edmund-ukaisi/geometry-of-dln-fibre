"""seat-L4D — the (b) ed1 diagonal-block-through-F₂ trace, INTERIOR S=1 pivot (exercises branch-(iii)).
Witness d=(3,2,2,2): layers 0,1,2; pivot at layer S=1 (interior). A_0 (2×3, =A_{S-1}), A_1 (2×2, =A_S,
pivot (0,0)), A_2 (2×2, =A_{S+1}). F₂ full-faithful three-home: branch-(i) interior Schur on A_1 → e₂;
branch-(ii) OUTPUT recoord A_2·Q₁⁻¹; branch-(iii) INPUT recoord Q₂⁻¹·A_0 (ACTIVE here — A_{S-1} exists).
Claim (Lemma-2, diag in NEW vars): A_1 recoords to diag(1,e₂) AND the product A_2·A_1·A_0 is PRESERVED
(the compensators absorb the pivot cross into the neighbors). branch-(iii) is EXERCISED (non-trivial Q₂⁻¹·A_0).
"""
import sympy as sp
u = lambda l,r,c: sp.Symbol(f'u{l}{r}{c}')
A0 = sp.Matrix([[u(0,r,c) for c in range(3)] for r in range(2)])   # layer 0: 2×3 (=A_{S-1})
A1 = sp.Matrix([[u(1,r,c) for c in range(2)] for r in range(2)])   # layer 1: 2×2 (pivot block A_S)
A2 = sp.Matrix([[u(2,r,c) for c in range(2)] for r in range(2)])   # layer 2: 2×2 (=A_{S+1})
b, g = A1[0,1], A1[1,0]; e2 = A1[1,1] - g*b                        # β=A1[0][1], γ=A1[1][0]
# pivot-normalize A1[0][0]→1 (blow-up chart): work with A1n
A1n = sp.Matrix([[1, b],[g, A1[1,1]]])
Q1 = sp.Matrix([[1,0],[-g,1]]); Q2 = sp.Matrix([[1,-b],[0,1]])
blockF2 = sp.expand(Q1*A1n*Q2)                                     # F₂: pivot-cross clear
print('branch-(i)+F₂: Q₁·A₁·Q₂ =', blockF2.tolist(), ' (= diag(1,e₂), e₂=', sp.expand(e2), ')')
assert blockF2 == sp.Matrix([[1,0],[0,e2]]), 'A₁ recoords to diag(1,e₂) in the new vars'
# product preservation: A₂·A₁·A₀ = (A₂·Q₁⁻¹)·diag(1,e₂)·(Q₂⁻¹·A₀)   [branch-ii OUTPUT, branch-iii INPUT]
orig = sp.expand(A2*A1n*A0)
A2p  = sp.expand(A2*Q1.inv())        # branch-(ii): A_{S+1}·Q₁⁻¹  (OUTPUT recoord)
A0p  = sp.expand(Q2.inv()*A0)        # branch-(iii): Q₂⁻¹·A_{S-1} (INPUT recoord — ACTIVE at S=1)
comp = sp.expand(A2p*blockF2*A0p)
print('product preserved (F₂ composite == original)?', sp.expand(comp-orig)==sp.zeros(2,3))
assert sp.expand(comp-orig)==sp.zeros(2,3), 'F₂ three-home must preserve the product'
# branch-(iii) EXERCISED: Q₂⁻¹·A₀ ≠ A₀ (input recoord is non-trivial at interior S=1)
print('branch-(iii) ACTIVE (Q₂⁻¹·A₀ ≠ A₀)?', sp.expand(A0p-A0)!=sp.zeros(2,3))
assert sp.expand(A0p-A0)!=sp.zeros(2,3), 'branch-(iii) must be non-trivial at interior S=1'
print('\n(b) TRACE PASS: interior S=1 — A₁→diag(1,e₂) in F₂ new vars; product PRESERVED via the two')
print('compensators (ii OUTPUT A₂·Q₁⁻¹ + iii INPUT Q₂⁻¹·A₀, both active); branch-(iii) EXERCISED.')
print('⟹ Lemma-2 diagonal-block-through-F₂ confirmed at an interior pivot (not just the corner).')
