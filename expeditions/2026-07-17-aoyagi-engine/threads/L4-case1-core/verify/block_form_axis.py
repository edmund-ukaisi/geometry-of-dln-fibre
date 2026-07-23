"""seat-L4D §8(g) BLOCK-AXIS decision (the priority column): does R3 monomialise the A_S block?
(2,2,2,2) ed1, corner pivot a=b=0. β=u001 (row a), γ=u010 (col b), e₂=u011−u001u010.
VERDICT: R3 leaves A_S NON-diagonal ⟹ block axis needs R4. R4 must REPLACE branch (i), not stack (double-count)."""
import sympy as sp
u=lambda l,r,c: sp.Symbol(f'u{l}{r}{c}')
b,g=u(0,0,1),u(0,1,0); e2=u(0,1,1)-g*b
A_S_R3 = sp.Matrix([[1,b],[g,e2]])   # under R3: branch(i) wrote only [1][1]=e2; branch(ii)/R3 don't touch A_S
Q1=sp.Matrix([[1,0],[-g,1]]); Q2=sp.Matrix([[1,-b],[0,1]])
A_S_raw = sp.Matrix([[1,b],[g,u(0,1,1)]])   # RAW A_S (no branch-i Schur)
R4_on_raw   = sp.expand(Q1*A_S_raw*Q2)
R4_on_R3    = sp.expand(Q1*A_S_R3*Q2)        # R4 stacked ON branch-(i) — DOUBLE-COUNT
print('A_S under R3        =', A_S_R3.tolist(), '  (off-diag β,γ present ⟹ NON-diagonal)')
print('R4 on RAW A_S       =', R4_on_raw.tolist(), '  → diag(1,e₂) ✓ (R4 REPLACES branch (i))')
print('R4 on branch-i A_S  =', R4_on_R3.tolist(), '  → [1][1]=u011−2u001u010 DOUBLE-COUNT (do NOT stack)')
assert R4_on_raw == sp.Matrix([[1,0],[0,e2]])
assert A_S_R3[0,1]==b and A_S_R3[1,0]==g   # non-diagonal
print('\nBLOCK AXIS: R3 does NOT monomialise (A_S non-diagonal) ⟹ R3+R4; R4 = generator transform on RAW A_S '
      '(replaces branch (i), clears β,γ → diag(1,e₂)); contained + G1-clean. Re-open only if R3+R4 cannot '
      'diagonalise within the fold — it does (Q₁·A_S·Q₂ = diag(1,e₂), Aoyagi worked.tex:619-629).')
