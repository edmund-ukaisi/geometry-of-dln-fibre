"""seat-L4D → pnp-transport: the exact case11 boost center + the ROW-clear status, for pnp's
decisive Deg1SupportedOn-center boostReady verdict on the FROZEN §8(i) def (R4-PAIRED, not R3-alone).

(2,2,2,2) corner pivot a=b=0.  β = u001 (pivot ROW, right of pivot), γ = u010 (pivot COLUMN, below pivot).
The reused-pivot / normalized-chart coordinate is  w := e₂ = u011 − u001·u010  (Aoyagi's classical Schur
complement; atomic in the normalized chart — pnp's `w`).  ed.center(case11) = {w} ∪ partialBlock coords.

PNP'S TWO QUESTIONS, answered at the def:
 (Q-center) exact center coord = w = e₂ = u011 − u001·u010.  Under R4 the D_J corner residual IS w, so
            Deg1SupportedOn {w} holds BY IDENTITY (the entry equals a single center coordinate, degree 1).
 (Q-row)   R3-alone (the −γ recoord, Q₁-type) clears the pivot COLUMN (γ→0) ⟹ clean E_J, but leaves the
            pivot ROW (β survives).  R4 = R3's Q₁ PLUS the Q₂ col-op that clears the pivot ROW (β→0).
            So YES, the frozen §8(i) def DOES clear the row — it is the Q₂ half of R4, which R3-alone lacks.
            That row-clear is exactly what removes pnp's u001² (§8(j): the flag VALIDATES R4).

Run: python3 boost_center_case11.py  → exit 0.
"""
import sympy as sp
u = lambda l, r, c: sp.Symbol(f'u{l}{r}{c}')
b, g, c = u(0, 0, 1), u(0, 1, 0), u(0, 1, 1)   # β (row), γ (col), raw corner
e2 = c - b * g                                  # w = classical e₂, atomic in the normalized chart
A_S_raw = sp.Matrix([[1, b], [g, c]])           # RAW A_S, pivot→1 (NO branch-(i) Schur pre-write)

Q1 = sp.Matrix([[1, 0], [-g, 1]])               # R3 recoord (row-op): clears pivot COLUMN (γ→0)
Q2 = sp.Matrix([[1, -b], [0, 1]])               # R4's extra col-op: clears pivot ROW (β→0)

R3_alone = sp.expand(Q1 * A_S_raw)              # column cleared, ROW uncleared
R4       = sp.expand(Q1 * A_S_raw * Q2)         # both cleared → diag(1, e₂)

print('R3-alone (Q₁·A_S)   =', R3_alone.tolist(), '  col cleared ([1][0]=0), ROW survives ([0][1]=β=u001)')
print('R4 (Q₁·A_S·Q₂)      =', R4.tolist(),       '  → diag(1, e₂): BOTH cleared; corner = w')
print('center coord w = e₂ =', e2)

# (Q-row) R3-alone clears the column but NOT the row; R4 clears both.
assert R3_alone[1, 0] == 0 and R3_alone[0, 1] == b, 'R3-alone: column cleared, pivot ROW (β) survives'
assert R4 == sp.Matrix([[1, 0], [0, e2]]),          'R4: both cleared → diag(1, e₂)'
# (Q-center) the D_J corner under R4 IS the center coordinate w ⟹ Deg1SupportedOn {w} by identity.
w = sp.Symbol('w')
corner_in_chart = R4[1, 1].subs(e2, w)          # normalized chart: e₂ ↦ atomic w
assert sp.total_degree(sp.Poly(corner_in_chart, w)) == 1, 'corner = w, degree 1 in the center coord'

print('\nVERDICT for pnp: run Deg1SupportedOn-center on the R4-rendered residual (diag(1,e₂)), NOT R3-alone.')
print(' • center = {w = u011−u001·u010} ∪ partialBlock;  R4 corner = w ⟹ Deg1SupportedOn {w} by identity.')
print(' • R3-alone leaves β=u001 in the pivot row ⟹ ed2 recoord squares it (pnp u001²); R4 Q₂ removes it.')
print(' • So boostReady_case11 PASSES on the frozen §8(i) (R4-PAIRED) def; the u001² is R3-alone-only.')
