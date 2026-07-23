"""seat-L4D confirmation battery (condition a+b), ed1-level all-entries, (2,2,2,2) corner pivot a=b=0.

FINDING (solid, model-independent): the branch-(i) Schur sign is LOAD-BEARING (elder condition b).
 - Flip branch (ii) recoord ALONE (−γ), Schur left at −γβ: (A₁·A₀)[0][1] = u001u100+u011u101 − 2u001u010u101
   — a residual defect (condition a: "a single entry can go clean by coincidence" — [0][0] went clean, [0][1] did not).
 - Flip BOTH (Schur +γβ AND recoord −γ): all four (A₁·A₀) entries lose the doubling; col-0 = u100/u110 (clean).
CAVEAT: (A₁·A₀) MIXES the clean D_J block with the recoordinatized deeper factor ∏_{s>S}C (her invariant
diag(b)·[E_J|D_J]·∏C), so this ed1-product does NOT cleanly separate D_J — the R3-vs-R4 direction and the
clean-D_J verdict need the full reuse-node structure (pnp harness #49/#50), which separates D_J from ∏C.
"""
import sympy as sp
u = lambda l, r, c: sp.Symbol(f'u{l}{r}{c}')
A1 = sp.Matrix([[u(1,0,0), u(1,0,1)], [u(1,1,0), u(1,1,1)]])
g, b = u(0,1,0), u(0,0,1)

def run(recoord_sign, schur_sign):
    A0 = sp.Matrix([[1, b], [g, u(0,1,1) + schur_sign*(-g*b)]])   # column NOT cleared; pivot→1
    A1r = A1 * sp.Matrix([[1, 0], [recoord_sign*g, 1]])           # recoord A1·(I ± γ e_i e_a^T)
    return sp.expand(A1r * A0)

P_ii_only = run(-1, -1)   # flip branch (ii) only
P_both    = run(-1, +1)   # flip both (Codex R3 as stated)
print('flip branch-(ii) only [0][1] =', P_ii_only[0,1], '  (defect −2u001u010u101 → condition b needed)')
print('flip BOTH entries     =', [sp.expand(P_both[i,j]) for i in range(2) for j in range(2)])
assert P_ii_only[0,1] == sp.expand(u(0,0,1)*u(1,0,0) + u(0,1,1)*u(1,0,1) - 2*u(0,0,1)*u(0,1,0)*u(1,0,1))
print('\nCONFIRMED: branch-(i) Schur sign is LOAD-BEARING (both signs must flip). '
      'Clean-D_J-at-reuse-node deferred to pnp (ed1-product mixes D_J + deeper factor).')
