"""seat-L4D confirmation battery (condition a+b), ed1-level all-entries, (2,2,2,2) corner pivot a=b=0.

SUPERSEDED by §8(i) (384ac17dc): this tests the two-sign COORDINATE flip on the ed1 PRODUCT — the WRONG
object. foldResid IS the block-slot (scalar-foldB def-fact), so the fix is DEF-EDIT-3 = branch-(i) REPLACED
by the R4 generator transform Q₁·A_S·Q₂ → diag(1,e₂) (classical −γβ) + branch-(ii) flip; NOT the two-sign
flip. Kept for the record: its live residue is the condition-(b)-load-bearing fact about the (moot) product
object, and the CAVEAT-2 discrepancy below is exactly what surfaced the wrong-object catch.

FINDING (solid, model-independent, controller re-derived): the branch-(i) Schur sign is LOAD-BEARING.
Baked = recoord +γ (Q₁⁻¹), Schur corner −γβ (= e₂). Controller-verified identity:
    (A₁·A₀)[0][1] = β·u₁₀₀ + u₀₁₁·u₁₀₁ + (r − s)·γβ·u₁₀₁,   r = recoord sign (−1 flipped),
    s = Schur "kept" sign (+1 kept / −1 flipped).
 - flip recoord ONLY (branch-(i) Schur KEPT): (r,s)=(−1,+1) ⟹ −2γβ·u₁₀₁ DEFECT at [0][1]
   (condition a: [0][0] went clean, [0][1] did not — "a single entry can go clean by coincidence").
 - flip BOTH (recoord −γ AND Schur +γβ): (r,s)=(−1,−1) ⟹ (r−s)=0 ⟹ clean cross-term at all entries.
So branch (i) MUST flip too (Codex's stated R3: −γ recoord, +γβ Schur).
[ERRATUM: the prior committed version SWAPPED the run() labels — schur_sign multiplied (−γβ), so +1 KEEPS
 and −1 FLIPS, inverting the comments; the assert then tested the clean matrix and failed the controller's
 re-run. Fixed here to explicit flip_recoord/flip_schur booleans so names, prints, and asserts agree.]
CAVEAT-1: (A₁·A₀) MIXES the clean D_J block with the recoordinatized deeper factor — clean-D_J needs the
reuse-node structure (pnp #50). CAVEAT-2 (sign convention, flag to elder + pnp): under the both-flip the
block corner is u₀₁₁ + γβ, NOT the classical Schur u₀₁₁ − γβ (the empirical/baked e₂) — a unit/sign
convention to reconcile against the e₂/divExp ledger.
"""
import sympy as sp
u = lambda l, r, c: sp.Symbol(f'u{l}{r}{c}')
A1 = sp.Matrix([[u(1,0,0), u(1,0,1)], [u(1,1,0), u(1,1,1)]])
g, b = u(0,1,0), u(0,0,1)

def run(flip_recoord, flip_schur):
    recoord_off = (-g if flip_recoord else g)          # baked +γ (Q₁⁻¹); flip → −γ (Q₁)
    corner = u(0,1,1) + (g*b if flip_schur else -g*b)  # baked −γβ (=e₂); flip → +γβ
    A0 = sp.Matrix([[1, b], [g, corner]])              # A_S, pivot→1, column NOT cleared
    A1r = A1 * sp.Matrix([[1, 0], [recoord_off, 1]])   # recoord A_{S+1}·(I + recoord_off · e_i e_a^T)
    return sp.expand(A1r * A0)

P_ii_only = run(flip_recoord=True,  flip_schur=False)  # recoord flipped, Schur KEPT → DEFECT
P_both    = run(flip_recoord=True,  flip_schur=True)   # both flipped → CLEAN cross-terms

defect = sp.expand(b*u(1,0,0) + u(0,1,1)*u(1,0,1) - 2*g*b*u(1,0,1))
print('flip recoord ONLY [0][1] =', P_ii_only[0,1], ' (defect −2γβu₁₀₁ ⟹ branch-(i) sign needed)')
print('flip BOTH entries        =', [sp.expand(P_both[i,j]) for i in range(2) for j in range(2)])
assert P_ii_only[0,1] == defect, 'ii-only (Schur kept) must carry the −2γβu₁₀₁ defect'
# both-flip: no γβ cross-term survives (col-0 = u₁₀₀/u₁₁₀ clean; col-1 coeffs are layer-0 entries, not γβ)
assert sp.expand(P_both[0,1] - (b*u(1,0,0) + u(0,1,1)*u(1,0,1))) == 0, 'both-flip [0][1] must be clean'
print('\nCONFIRMED: branch-(i) Schur sign is LOAD-BEARING (both signs must flip). Both-flip block corner = '
      'u₀₁₁+γβ (CAVEAT-2). Clean-D_J-at-reuse-node deferred to pnp (#50).')
