#!/usr/bin/env python3
# provenance: threads/L4-case1-core (SEAT-L4). Obstruction (ii) of THE WALL checkpoint —
# decorrelated Codex-confirmed. The foldResid PURE-PULLBACK + foldB EXTRA-u_p is a u_p-ORDER
# mismatch for δ=1, INDEPENDENT of the shear (hits case11 too, φ=id). EXACT algebra.
"""
The round-5 foldState DATA defs set, for a δ=1 child:
  foldB(child) u    = u_pivot^1 · foldB p (stepMap u)          -- EXTRA u_pivot
  foldResid(child)_j = foldResid p_j ∘ stepMap                  -- PURE PULLBACK (docstring: "never a
                                                                   division; that belongs to the ∃q")
FoldStepInv(child) needs ∃ CONTINUOUS q', coreGen∘foldG(child) = ∑_j q'_j·(foldB(child)·foldResid(child)_j).

But foldResid p_j ∈ ⟨center coords⟩ (hsupp) ALREADY gains u_pivot under blockBlowupMap, so
foldResid(child)_j = u_pivot·ρ_j; and foldB(child) carries ANOTHER u_pivot ⟹ foldB(child)·foldResid(child)
carries u_pivot², while coreGen∘foldG(child) carries only u_pivot¹. No continuous q' bridges u_p¹ = u_p²·q'.
The ∃q CANNOT absorb it — refuting the docstring's "division belongs to ∃q". Codex-decorrelated confirm.

FIX-RESID: foldResid(child) for δ=1 must be the STRICT TRANSFORM (resid∘stepMap)/u_pivot (seat-L4's
BlockDivision `blockBlowup_center_comb_eq` supplies the exact quotient), NOT the pure pullback.
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok
    ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

# Codex's minimal witness: case11 (edgeShear=id, stepMap = blockBlowupMap), D=3, center {0,1}, pivot 0.
# resid = the pivot coordinate v_0 (∈ ⟨center coords⟩ via c_0=1); b = q = 1.  δ = 1.
u0, u1, u2 = sp.symbols('u0 u1 u2')
pivot = 0; center = {0, 1}
def blockBlowup(u):
    return [u[0] if j == pivot else (u[0] * u[j] if j in center else u[j]) for j in range(3)]
sm = blockBlowup([u0, u1, u2])                     # case11 stepMap (no shear)

resid = [lambda w: w[0]]                            # resid_0 = center coord 0 (= the pivot); SupportedOn
coreGen_g = sp.Integer(1)                           # b = q = 1 ⟹ (coreGen∘foldG p)(v) = resid_0(v)
LHS = resid[0](sm)                                  # coreGen∘foldG(child) = resid_0(stepMap u) = u0
bprime = u0 * 1                                     # foldB(child) = u_pivot^1 · (b∘stepMap) = u0
residp = resid[0](sm)                               # foldResid(child)_0 = resid_0∘stepMap = u0 (pullback)
RHS_factor = bprime * residp                        # foldB(child)·foldResid(child)_0 = u0 * u0 = u0^2
check("LHS coreGen∘foldG(child) = u0  (u_pivot order 1)", sp.simplify(LHS - u0) == 0)
check("RHS foldB(child)·foldResid(child) = u0^2  (u_pivot order 2)", sp.simplify(RHS_factor - u0**2) == 0)
qprime = sp.cancel(LHS / RHS_factor)                # the forced q' = u0/u0^2 = 1/u0
check("forced q' = LHS/RHS = 1/u0 is NON-polynomial (discontinuous at u0=0) ⟹ NO continuous witness",
      not qprime.is_polynomial(u0, u1, u2) and sp.simplify(qprime - 1/u0) == 0)
check("φ-INDEPENDENT: this is case11 (edgeShear=id, no shear) ⟹ the mismatch is a foldResid/foldB bug",
      True)

# FIX-RESID: strict transform resid' = (resid∘stepMap)/u_pivot ⟹ balance restored with q'=q∘stepMap.
resid_strict = sp.cancel(residp / u0)               # = u0/u0 = 1, POLYNOMIAL (continuous)
check("FIX-RESID strict transform (resid∘stepMap)/u_pivot = 1 is polynomial (continuous)",
      resid_strict.is_polynomial(u0, u1, u2))
check("FIX-RESID balances: q'=1, foldB(child)·resid'_strict = u0·1 = u0 = LHS ✓",
      sp.simplify(1 * (bprime * resid_strict) - LHS) == 0)

print("\nCONCLUSION (Codex-decorrelated): the δ=1 foldState formula (foldB extra-u_p + foldResid PURE")
print("PULLBACK) is a u_p-ORDER mismatch, φ-INDEPENDENT (breaks case11 too). The ∃q cannot absorb it")
print("(would need q'=1/u_p). FIX: foldResid(child) for δ=1 = STRICT TRANSFORM (resid∘stepMap)/u_pivot")
print("(seat-L4 BlockDivision.blockBlowup_center_comb_eq supplies the exact quotient). This is SEPARATE")
print("from + on top of the shear-alignment fix (case1_shear_alignment_checkpoint.py).")
print(f"\nL4 resid-order-mismatch (obstruction ii): {'PASS (gap confirmed)' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)
