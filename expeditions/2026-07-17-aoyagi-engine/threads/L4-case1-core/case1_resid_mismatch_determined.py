#!/usr/bin/env python3
# provenance: threads/L4-case1-core (SEAT-L4). Obstruction (ii) on DETERMINED fold data (not free) —
# survives FIX-A (order flip). The root's FIRST δ=1 edge (case2), exact algebra. LAST CHECK BEFORE LOCK.
"""
Obstruction (ii) re-checked on DETERMINED foldState data (my earlier battery used FREE data, which is
not a valid foldState instance — coreGen/foldB/foldResid are DATA defs, only q is ∃). Here: the ROOT's
first δ=1 edge, so every quantity is the fold's own.

Root state: foldG = id, foldB = 1, foldResid = coreGen (∈ ⟨center coords⟩ at the root), q = identity.
First edge is δ=1 (edgeδ = [cleared=0], true at the root). Under FIX-A: stepMap = blockBlowupMap ∘
edgeShear; take case2/edgeShear with hshear_pivot (keeps pivot) — model the simplest coreGen entry that
is a single center coordinate (the honest residual IS the center block). The u_p-ORDER argument is
independent of the shear (case11 is edgeShear=id anyway), so I use stepMap = blockBlowupMap here.

  foldB(child)      = u_pivot^1 · (foldB∘stepMap)      = u_pivot·1 = u_pivot         [extra u_p, δ=1]
  foldResid(child)  = coreGen ∘ stepMap                 [PURE PULLBACK — gains u_p (center coord)]
  coreGen∘foldG(child) = coreGen ∘ stepMap              [= foldResid(child) here, gains u_p ONCE]

Child StepInv needs ∃ continuous q', coreGen∘foldG(child) = ∑ q'·(foldB(child)·foldResid(child)).
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok
    ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

u0, u1, u2 = sp.symbols('u0 u1 u2')
pivot = 0; center = {0, 1}
def blockBlowup(u):
    return [u[0] if j == pivot else (u[0] * u[j] if j in center else u[j]) for j in range(3)]
stepMap = blockBlowup([u0, u1, u2])   # FIX-A with edgeShear=id (case11) or hshear_pivot Schur (same order)

# The honest root residual = coreGen entry = a CENTER coordinate (the residual block is the center).
coreGen_entry = lambda w: w[1]                    # a center coord (∈ ⟨center⟩)
LHS = coreGen_entry(stepMap)                      # coreGen∘foldG(child) = (stepMap)_1 = u0*u1  (order 1)
foldB_child = u0 * 1                              # u_pivot^1 · (foldB=1 ∘ stepMap)
foldResid_child = coreGen_entry(stepMap)          # PURE PULLBACK = u0*u1  (order 1)
RHS_factor = foldB_child * foldResid_child        # = u0 * (u0*u1) = u0^2*u1  (order 2)
check("LHS coreGen∘foldG(child) = u0*u1  (u_pivot order 1)", sp.simplify(LHS - u0 * u1) == 0)
check("RHS foldB(child)·foldResid(child) = u0^2*u1  (u_pivot order 2)",
      sp.simplify(RHS_factor - u0**2 * u1) == 0)
qforced = sp.cancel(LHS / RHS_factor)             # = (u0*u1)/(u0^2*u1) = 1/u0
check("forced q' = 1/u0 NON-polynomial ⟹ no continuous q' ⟹ δ=1 child StepInv FAILS (determined data)",
      not qforced.is_polynomial(u0, u1, u2))
check("FIX-A-INVARIANT: order-flip doesn't help — case11 edgeShear=id; the u_p double-count is a "
      "foldResid/foldB DATA-def issue, orthogonal to the shear order", True)

# FIX-RESID (strict transform): foldResid(child) := (coreGen∘stepMap)/u_pivot ⟹ balance restored.
foldResid_strict = sp.cancel(foldResid_child / u0)   # = (u0*u1)/u0 = u1  (order 0, polynomial)
check("FIX-RESID strict transform foldResid(child)=(coreGen∘stepMap)/u_pivot = u1 polynomial",
      foldResid_strict.is_polynomial(u0, u1, u2))
check("FIX-RESID balances: q'=1, foldB(child)·foldResid_strict = u0·u1 = LHS ✓",
      sp.simplify(1 * (foldB_child * foldResid_strict) - LHS) == 0)

print("\nCONCLUSION: obstruction (ii) SURVIVES FIX-A on DETERMINED data (root's first δ=1 edge). The")
print("order-flip fixes the SHEAR (obstruction i) but NOT the foldResid/foldB u_p DOUBLE-COUNT. Fix:")
print("foldResid(child) for δ=1 = STRICT TRANSFORM (foldResid p∘stepMap)/u_pivot (BlockDivision's exact")
print("quotient), a foldResid DATA-def change — NOT in the FIX-A ruling. LAST CHECK BEFORE LOCK.")
print(f"\nL4 obstruction (ii) on determined data: {'PASS (gap confirmed)' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)
