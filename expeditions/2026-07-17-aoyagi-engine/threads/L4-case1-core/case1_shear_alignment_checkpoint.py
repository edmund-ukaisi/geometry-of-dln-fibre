#!/usr/bin/env python3
# provenance: threads/L4-case1-core (SEAT-L4). THE WALL checkpoint (rev-leaves round-5 must-verify):
# does the δ=1 child divisibility survive the FREE shear `ed.shearφ` at a case12 edge? EXACT algebra.
"""
CHECKPOINT (owned by SEAT-L4): `case1_preserves_stepInv` types `ed.shearφ` as a FREE displacement
(only `hshear: jacDet(blockShear φ)=1`, `hshear0: φ 0 = 0`; round-5 DROPPED CenterCoordAligned), and
`stepMap = edgeShear ∘ blockBlowupMap` applies the shear AFTER the blow-up (`stepMap u =
blockShear φ (blockBlowupMap center pivot u)` at case12). The δ=1 child needs
`coreGen∘foldG p∘stepMap ∈ ⟨u_pivot⟩`; hsupp (foldResid ∈ ⟨center coords⟩) delivers it THROUGH
blockBlowupMap (center coords gain u_pivot) — BUT the after-shear can add spectator content to a
center coordinate: `(center coord)∘stepMap = u_pivot·(…) + φ(blockBlowup u)_center`, and a free φ's
term need not lie in ⟨u_pivot⟩.

Verdict this battery establishes (all EXACT, sympy/Q):
  (C1) A FREE jacDet-1, φ0=0 blockShear φ that mixes a SPECTATOR into a center coord BREAKS the
       divisibility: a center-supported residual pulls back to a function NOT in ⟨u_pivot⟩ (nonzero at
       u_pivot=0). ⟹ case12 δ=1 child divisibility FAILS for a free φ. [STOP-ON-SUSPECT (b).]
  (C2) The REAL Schur φ (displacement = a PRODUCT of center coords) is fine: its pullback gains u_pivot,
       divisibility holds. ⟹ the FOLD's real edges are safe; the gap is the STATEMENT's free φ.
  (C3) FIX-A (order flip): with blowup OUTERMOST (stepMap = blockBlowupMap ∘ shear, φ keeping the pivot)
       the center coords stay in ⟨u_pivot⟩ for ANY such φ — matches the certificate's φ=β∘σ_shear order
       (blowup last), OPPOSITE to the render's edgeShear∘blockBlowupMap.
  (C4) FIX-B (center-support constraint): if φ's center-coordinate displacements ∈ ⟨center coords⟩,
       render-order divisibility is restored (the real Schur φ is in this class).
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok
    ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

# D=3, center = {0,1} (card 2, the coupled minimum), pivot = 0, spectator = 2.
u0, u1, u2 = sp.symbols('u0 u1 u2')
center = {0, 1}
pivot = 0
def blockBlowup(u):
    return [u[0] if j == pivot else (u[0] * u[j] if j in center else u[j]) for j in range(3)]

# ---- (C1) FREE shear: φ writes center coord 1 with the SPECTATOR u2. jacDet=1 (unipotent), φ0=0. ----
def phi_free(w):  # displacement; blockShear φ (w) = w + φ(w)
    return [sp.Integer(0), w[2], sp.Integer(0)]   # only coord 1 gets +w2 (spectator)
def blockShear(phi, w):
    d = phi(w); return [w[j] + d[j] for j in range(3)]
# render order: stepMap = blockShear φ ∘ blockBlowup
u = [u0, u1, u2]
sm_free = blockShear(phi_free, blockBlowup(u))
# jacDet check on the SHEAR ALONE `blockShear φ` (= the `hshear` field), NOT the composite:
# blockShear φ (w) = (w0, w1+w2, w2), Jacobian unipotent ⟹ det 1.
w = list(sp.symbols('w0 w1 w2'))
bs = blockShear(phi_free, w)
Jsh = sp.Matrix([[sp.diff(bs[i], w[j]) for j in range(3)] for i in range(3)])
check("(C1) free φ: blockShear φ has jacDet = 1 (unipotent) and φ 0 = 0",
      sp.simplify(Jsh.det() - 1) == 0 and all(c == 0 for c in phi_free([0, 0, 0])))
# a center-supported residual: resid = center coord 1  (∈ ⟨center coords⟩, SupportedOn with c=e_1)
resid_pullback = sm_free[1]                      # (center coord 1) ∘ stepMap = u0*u1 + u2
check("(C1) center coord 1 ∘ stepMap = u0*u1 + u2  (render order, free φ)",
      sp.simplify(resid_pullback - (u0 * u1 + u2)) == 0)
check("(C1) NOT in ⟨u_pivot=u0⟩: value at u0=0 is u2 ≠ 0  ⟹ δ=1 divisibility FAILS for a free φ",
      sp.simplify(resid_pullback.subs(u0, 0) - u2) == 0 and resid_pullback.subs(u0, 0) != 0)

# ---- (C2) REAL Schur φ: displacement = a PRODUCT of center coords (e.g. −u_C21·u_C12). ----
def phi_schur(w):  # writes center coord 1 with a product of CENTER coords (0 and 1) — Schur-shape
    return [sp.Integer(0), -w[0] * w[1], sp.Integer(0)]
sm_schur = blockShear(phi_schur, blockBlowup(u))
resid_pb_schur = sm_schur[1]
check("(C2) real Schur φ (center-coord product): center coord 1 ∘ stepMap ∈ ⟨u0⟩ (vanishes at u0=0)",
      sp.simplify(resid_pb_schur.subs(u0, 0)) == 0 and sp.cancel(resid_pb_schur / u0).is_polynomial(u0, u1, u2))

# ---- (C3) FIX-A: blowup OUTERMOST (stepMap = blockBlowup ∘ shear), φ KEEPS the pivot. ----
def phi_keep_pivot(w):  # free-ish but keeps pivot (φ_pivot=0); reads spectator, writes center 1
    return [sp.Integer(0), w[2], sp.Integer(0)]
sm_orderflip = blockBlowup(blockShear(phi_keep_pivot, u))   # blowup last
check("(C3) FIX-A order-flip (blowup last), φ keeps pivot: ALL center coords ∘ stepMap ∈ ⟨u0⟩",
      all(sp.simplify(sm_orderflip[i].subs(u0, 0)) == 0 for i in center))

# ---- (C4) FIX-B: constrain the (render-order) φ so its center displacements ∈ ⟨center coords⟩. ----
# (C2 already exhibits a member of this class working; state the class check explicitly.)
check("(C4) FIX-B center-supported φ (C2's Schur shape) restores render-order divisibility",
      sp.simplify(resid_pb_schur.subs(u0, 0)) == 0)

print("\nCONCLUSION: case12 δ=1 divisibility is FALSE for a FREE ed.shearφ (C1); the fold's REAL Schur φ")
print("is center-supported and safe (C2). The render's composition order (edgeShear ∘ blockBlowupMap =")
print("shear AFTER blowup) is what admits the break; the certificate's β∘σ_shear (blowup LAST) does not.")
print("STOP-ON-SUSPECT: the statement needs EITHER FIX-A (blowup outermost + φ keeps pivot) OR FIX-B")
print("(φ's center displacements ∈ ⟨center coords⟩). CenterCoordAligned (injectivity) does NOT suffice.")
print(f"\nL4 shear-alignment checkpoint: {'PASS (gap confirmed)' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)
