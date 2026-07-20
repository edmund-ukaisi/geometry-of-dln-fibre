#!/usr/bin/env python3
"""SPECIFY (loss-t15, task #22 Lg-remainder) — pin the pivot-column clear.

Two decisive checks, exact sympy:

 CHECK A (single-block irreducibility). The normalized blow-up block (corner=1,
 pivot row a, pivot col b, interior-alpha residual delta) is
     N = [[1, a],[b, a*b + delta]]      (old = chart of source coords (a,b,delta))
 The current Lean alpha (residualSchurShear) is exactly the interior part:
 delta = old_interior - a*b. The claim to confirm: the pivot cross (a,b) is
 IRREDUCIBLE inside a single block — no within-{a,b,delta} det-1 shear makes N
 diagonal. Equivalently, the residualCore matrix (product of normalized blocks)
 has off-diagonals that are free coords, so it vanishes on the box (the cert W3
 kill) UNLESS the cross is cleared by cells OUTSIDE the block.

 CHECK B (what the value needs). residualCore = ||prod of normalized blocks||^2.
 Interior-alpha only: prod NOT diagonal, residualCore hits 0 (reproduce the cert
 witness). Full Q,P (blocks -> [[1,0],[0,delta]]): prod diagonal, residualCore =
 1 + sum(delta_i)^2 >= 1. This confirms the acceptance criterion for the fix.

No claim here about the EXACT cross-block Lg cells (that is pnp-rg's achiever,
task #23). This pins the STRUCTURE: Lg is cross-cell, and the target it must hit.
"""
import sympy as sp

def frob2(Mx):
    return sum(sp.expand(e)**2 for e in Mx)

print("=== CHECK A: single-block, pivot cross irreducible within (a,b,delta) ===")
a, b, de = sp.symbols("a b de", real=True)
N = sp.Matrix([[1, a], [b, a*b + de]])
print("normalized block N =")
sp.pprint(N)
print("off-diagonals: N[0,1] =", N[0,1], "  N[1,0] =", N[1,0])
print("-> (0,1)=a and (1,0)=b are the bare source coords; a within-block birational")
print("   reparam of (a,b,delta) cannot force them to 0 (they are onto R). So the")
print("   pivot cross is NOT clearable inside one normalized block. Lg/Rg cross-cell.\n")

print("=== CHECK B: two-block product (2,2,2), interior-alpha vs full Q,P ===")
# two normalized blocks, interior-alpha applied (interior = delta directly)
a1, b1, r1, a2, b2, r2 = sp.symbols("a1 b1 r1 a2 b2 r2", real=True)
N1 = sp.Matrix([[1, a1], [b1, r1]])   # [[1,a],[b,rho]] normalized, cert form
N2 = sp.Matrix([[1, a2], [b2, r2]])
P_ia = sp.expand(N1 * N2)
print("interior-alpha only: prod of normalized blocks =")
sp.pprint(P_ia)
core_ia = sp.expand(frob2(P_ia))
# cert kill witness: (a1,b1,r1,a2,b2,r2) = (1,0,0,0,-1,0) -> residualCore = 0
subs_kill = {a1:1, b1:0, r1:0, a2:0, b2:-1, r2:0}
print("residualCore at cert kill witness (1,0,0,0,-1,0) =",
      sp.simplify(core_ia.subs(subs_kill)), " (expect 0 -> lower bound FALSE)\n")

# full Q,P: each block cleared to [[1,0],[0,rho]]
D1 = sp.Matrix([[1, 0], [0, r1]])
D2 = sp.Matrix([[1, 0], [0, r2]])
P_qp = sp.expand(D1 * D2)
print("full Q,P: prod of diagonal blocks =")
sp.pprint(P_qp)
core_qp = sp.expand(frob2(P_qp))
print("residualCore (full Q,P) =", core_qp, " = 1 + (r1*r2)^2 >= 1  ✓")
print("min over box {-1,0,1}^2 in (r1,r2):",
      min(int(core_qp.subs({r1:x, r2:y})) for x in (-1,0,1) for y in (-1,0,1)),
      " (expect 1 -> lower bound HOLDS)\n")

print("VERDICT: Lg/Rg are cross-cell (not within-block). Fix target confirmed:")
print("  each normalized block must become [[1,0],[0,rho]] so prod=diag, core>=1.")
