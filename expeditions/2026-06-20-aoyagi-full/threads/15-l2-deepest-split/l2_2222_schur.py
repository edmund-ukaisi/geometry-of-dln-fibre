"""
L=3 core middle factor = (b0 b3 - b1 b2 + b3) = (1+b0)*b3 - b1*b2. Is this a valid CORE coordinate
(unit-Jacobian shift of b3, the (1,1,1,1) middle core var)?

The middle factor M := (1+b0) b3 - b1 b2. As a function of (b0,b1,b2,b3):
  dM/db3 = 1 + b0 = unit (=1 at 0). So b3 -> M is a local diffeo in b3 (at fixed b0,b1,b2), a
  UNIT-DIVISION / unit-Jacobian change. So M is a legitimate replacement for b3 as a core coordinate.

Then core slice = a3 c3 M / unit = (a3)(M)(c3) / unit. With B3:=M as the new middle core var, and
keeping a3, c3, this is the (1,1,1,1) chain product a3 B3 c3 times a unit. CLEAN (1,1,1,1) core.

This is EXACTLY the iterated L1 / Schur structure: M = Schur complement of the middle layer's pivot.
So for L=3 the core is the length-3 chain in the Schur-reduced middle variable -- precisely Aoyagi's
Theorem 3 product reduction (each middle layer contributes its own block-elimination unit).

Verify: M as a coordinate (replace b3) -- Jacobian of (b0,b1,b2,M) wrt (b0,b1,b2,b3) at 0:
"""
import sympy as sp
b0,b1,b2,b3=sp.symbols('b0 b1 b2 b3',real=True)
M=(1+b0)*b3 - b1*b2
J=sp.Matrix([[sp.diff(f,v) for v in [b0,b1,b2,b3]] for f in [b0,b1,b2,M]]).subs({b0:0,b1:0,b2:0,b3:0})
print("Jacobian of (b0,b1,b2,M) wrt (b0,b1,b2,b3) at 0:")
sp.pprint(J)
print("det =", J.det(), " => M is a valid core coordinate replacing b3 (unit-Jacobian).")
print("dM/db3 =", sp.diff(M,b3), " (=1+b0, unit at 0)")
print("""
CONCLUSION (L=3): the core on the regular-zero slice is a3 * M * c3 / unit, where M = (1+b0)b3 - b1 b2
is the middle-layer Schur complement = a valid unit-Jacobian core coordinate. So the (1,1,1,1) chain
product structure is recovered EXPLICITLY via iterated block-elimination (unit-division), exactly as
Aoyagi's Theorem 3 prescribes. The OFF-slice x-dependence (the +x1 x2 b0-cross terms in E11_sub) is the
same 'regular-cross' universal entanglement as L=2, handled by completion-of-squares / the value squeeze.
""")
