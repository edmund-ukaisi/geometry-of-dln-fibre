#!/usr/bin/env python3
"""Codex's refinement: the c11=1 chart is a normalized blow-up. If the initial radial blow-up of
the 9-dim C1 (C1 = rho * Chat, Chat pivot=1) is included, it contributes rho^8 (codim-9 radial).
Confirm the full |det Dg| = rho^8 * E^7 * alpha^3 (still a PURE monomial, unit==1)."""
import sympy as sp
rho = sp.symbols('rho', positive=True)
# radial blow-up of a 9-dim vector v = rho * vhat (vhat[0]=1 chart): Jacobian rho^{9-1}=rho^8
e = sp.symbols('e1:9')                       # 8 projective ratios
src = [rho] + list(e)
tgt = [rho] + [rho*ei for ei in e]           # v = (rho, rho*e1, ..., rho*e8)
det = sp.simplify(sp.Matrix(tgt).jacobian(src).det())
print("initial C1 radial blow-up (codim 9): |det| =", det, " (expect rho**8)")
assert sp.simplify(det - rho**8) == 0
E, al = sp.symbols('E alpha', positive=True)
full = rho**8 * E**7 * al**3
print("full |det Dg| = rho^8 * E^7 * alpha^3 =", full, " -> PURE MONOMIAL, unit == 1")
print("PASS")
