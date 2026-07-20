#!/usr/bin/env python3
# guards: exponent-ledger-bridge
# config: form A minAdm <= u*deepTailMin + (M0-u)(M1-u) scanned arities 3-4 widths<=6; tight at (2,2,2),u=1
# provenance: threads/00-genesis/architecture-cert.md (the b*M0-vs-formA discriminator, 2026-07-17)
"""Tightness discriminator guard: inequality-shaped conditions need equality
witnesses at binding cells, not only truth scans.

Form A (the tight interior QIP): minAdm(M) <= u*min(M[2:]) + (M0-u)(M1-u), all
u <= min(M0,M1). The superseded b*M0 form is TRUE but slack at the binding cell —
truth scans cannot separate them; tightness does. Exit 0 iff: form A has zero
violations on the scan, IS tight at (2,2,2) u=1, and the b*M0 form is NOT."""
import sys, itertools
from _minadm import minAdm

viol = tight = 0
for arity in (3, 4):
    for M in itertools.product(range(1, 7), repeat=arity):
        d = min(M[2:])
        for u in range(min(M[0], M[1]) + 1):
            rhs = u * d + (M[0] - u) * (M[1] - u)
            if minAdm(M) > rhs: viol += 1
            elif minAdm(M) == rhs: tight += 1
M, u = (2, 2, 2), 1
formA = u * min(M[2:]) + (M[0] - u) * (M[1] - u)          # 3
bM0 = u * M[2] + (M[1] - u) * M[0]                         # 4
ok = (viol == 0) and (formA == minAdm(M)) and (bM0 > minAdm(M))
print(f"formA: {viol} violations, {tight} tight; binding cell: formA={formA} bM0={bM0} minAdm={minAdm(M)}")
sys.exit(0 if ok else 1)
