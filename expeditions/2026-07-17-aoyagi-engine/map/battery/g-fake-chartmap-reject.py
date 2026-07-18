#!/usr/bin/env python3
# guards: coverage-theorem, resolution-tree
# config: identity "chart" (r1 fake chartMap=id) fails LeafPullback (P) on raw (2,2,2); real chart needed
# provenance: threads/01-skeleton (architect-t01, repair pass, item 7(a)); companion to g-chart-bridge-pullback
"""Fake-chartMap rejection (item 7(a)): the identity chart cannot satisfy the loss-pullback (P).

The r1 witness used `chartMap = id` with `srcBox = univ`. `LeafPullback` demands, on the source box,

    F o chartMap = (prod_k u_k^2) * R,     lo * base <= R <= hi * base   (lo > 0),

with `u_k` the divisor coordinates and `base` the residual base form (`||z||^2` Morse core, order 2,
or the unit `1`). This battery shows the IDENTITY chart fails (P) on the raw (2,2,2) fibre loss, so a
fake `chartMap = id` is rejected by reading -- only a real blow-up chart (g-chart-bridge-pullback.py)
monomializes.

RAW LOSS: F = ||A.B||^2, A,B generic 2x2 (the fibre-over-0 loss, 8 coordinates). Under `chartMap = id`
there is NO blow-up, so the only monomial you can factor out is the gcd of F's monomials.

REJECT (a): no single coordinate divides F  => the factorable divisor monomial is 1 (prod u^2 = 1).
REJECT (b): with monomial 1, R = F, and F vanishes at the origin to order 4 (A.B is bilinear, so F is
degree 4 with zero Hessian at 0). So F is neither a bounded unit (F(0)=0) nor squeezable by an
order-2 base form: F/||z||^2 -> 0, so `lo*||z||^2 <= F` FAILS for every lo>0 near 0.
Hence (P) is unsatisfiable for `chartMap = id`.

CONTRAST (c): the real (2,2,2) blow-up chart DOES satisfy (P) exactly (asserted in the companion
battery), so the rejection is specific to the fake, not to (2,2,2).

Exit 0 iff (a) no coordinate divides F; (b) F(0)=0 and Hessian_0(F)=0 (order > 2); together (P) fails
for the identity chart.
"""
import sys
import sympy as sp

a = sp.Matrix(2, 2, lambda i, j: sp.Symbol(f"a{i}{j}", real=True))
b = sp.Matrix(2, 2, lambda i, j: sp.Symbol(f"b{i}{j}", real=True))
coords = list(a) + list(b)
AB = sp.expand(a * b)
F = sp.expand(sum(e**2 for e in AB))

# (a) no single coordinate divides F  =>  gcd-monomial is 1  =>  prod u^2 = 1 under chartMap=id
none_divides = all(sp.rem(F, c) != 0 for c in coords)

# (b) F(0) = 0 (not a unit) AND Hessian at 0 is the zero matrix (vanishing order > 2, not Morse)
F0 = F.subs({c: 0 for c in coords})
H0 = sp.hessian(F, coords).subs({c: 0 for c in coords})
vanishes_high = (F0 == 0) and (H0 == sp.zeros(len(coords), len(coords)))

# so no monomial + order-2 base-form squeeze works: identity chart fails (P)
pullback_fails_for_id = none_divides and vanishes_high
ok = pullback_fails_for_id

print(f"(a) no coordinate divides raw F => factorable monomial is 1: {none_divides}")
print(f"(b) F(0)=0 and Hessian_0(F)=0 (order>2, not a unit, not order-2 Morse): {vanishes_high}")
print(f"=> identity chart (r1 fake chartMap=id) fails LeafPullback (P): {pullback_fails_for_id}")
print("   (the real blow-up chart satisfies (P) exactly -- see g-chart-bridge-pullback.py)")
sys.exit(0 if ok else 1)
