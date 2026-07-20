#!/usr/bin/env python3
# guards: resolution-tree
# config: lct(d^2(x^2+y^2)) = 1/2 vs lct(d1^2 x^2 + d2^2 y^2) = 1
# provenance: threads/00-genesis/paper-read-cert.md §6 (flattened-invariant counterexample)
"""Threshold-only summaries break: sharing one blow-up variable vs two.

Exact monomial-rule arithmetic (rationals):
(a) f = d^2(x^2+y^2), vars (d,x,y). Polar (x,y)->(r,angle) is measure-preserving up
    to bounded angle factor; f = d^2 r^2 with volume element r dr. Monomial rule per
    variable: lct = min over vars (h+1)/(2k): d -> (0+1)/(2*1)=1/2, r -> (1+1)/(2*1)=1.
    lct = 1/2.
(b) g = d1^2 x^2 + d2^2 y^2 — a sum in DISJOINT variable pairs; lct adds (Watanabe
    additivity, cited): lct(d^2 x^2) per pair = min(1/2, 1/2) = 1/2; total = 1.
Same "one quadratic relation, one corank pattern" summary; different thresholds.
So the tree's node data must record WHICH divisor divides WHICH generator.
Exit 0 iff the exact arithmetic gives 1/2 != 1."""
import sys
from fractions import Fraction

def monomial_lct(pairs):
    """lct of a monomial ∏ v_i^(2k_i) against volume ∏ v_i^(h_i) dv: min (h_i+1)/(2k_i)."""
    return min(Fraction(h + 1, 2 * k) for k, h in pairs)

lct_a = monomial_lct([(1, 0), (1, 1)])   # d^2 r^2 with r dr: vars d (k=1,h=0), r (k=1,h=1) -> 1/2
lct_pair = monomial_lct([(1, 0), (1, 0)])  # d^2 x^2: vars d, x each (k=1,h=0) -> 1/2
lct_b = lct_pair + lct_pair              # disjoint-variable additivity (cited: Watanabe) -> 1
ok = (lct_a == Fraction(1, 2)) and (lct_b == 1) and (lct_a != lct_b)
print(f"lct(shared)={lct_a}  lct(split)={lct_b}  distinct={ok}")
sys.exit(0 if ok else 1)
