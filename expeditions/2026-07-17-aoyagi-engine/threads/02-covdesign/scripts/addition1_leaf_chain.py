#!/usr/bin/env python3
"""Addition (1): does region_glue's SEPARATED product form hold at a corank>=2 leaf?

region_glue integrand = prod_k u_k^{(divExp_k - 1) - 2c'}  => threshold = min_k divExp_k/2.
Question: at a genuine normal-crossing leaf Sum_i b_i^2 (b_i monomials in exceptional u's),
is rlct = min_k divExp_k/2 (SEPARATED), or must it consult `support` (COUPLED, additive)?

MECHANISM: Aoyagi's b_i form a DIVISIBILITY CHAIN b_1 | b_2 | ... . Then
   Sum_i b_i^2 = b_1^2 (1 + (b_2/b_1)^2 + ...) = b_1^2 * unit,
a SINGLE dominant monomial times a unit, so rlct = rlct(b_1^2) = min over b_1's divisors of
divExp/2 -- the SEPARATED form is EXACT. The chain is what the blow-ups establish; it is the
reason a sum-of-squares leaf behaves like min, not additive.

KILL: if a node is declared a leaf while its b's are INCOMPARABLE (no chain -- e.g. b_1=u1, b_2=u2,
a Morse sum), the SEPARATED form UNDERSHOOTS (min 1/2 vs true additive 1). So IsFullMonomialization
(chain established) is the precondition region_glue rides on; region_glue does NOT need a coupled
integrand -- the coupling lives in the divExp values (sharing-aware) + WHICH leaves exist.

We verify EXACTLY (Newton-LP): valid chain leaf => Newton-LP(Sum b_i^2) == min divExp/2;
incomparable "leaf" => Newton-LP > min divExp/2 (undershoot, not a real leaf).
"""
import sys
from fractions import Fraction as F
sys.path.insert(0, "/tmp")
from rlct_newton import rlct_monomial_ideal


def minhalf(gens, nvars):
    """min over single generators of (sum of exponents)/2  -- the SEPARATED product-form threshold
    for a single-monomial-per-divisor reading (each divisor u_k: ratio = divExp_k/2, divExp_k = its
    exponent in the dominant monomial +Jacobian; for these bare blow-up divisors divExp = mult)."""
    # For a genuine chain leaf b_1^2*unit, divExp_k = exponent of u_k in b_1; ratio = divExp_k/2;
    # threshold = min over u_k in b_1 of divExp_k/2. Here we read it off the SMALLEST generator.
    return None  # (computed inline per case for clarity)


cases = [
    # (name, generators (b_i exponent vectors), nvars, is_chain, dominant b_1 index)
    ("chain  b1=u1, b2=u1u2",        [(1, 0), (1, 1)], 2, True, 0),
    ("chain  b1=u1, b2=u1u2, b3=u1u2u3", [(1,0,0),(1,1,0),(1,1,1)], 3, True, 0),
    ("INCOMPARABLE b1=u1, b2=u2 (Morse, NOT a leaf)", [(1, 0), (0, 1)], 2, False, None),
    ("INCOMPARABLE <d1 x, d2 y> (2,2,1) residual", [(1,0,1,0),(0,1,0,1)], 4, False, None),
]
ok = True
for name, gens, nv, is_chain, b1 in cases:
    true_rlct = rlct_monomial_ideal(gens, nv)
    if is_chain:
        # dominant monomial b_1 = gens[b1]; F = b_1^2 * unit; rlct = min over u_k in b_1 of 1/(2*mult)
        b = gens[b1]
        sep = min(F(1, 2 * e) for e in b if e > 0)   # min divExp/2 with divExp = mult in b_1
        agree = (true_rlct == sep)
        ok &= agree
        print(f"[chain] {name:44s} NewtonLP={true_rlct}  min-divExp/2={sep}  MATCH:{agree}")
    else:
        # a naive "min over ALL generators' divisors" separated reading
        sep_naive = min(F(1, 2 * e) for g in gens for e in g if e > 0)
        undershoot = (sep_naive < true_rlct)
        ok &= undershoot
        print(f"[NON ] {name:44s} NewtonLP(additive)={true_rlct}  naive-sep-min={sep_naive}  "
              f"UNDERSHOOT:{undershoot} (=> not a genuine leaf; needs more blow-up)")
print("\nSETTLED: separated form EXACT at a divisibility-chain leaf; UNDERSHOOTS at a non-chain node."
      if ok else "\nUNEXPECTED")
sys.exit(0 if ok else 1)
