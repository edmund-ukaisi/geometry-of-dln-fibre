#!/usr/bin/env python3
# guards: exponent-ledger-bridge, hbox-root
# config: paper worked examples: minAdm (2,2,2)->3, (2,1,2)->2, (2,2,2,2)->3, (3,3,4)->8; lambda=minAdm/2
# provenance: theory/aoyagi-2023-reproduction/verify-arith-groundtruth.md (red-team PASS)
"""Ground-truth guard binding the minAdm recursion to the paper's worked values.

lambda((2,2,2)) = 3/2, lambda((2,1,2)) = 1, lambda((2,2,2,2)) = 3/2 are the
reproduction's verified cross-checks; minAdm = 2*lambda. Exit 0 iff all match."""
import sys
from fractions import Fraction
from _minadm import minAdm

expect = {(2, 2, 2): 3, (2, 1, 2): 2, (2, 2, 2, 2): 3, (3, 3, 4): 8}
bad = {M: (minAdm(M), v) for M, v in expect.items() if minAdm(M) != v}
lam_ok = Fraction(minAdm((2, 2, 2)), 2) == Fraction(3, 2)
print(f"mismatches={bad}  lambda(2,2,2)=minAdm/2=3/2: {lam_ok}")
sys.exit(0 if (not bad and lam_ok) else 1)
