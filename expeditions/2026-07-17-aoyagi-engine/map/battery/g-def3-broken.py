#!/usr/bin/env python3
# guards: exponent-ledger-bridge
# config: Def 3's printed non-member inequality forces empty selection at ell=1
# provenance: theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex (typo ledger T-D)
"""Transcription guard: NEVER transcribe the paper's Definition-3 inequalities.

The printed condition (sum over selected <= (ell-1) * M^(s) for non-members) forces
sum <= 0 at ell = 1, rejecting the size-2 selections Theorem 1 requires. This guard
re-derives the brokenness on concrete vectors so any future transcription of the
printed form fails loudly. The banked replacement is the geometric 1/2*min_t Mval(t)
form. Exit 0 iff the printed rule is empty on >0 of the tested vectors while the
recursion gives a finite positive value."""
import sys, itertools
from _minadm import minAdm

def printed_def3_selects(Ms):
    # try all nonempty selections; printed conditions with ell = |sel| - 1
    ok_sels = []
    for r in range(1, len(Ms) + 1):
        for sel in itertools.combinations(range(len(Ms)), r):
            ell = len(sel) - 1
            S = sum(Ms[i] for i in sel)
            in_ok = all(S > ell * Ms[i] for i in sel)
            out_ok = all(S <= (ell - 1) * Ms[i] for i in range(len(Ms)) if i not in sel)
            if in_ok and out_ok:
                ok_sels.append(sel)
    return ok_sels

empties = 0
for Ms in itertools.product(range(1, 4), repeat=3):
    if not printed_def3_selects(list(Ms)):
        empties += 1
sane = minAdm((2, 2, 2)) == 3
print(f"printed Def-3 empty on {empties}/27 small vectors; recursion sane: {sane}")
sys.exit(0 if (empties > 0 and sane) else 1)
