#!/usr/bin/env python3
"""Exhaustive exact sweep: does minAdmRank(a*s) == minAdm on ALL small chains?
   Also validates minAdmRec == minAdm_brute (instrument check)."""
from rankcharge import (minAdm_brute, minAdmRec, minAdmRank, redChain,
                         tail_bottleneck, minAdm_brute as MB)
from itertools import product

def sweep(Lplus1, wmax, wmin=0, brute=True):
    """all chains of Lplus1 widths in [wmin..wmax]."""
    n_checked = 0
    instrument_fail = []
    close_fail = []          # minAdmRank < minAdm  (the CLOSURE-BREAKING set)
    above = []               # minAdmRank > minAdm  (should be impossible)
    for M in product(range(wmin, wmax+1), repeat=Lplus1):
        M = tuple(M)
        mr = minAdmRec(M)
        mrank = minAdmRank(M)
        if brute:
            mb = minAdm_brute(M)
            if mr != mb:
                instrument_fail.append((M, mr, mb))
        base = mr  # trust minAdmRec == minAdm (validated separately)
        if mrank < base:
            close_fail.append((M, mrank, base))
        elif mrank > base:
            above.append((M, mrank, base))
        n_checked += 1
    return n_checked, instrument_fail, close_fail, above

print("Sweep 1: L+1=3 (L=2), widths 0..6  [brute-validated]")
n, ifail, cfail, ab = sweep(3, 6, brute=True)
print(f"  checked {n}: instrument_fail={len(ifail)}  close_fail={len(cfail)}  above={len(ab)}")
if ifail: print("   INSTRUMENT FAIL:", ifail[:10])
if cfail: print("   CLOSURE FAIL   :", cfail[:20])

print("Sweep 2: L+1=4 (L=3), widths 0..5  [brute-validated]")
n, ifail, cfail, ab = sweep(4, 5, brute=True)
print(f"  checked {n}: instrument_fail={len(ifail)}  close_fail={len(cfail)}  above={len(ab)}")
if ifail: print("   INSTRUMENT FAIL:", ifail[:10])
if cfail: print("   CLOSURE FAIL   :", cfail[:20])

print("Sweep 3: L+1=5 (L=4), widths 0..4  [brute-validated]")
n, ifail, cfail, ab = sweep(5, 4, brute=True)
print(f"  checked {n}: instrument_fail={len(ifail)}  close_fail={len(cfail)}  above={len(ab)}")
if ifail: print("   INSTRUMENT FAIL:", ifail[:10])
if cfail: print("   CLOSURE FAIL   :", cfail[:20])

print("Sweep 4: L+1=6 (L=5), widths 0..4  [recursion-only, no brute]")
n, ifail, cfail, ab = sweep(6, 4, brute=False)
print(f"  checked {n}: close_fail={len(cfail)}  above={len(ab)}")
if cfail: print("   CLOSURE FAIL   :", cfail[:20])

print("Sweep 5: L+1=4 (L=3), widths 0..8  [recursion-only, wide]")
n, ifail, cfail, ab = sweep(4, 8, brute=False)
print(f"  checked {n}: close_fail={len(cfail)}  above={len(ab)}")
if cfail: print("   CLOSURE FAIL   :", cfail[:20])

print("Sweep 6: L+1=7 (L=6), widths 0..3  [recursion-only, deep]")
n, ifail, cfail, ab = sweep(7, 3, brute=False)
print(f"  checked {n}: close_fail={len(cfail)}  above={len(ab)}")
if cfail: print("   CLOSURE FAIL   :", cfail[:20])
