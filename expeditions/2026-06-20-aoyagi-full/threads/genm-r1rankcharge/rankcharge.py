#!/usr/bin/env python3
"""
genm-r1rankcharge — EXACT-ARITHMETIC adjudication of the RANK-CORRECTED descent charge.

Question (A): over the full R1-UPPER recursion tree (redChain descent), does the sum of
per-step rank-corrected charges  a*s  (s = rank Q_b at each chart) reach EXACTLY minAdm M?

Objects (all integer / exact):
  Mval, admBound, admPred, Adm, minAdm   -- FAITHFUL reimplementation of the Lean defs
                                             (Lambda.lean, RouteMLayerSplit.lean).
  minAdmRec                               -- the ab layer-peeling recursion (Lean minAdmRec).
  minAdmRank                              -- the a*s rank-corrected recursion (the NEW object).

Rank formula (derived, load-bearing):
  peel boundary 0 of chain N=(N0,N1,...,Nk) with pivot t (t <= min(N0,N1)):
     a = N0 - t,  b = N1 - t,  n = min(N2,...,Nk)  (tail bottleneck; leaf if k<2)
     s = rank Q_b = min(b, n)          [generic rank of b non-pivot rows of the tail product,
                                        whose generic rank is min(N1,...,Nk); restricted to b<=N1 rows]
     ab-charge  = a*b   (the current Lean peelCharge = LayerSplit codim)
     as-charge  = a*s   (the rank-corrected charge)
  recurse on redChain = (t, N2, ..., Nk).
"""
from itertools import product
from functools import lru_cache

# ---------- FAITHFUL brute-force minAdm (the Lean definition) ----------
def tPrev(M, T, j):
    # t^{(j-1)} with t^{(0)} := M0
    return M[0] if j == 0 else T[j-1]

def Mval(M, T):
    # sum_{j=0}^{L-1} (tPrev_j - T_j)*(M_{j+1} - T_j)   over ints
    L = len(M) - 1
    return sum((tPrev(M, T, j) - T[j]) * (M[j+1] - T[j]) for j in range(L))

def admBound(M, j):
    return min(M[0], M[1]) if j == 0 else M[j+1]

def admPred(M, T):
    L = len(M) - 1
    # (1) block bound
    if any(T[j] > admBound(M, j) for j in range(L)):
        return False
    # (2) weak decrease: i<=j => T[j] <= T[i]  (i.e. nonincreasing)
    for i in range(L):
        for j in range(i, L):
            if T[j] > T[i]:
                return False
    # (3) last exponent zero
    if L >= 1 and T[L-1] != 0:
        return False
    return True

def minAdm_brute(M):
    L = len(M) - 1
    if L == 0:
        return 0
    bounds = [admBound(M, j) for j in range(L)]
    best = None
    for T in product(*[range(bnd+1) for bnd in bounds]):
        if admPred(M, T):
            v = Mval(M, T)
            if best is None or v < best:
                best = v
    return best  # toNat: min is >=0 for these chains

# ---------- the ab layer-peeling recursion (Lean minAdmRec) ----------
def redChain(t, M):
    return (t,) + tuple(M[2:])

@lru_cache(maxsize=None)
def minAdmRec(M):
    L = len(M) - 1
    if L == 0:
        return 0
    if L == 1:
        return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t) + minAdmRec(redChain(t, M))
               for t in range(min(M[0], M[1])+1))

# ---------- the a*s rank-corrected recursion (the NEW object) ----------
def tail_bottleneck(M):
    # n = min(M2,...,ML); None if leaf
    return min(M[2:]) if len(M) >= 3 else None

@lru_cache(maxsize=None)
def minAdmRank(M):
    L = len(M) - 1
    if L == 0:
        return 0
    if L == 1:
        return M[0]*M[1]
    n = tail_bottleneck(M)
    best = None
    for t in range(min(M[0], M[1])+1):
        a = M[0]-t
        b = M[1]-t
        s = min(b, n)
        charge = a*s
        v = charge + minAdmRank(redChain(t, M))
        if best is None or v < best:
            best = v
    return best

# ---------- per-cut breakdown at the TOP level (the gate) ----------
def top_gate(M):
    """For each cut t at the top boundary, report ab-charge, as-charge, minAdm(redChain),
       and the two sums.  Uses the TRUE minAdm (=minAdmRec) on redChain."""
    n = tail_bottleneck(M)
    rows = []
    for t in range(min(M[0], M[1])+1):
        a = M[0]-t; b = M[1]-t
        s = min(b, n) if n is not None else b
        rc = redChain(t, M)
        mrc = minAdmRec(rc)
        rows.append(dict(t=t, a=a, b=b, s=s, ab=a*b, aS=a*s,
                         redChain=rc, minAdm_rc=mrc,
                         ab_sum=a*b+mrc, aS_sum=a*s+mrc))
    return rows

def report(M):
    M = tuple(M)
    mb = minAdm_brute(M)
    mr = minAdmRec(M)
    mrank = minAdmRank(M)
    print(f"\n===== M = {M} =====")
    print(f"  minAdm(brute)   = {mb}")
    print(f"  minAdmRec(ab)   = {mr}   [{'OK' if mr==mb else 'MISMATCH!!'}]")
    print(f"  minAdmRank(a*s) = {mrank}   [{'CLOSES (==minAdm)' if mrank==mb else 'FAILS: '+str(mrank)+' < '+str(mb) if mrank<mb else 'ABOVE?!'}]")
    if len(M) >= 3:
        print("  top-level per-cut gate (charge + minAdm(redChain)):")
        print("    t | a b s | ab  a*s | redChain      minAdm_rc | ab_sum  aS_sum")
        for r in top_gate(M):
            flag = ""
            if r['aS_sum'] < mb: flag = "  <-- aS_sum BELOW minAdm !!"
            print(f"    {r['t']} | {r['a']} {r['b']} {r['s']} | {r['ab']:>2}  {r['aS']:>3} | "
                  f"{str(r['redChain']):<13} {r['minAdm_rc']:>3}     | {r['ab_sum']:>3}     {r['aS_sum']:>3}{flag}")
        aS_min = min(r['aS_sum'] for r in top_gate(M))
        print(f"  => min_t (a*s + minAdm_rc) = {aS_min}   (minAdm = {mb})   "
              f"{'EQUAL' if aS_min==mb else 'BELOW by '+str(mb-aS_min)}")

# ---------- anchors from the mission ----------
for M in [(2,4,1),(3,3,4),(3,3,3,4),(4,4,2,2),(2,2,2),(2,2,2,2),(2,2,2,3),(1,1,1,4)]:
    report(M)
