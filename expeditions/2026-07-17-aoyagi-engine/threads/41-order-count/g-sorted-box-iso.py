#!/usr/bin/env python3
"""Kill-battery for the SORTED-BOX iso (seat-Ecore, P6.2 Tier-3 last factor).

Target: for sorted (monotone) positive widths D : Fin (L+1) -> N,
  bindingSet D  ≃o  BoxPart (ell) (a)
where ell = qipM D, a = residueA D (.toNat), order = pointwise <= on profiles.

Verifies, on a sweep of monotone positive D:
  (1) |bindingSet D| == |BoxPart ell a| == C(ell, a)
  (2) the pivotal fact: on each binding profile, active steps x_i in {C-1, C} for i<ell,
      and increments e_i = 0 for i>=ell, with exactly a of the x_i == C.
  (3) the encoding enc(T) lands in BoxPart (antitone, bounded by ell-a).
  (4) BOTH directions of order-reflection: for all binding T, T':
        (T <= T' pointwise)  <->  (enc T <= enc T' pointwise)     [THE HAZARD]
  (5) enc is a bijection onto BoxPart.
"""
from itertools import product
from math import comb, ceil

def qipA(D, l):
    N = len(D) - 1
    s = sum(D[min(i, N)] for i in range(l + 1))
    return s - l * D[min(l, N)]

def qipM(D):
    N = len(D) - 1
    best = 0
    for l in range(0, N + 1):
        if qipA(D, l) >= 0:
            best = l
    return best

def qipS(D):
    N = len(D) - 1
    m = qipM(D)
    return sum(D[min(i, N)] for i in range(m + 1))

def ell_of(D):
    return qipM(D)

def ceilingM(D):
    l = ell_of(D); S = qipS(D)
    if l == 0:
        return 0  # int div by 0 = 0 in Lean
    return (S + l - 1) // l  # ceil(S/l)

def residueA(D):
    l = ell_of(D); S = qipS(D); C = ceilingM(D)
    return S - (C - 1) * l

def admissible(D, T):
    """T : list length L. admPred: bounds, weak-decrease, last=0."""
    L = len(T)
    if L == 0:
        return True
    # bounds
    for j in range(L):
        bound = min(D[0], D[1]) if j == 0 else D[j + 1]
        if T[j] > bound:
            return False
    # weak decrease
    for i in range(L):
        for j in range(i, L):
            if T[j] > T[i]:
                return False
    # last = 0
    if T[L - 1] != 0:
        return False
    return True

def Mval(D, T):
    L = len(T)
    tot = 0
    for j in range(L):
        tPrev = D[0] if j == 0 else T[j - 1]
        tot += (tPrev - T[j]) * (D[j + 1] - T[j])
    return tot

def all_adm(D):
    L = len(D) - 1
    if L == 0:
        return [tuple()]
    caps = []
    for j in range(L):
        bound = min(D[0], D[1]) if j == 0 else D[j + 1]
        caps.append(bound)
    out = []
    for T in product(*[range(c + 1) for c in caps]):
        if admissible(D, list(T)):
            out.append(tuple(T))
    return out

def binding_set(D):
    adm = all_adm(D)
    if not adm:
        return []
    mv = min(Mval(D, list(T)) for T in adm)
    return [T for T in adm if Mval(D, list(T)) == mv]

def sIncr(D, T, i):
    if i == 0:
        return D[0] - T[0]
    return T[i - 1] - T[i]

def sStep(D, T, i):
    return sIncr(D, T, i) + D[i + 1]

def box_subset(D, T):
    """A = {i<ell : x_i == C}."""
    l = ell_of(D); C = ceilingM(D)
    return sorted([i for i in range(l) if sStep(D, T, i) == C])

def enc(D, T):
    """box element f : Fin a -> N,  f_i = p_{a-1-i} - (a-1-i)."""
    A = box_subset(D, T)
    a = len(A)
    return tuple(A[a - 1 - i] - (a - 1 - i) for i in range(a))

def all_box(l, a):
    """antitone f: Fin a -> N bounded by l-a (Lean ℕ-subtraction: max(l-a,0))."""
    K = max(l - a, 0)
    if a == 0:
        return [tuple()]
    out = []
    for f in product(range(K + 1), repeat=a):
        if all(f[i] >= f[i + 1] for i in range(a - 1)):
            out.append(f)
    return out

def le_ptwise(x, y):
    return all(xi <= yi for xi, yi in zip(x, y))

def check(D):
    D = list(D)
    L = len(D) - 1
    l = ell_of(D); C = ceilingM(D); a = residueA(D)
    B = binding_set(D)
    box = all_box(l, max(a, 0))
    errs = []
    # L=0 (ell=0): iso is singleton-singleton (separate trivial Lean branch); the
    # position-encoding is degenerate here (no active positions), so only check cards.
    if L == 0:
        if not (len(B) == 1 and len(box) == 1):
            errs.append(f"L=0 not singleton-singleton: |bind|={len(B)} |box|={len(box)}")
        return errs
    # (1) cardinalities
    if l >= 1:
        if len(B) != comb(l, a):
            errs.append(f"|binding|={len(B)} != C({l},{a})={comb(l,a)}")
    if len(B) != len(box):
        errs.append(f"|binding|={len(B)} != |box|={len(box)}")
    # (2) pivotal fact + (3) enc lands in box
    encs = []
    for T in B:
        # increments >=0
        for i in range(L):
            if sIncr(D, T, i) < 0:
                errs.append(f"neg incr T={T} i={i}")
        # e_i = 0 for i>=ell
        for i in range(l, L):
            if sIncr(D, T, i) != 0:
                errs.append(f"nonzero incr past ell T={T} i={i}")
        # x_i in {C-1,C} for i<ell
        for i in range(l):
            if sStep(D, T, i) not in (C - 1, C):
                errs.append(f"step not in pair T={T} i={i} x={sStep(D,T,i)} C={C}")
        # exactly a of x_i == C
        A = box_subset(D, T)
        if len(A) != a:
            errs.append(f"|A|={len(A)} != a={a} T={T}")
        f = enc(D, T)
        encs.append((T, f))
        # in box: antitone + bounded
        if any(f[i] < f[i + 1] for i in range(len(f) - 1)):
            errs.append(f"enc not antitone T={T} f={f}")
        if any(fi > l - a for fi in f):
            errs.append(f"enc not bounded T={T} f={f} bound={l-a}")
    # (5) bijection onto box
    encset = set(ff for _, ff in encs)
    if encset != set(box):
        errs.append(f"enc image {sorted(encset)} != box {sorted(box)}")
    # (4) BOTH directions of order-reflection (THE HAZARD)
    for (T1, f1) in encs:
        for (T2, f2) in encs:
            le_T = le_ptwise(T1, T2)
            le_f = le_ptwise(f1, f2)
            if le_T != le_f:
                errs.append(f"ORDER MISMATCH T1={T1} T2={T2} f1={f1} f2={f2} "
                            f"le_T={le_T} le_f={le_f}")
    return errs

def monotone_positive_widths(maxL, maxW):
    for L in range(0, maxL + 1):
        # D : length L+1, monotone, entries in 1..maxW
        for D in product(range(1, maxW + 1), repeat=L + 1):
            if all(D[i] <= D[i + 1] for i in range(L)):
                yield D

def main():
    total = 0
    fails = 0
    trap_cores = [(1, 1, 1, 2), (2, 3, 3, 4), (2, 2, 2), (1, 1, 2),
                  (2, 2, 2, 2, 2), (1, 1, 4), (2, 2, 4), (1, 2, 3, 4)]
    print("=== trap / worked cores ===")
    for D in trap_cores:
        errs = check(D)
        total += 1
        status = "OK" if not errs else "FAIL"
        if errs:
            fails += 1
        l = ell_of(list(D)); a = residueA(list(D)); C = ceilingM(list(D))
        print(f"D={D}  (ell,a,C)=({l},{a},{C})  |binding|={len(binding_set(list(D)))}  {status}")
        for e in errs[:5]:
            print("    ", e)
    print("\n=== exhaustive sweep (monotone positive, L<=4, W<=5) ===")
    for D in monotone_positive_widths(4, 5):
        errs = check(D)
        total += 1
        if errs:
            fails += 1
            if fails <= 20:
                print(f"FAIL D={D}: {errs[:3]}")
    print(f"\nTOTAL {total} cores, {fails} FAIL")
    print("EXIT", 0 if fails == 0 else 1)
    return 0 if fails == 0 else 1

if __name__ == "__main__":
    import sys
    sys.exit(main())
