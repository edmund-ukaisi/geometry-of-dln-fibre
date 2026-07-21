#!/usr/bin/env python3
"""thread-31 (pnp-monument) reproducibility battery.

Recomputes Aoyagi's terminal accumulated exponent Mval(t) (worked.tex:533) for the
instances threads 27/28 pinned, plus the Case-2 raw-width defect instance and the
T-profile incomparability Codex flagged. Asserts the exact numbers the certificate cites.
Exact integer arithmetic; no floats. EXIT 0 = all cross-checks pass.
"""
from itertools import product


def Mval(M, t):
    """Aoyagi worked.tex:533. M = (M^1..M^{L+1}) reduced widths (len L+1);
    t = (t^1..t^L) weakly-decreasing rank profile of the branch (len L)."""
    L = len(t)
    assert len(M) == L + 1, (M, t)
    val = (M[0] - t[0]) * (M[1] - t[0])
    for j in range(2, L + 1):                       # paper j = 2..L
        val += (t[j - 2] - t[j - 1]) * (M[j] - t[j - 1])
    return val


def Gqip(d, e):
    """The QIP objective G_d(e) = sum_{j<=i} e_i (e_j + d_j - d_{j-1}), i,j in 1..N.
    d = (d_0..d_N); e : Fin N -> N with sum e = d_0 (the antidiagonal)."""
    N = len(e)
    tot = 0
    for i in range(N):
        for j in range(N):
            if j <= i:
                tot += e[i] * (e[j] + d[j + 1] - d[j])
    return tot


def qipMin(d):
    N = len(d) - 1
    feas = [e for e in product(range(d[0] + 1), repeat=N) if sum(e) == d[0]]
    return min(Gqip(d, e) for e in feas)


checks = []

# (3,3,4): terminal (t1, 0); min 8 at t1=1 -> rlct 4 (thread 27).
row = {t1: Mval((3, 3, 4), (t1, 0)) for t1 in range(4)}
checks.append(("(3,3,4) row", row == {0: 9, 1: 8, 2: 9, 3: 12} and min(row.values()) == 8))

# (4,4,4): terminal (t1, 0); min 12 at t1=2 -> rlct 6 (thread 28).
row = {t1: Mval((4, 4, 4), (t1, 0)) for t1 in range(5)}
checks.append(("(4,4,4) row", row == {0: 16, 1: 13, 2: 12, 3: 13, 4: 16} and min(row.values()) == 12))

# (3,3,2,2) t=(2,1,0) -> 4, rlct 2 (thread 27); (3,3,3,2,2) t=(2,2,1,0) -> 4, rlct 2 (thread 28).
checks.append(("(3,3,2,2)", Mval((3, 3, 2, 2), (2, 1, 0)) == 4))
checks.append(("(3,3,3,2,2)", Mval((3, 3, 3, 2, 2), (2, 2, 1, 0)) == 4))

# (2,2,3,2) Case-2 defect: raw label (2,3,0)->6 (Mval) but physical running-min (2,2,0)->4;
# qipMin = 3 (non-binding, no undershoot).
checks.append(("(2,2,3,2) raw label", Mval((2, 2, 3, 2), (2, 3, 0)) == 6))
checks.append(("(2,2,3,2) physical", Mval((2, 2, 3, 2), (2, 2, 0)) == 4))
checks.append(("(2,2,3,2) qipMin", qipMin((2, 2, 3, 2)) == 3))
checks.append(("(2,2,3,2) defect non-binding", Mval((2, 2, 3, 2), (2, 2, 0)) > qipMin((2, 2, 3, 2))))

# (2,2,1,1) T-profile incomparability (Codex): (1,1,1) and (2,1,0) both Mval 1, componentwise incomparable.
a, b = (1, 1, 1), (2, 1, 0)
incomp = not (all(x <= y for x, y in zip(a, b)) or all(y <= x for x, y in zip(a, b)))
checks.append(("(2,2,1,1) both Mval 1", Mval((2, 2, 1, 1), a) == 1 and Mval((2, 2, 1, 1), b) == 1))
checks.append(("(2,2,1,1) incomparable", incomp))

ok = True
for name, passed in checks:
    print(f"[{'PASS' if passed else 'FAIL'}] {name}")
    ok = ok and passed

assert ok, "a cross-check FAILED"
print("\nALL PASS — instance Mvals reconcile with threads 27/28 + the Case-2 defect + Codex incomparability.")
