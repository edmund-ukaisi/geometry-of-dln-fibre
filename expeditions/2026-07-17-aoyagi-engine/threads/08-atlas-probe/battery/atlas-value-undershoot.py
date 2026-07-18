#!/usr/bin/env python3
# guards: coverage-theorem, resolution-tree
# provenance: threads/08-atlas-probe (pen-and-paper pnp08, DECORRELATED atlas-closure probe).
#   Formulae pinned to Aoyagi 2023 PAGE IMAGES p.14-22 (Mval p.22; minAdm = the paper's
#   nested minimisation = RouteMLayerSplit.minAdmRec). NOT read from the Lean engine.
"""COMPUTATION 1 (atlas closure), decorrelated value + no-undershoot instrument.

Three exact checks, all integer/rational (no float, no Monte-Carlo):

(1) minAdm(M) equals min over NESTED rank-profiles t=(t^1>=...>=t^L=0),
    t^j<=min(t^{j-1},M^{j+1})  [t^0:=M^1], of Aoyagi's terminal divisor exponent
        Mval(t) = (M^1-t^1)(M^2-t^1) + sum_{j=2}^L (t^{j-1}-t^j)(M^{j+1}-t^j)     (p.22)
    -- i.e. the paper's own candidate-min IS the minAdm recursion. Establishes the
    TARGET value and the admissible-profile atlas independently of the Lean engine.

(2) NO-UNDERSHOOT over the admissible profiles: every emitted terminal exponent
    Mval(t) >= minAdm(M) (tautological given (1); displayed so an off-profile emission
    would show as < minAdm). The genuine undershoot risk is a MIS-TRACKED divisor
    (sharing conflated/independentised) -- checked in the sibling kill-cond battery.

(3) COORDINATE-WEIGHT valuation bound (a genuinely independent obstruction hunt):
    for any positive weight w on the C-entries, lambda_0 <= (sum w)/(2 ord_w(J)); the
    best coordinate-weight bound has (sum w)/ord_w(J) = M^2 * min(M^1,M^3) [L=2, proved
    below by LP decoupling over the shared index k]. If this were < minAdm it would be a
    PROVEN undershoot. We report it and whether it reaches minAdm (it does NOT -- the
    binding divisor is a genuine rank blow-up, not a coordinate monomial).
"""
import sys
from functools import lru_cache
from itertools import product as iproduct
from fractions import Fraction as F


@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(int(x) for x in M)
    if len(M) == 1:
        return 0
    if len(M) == 2:
        return M[0] * M[1]
    return min((M[0] - t) * (M[1] - t) + minAdm((t,) + M[2:])
               for t in range(min(M[0], M[1]) + 1))


def Mval(M, t):
    """Aoyagi p.22 terminal divisor exponent for profile t=(t^1,...,t^L), len(t)=L=len(M)-1."""
    L = len(M) - 1
    assert len(t) == L
    v = (M[0] - t[0]) * (M[1] - t[0])
    for j in range(2, L + 1):           # j = 2..L
        v += (t[j - 2] - t[j - 1]) * (M[j] - t[j - 1])   # (t^{j-1}-t^j)(M^{j+1}-t^j)
    return v


def nested_profiles(M):
    """All nested profiles t^1>=...>=t^L=0 with t^1<=min(M^1,M^2), t^j<=min(t^{j-1},M^{j+1})."""
    L = len(M) - 1
    out = []

    def rec(prefix, prev_bound):
        j = len(prefix) + 1          # building component t^j
        if j == L:
            out.append(tuple(prefix) + (0,))     # t^L forced 0 (tilde_t=0)
            return
        hi = min(prev_bound, M[j])   # t^j <= min(t^{j-1}, M^{j+1})  (M[j] is M^{j+1})
        for tj in range(hi + 1):
            rec(prefix + [tj], tj)

    if L == 1:
        return [(0,)]
    rec([], min(M[0], M[1]))
    return out


def coord_weight_bound(M):
    """L=2 best coordinate-weight ratio (sum w)/ord_w(J).  LP decouples over shared index k:
    per k, min (sum_i a_ik + sum_j b_kj) s.t. a_ik+b_kj>=1  ->  min(M^1,M^3); times M^2 values of k."""
    assert len(M) == 3
    return M[1] * min(M[0], M[2])


def report(M):
    M = tuple(M)
    L = len(M) - 1
    profs = nested_profiles(M)
    vals = {t: Mval(M, t) for t in profs}
    mn = min(vals.values())
    argmins = sorted(t for t, v in vals.items() if v == mn)
    ma = minAdm(M)

    print(f"=== M={M}  (L={L}) ===")
    print(f"  admissible nested profiles (t^L=0): {len(profs)}")
    for t in sorted(profs):
        flag = "  <-- MIN" if vals[t] == mn else ""
        under = "  ** UNDERSHOOT **" if vals[t] < ma else ""
        print(f"    t={t}:  Mval={vals[t]}   half={F(vals[t],2)}{flag}{under}")
    print(f"  min_t Mval = {mn}   at {argmins}")
    print(f"  minAdm({M}) = {ma}")
    check1 = (mn == ma)
    check2 = all(v >= ma for v in vals.values())
    print(f"  (1) min_t Mval == minAdm : {check1}")
    print(f"  (2) no admissible-profile undershoot (all Mval>=minAdm): {check2}")
    if L == 2:
        cw = coord_weight_bound(M)
        print(f"  (3) best COORDINATE-weight ratio (sum w)/ord_w = M^2*min(M^1,M^3) = {cw}")
        print(f"      -> coord-weight lambda bound = {F(cw,2)} ; minAdm/2 = {F(ma,2)} ; "
              f"coord-weight {'UNDERSHOOTS' if cw < ma else 'does NOT undershoot'} "
              f"(reaches minAdm: {cw == ma})")
    print()
    return check1 and check2


ok = True
for M in [(2, 2, 2), (3, 3, 4)]:
    ok &= report(M)

# extra corroboration: the two ground-truth RRR anchors from the reproduction
print("=== cross-checks vs reproduction ground truth (RRR / AW-2005) ===")
for M, want_half in [((2, 2, 2), F(3, 2)), ((3, 3, 4), F(4, 1)), ((2, 1, 2), F(1)), ((1, 1, 3), F(1, 2))]:
    got = F(minAdm(M), 2)
    tag = "OK" if got == want_half else "MISMATCH"
    ok &= (got == want_half)
    print(f"  M={M}: minAdm/2={got}  expected lambda_core={want_half}  {tag}")

print("\nALL CHECKS PASS" if ok else "\nFAILED")
sys.exit(0 if ok else 1)
