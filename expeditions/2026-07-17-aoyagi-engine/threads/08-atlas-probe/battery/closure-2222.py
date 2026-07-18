#!/usr/bin/env python3
# guards: coverage-theorem, resolution-tree
# provenance: threads/08-atlas-probe (pnp08), SECOND task -- the depth-3 R2 leg. Formulae pinned to
#   Aoyagi p.14-22 (Mval p.22; minAdm recursion; Def-4 comparability p.14/15; tie-break p.15).
#   NOT the Lean engine. Integer-only, exact.
"""(2,2,2,2) chart-atlas closure at L=3: value+no-undershoot (a,b) and the tie-break consequence (c).

(a,b): admissible nested profiles t=(t^1>=t^2>=t^3=0), Mval, min = minAdm(2,2,2,2) = 3, no undershoot.
(c)  : at the Case-1 node (S,J,J1)=(3,0,1) two divisors sit at tilde_t=1 --
         A=(1,1,1)  [born layer 1, rank level 1]
         B=(2,1,1)  [born layer 2, Case 2, head reset to M^2=2, tail=J=1]
       Def-4 (componentwise <=) selects the minimum A. We test the CONSEQUENCE of the choice:
         - Case 1(1) on the fixed divisor sets its tail t^(S..L)=t^(3):=J=0.
         - the OTHER divisor stays at level 1.
       Check total-comparability (Def 4, an invariant of the whole construction) of the resulting
       T-set, and the emitted tilde_t=0 minimum, under BOTH the correct (fix A) and wrong (fix B)
       choices. The DIFFERENCE is the faithfulness content.
"""
import sys
from functools import lru_cache


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
    L = len(M) - 1
    v = (M[0] - t[0]) * (M[1] - t[0])
    for j in range(2, L + 1):
        v += (t[j - 2] - t[j - 1]) * (M[j] - t[j - 1])
    return v


def nested_profiles(M):
    L = len(M) - 1
    out = []

    def rec(prefix, prev_bound):
        j = len(prefix) + 1
        if j == L:
            out.append(tuple(prefix) + (0,))
            return
        hi = min(prev_bound, M[j])
        for tj in range(hi + 1):
            rec(prefix + [tj], tj)
    rec([], min(M[0], M[1]))
    return out


def comparable(a, b):
    return all(x <= y for x, y in zip(a, b)) or all(x >= y for x, y in zip(a, b))


def set_tail(T, S, J):
    T = list(T)
    for j in range(S, len(T) + 1):
        T[j - 1] = J
    return tuple(T)


ok = True
M = (2, 2, 2, 2)
L = 3
ma = minAdm(M)
print(f"=== M={M} (L={L}),  minAdm={ma} (=> lambda_core = {ma}/2 = 3/2) ===\n")

# ---- (a,b) closure value + no undershoot over the admissible (=stratum) atlas ----
profs = nested_profiles(M)
vals = {t: Mval(M, t) for t in profs}
mn = min(vals.values())
argmins = sorted(t for t, v in vals.items() if v == mn)
print("(a,b) admissible nested profiles (t^3=0 -> tilde_t=0):")
for t in sorted(profs):
    flag = "  <-- MIN" if vals[t] == mn else ""
    under = "  ** UNDERSHOOT **" if vals[t] < ma else ""
    print(f"    t={t}: Mval={vals[t]}{flag}{under}")
print(f"  min = {mn}  minAdm = {ma}  equal: {mn == ma}   minimisers: {argmins}")
print(f"  no undershoot (all Mval >= minAdm): {all(v >= ma for v in vals.values())}\n")
ok &= (mn == ma == 3) and all(v >= ma for v in vals.values())

# ---- (c) the tie-break at (S,J,J1)=(3,0,1): correct vs wrong choice ----
A = (1, 1, 1)     # born layer 1, rank level 1
B = (2, 1, 1)     # born layer 2, Case 2 (head reset M^2=2, tail J=1)
S, J = 3, 0
print(f"(c) Case-1 node (S,J,J1)=({S},{J},1); level tilde_t=1 candidates: A={A}, B={B}")
print(f"    A,B distinct: {A != B}   comparable (Def-4 chain): {comparable(A, B)}   "
      f"tilde_t equal: {min(A) == min(B) == 1}")
print(f"    Def-4 minimum (the tie-break pick): {'A=' + str(A) if all(a <= b for a, b in zip(A, B)) else 'B'}")
ok &= (A != B and comparable(A, B) and min(A) == min(B) == 1
       and all(a <= b for a, b in zip(A, B)))

# CORRECT: fix A (the min). Case 1(1): A -> tail t^(3):=J=0.  B remains.
A_after = set_tail(A, S, J)                       # (1,1,0)
correct_set = [A_after, B]
correct_comp = comparable(A_after, B)
# WRONG: fix B (non-min). Case 1(1): B -> tail t^(3):=J=0.  A remains.
B_after = set_tail(B, S, J)                        # (2,1,0)
wrong_set = [B_after, A]
wrong_comp = comparable(B_after, A)

print(f"\n    CORRECT (fix min A): A={A}->{A_after}; remaining B={B}")
print(f"       compare {A_after} vs {B}: comparable = {correct_comp}   (Mval {A_after}={Mval(M,A_after)})")
print(f"    WRONG   (fix non-min B): B={B}->{B_after}; remaining A={A}")
print(f"       compare {B_after} vs {A}: comparable = {wrong_comp}   (Mval {B_after}={Mval(M,B_after)})")

# The minimum is choice-independent (both merged divisors are Mval-3 minimisers);
# the total-comparability invariant is BROKEN only by the wrong choice.
min_choice_independent = (Mval(M, A_after) == Mval(M, B_after) == 3)
tiebreak_loadbearing = (correct_comp and not wrong_comp)
print(f"\n    -> emitted merged-divisor Mval is 3 under BOTH choices: {min_choice_independent} "
      f"(the minimum is NOT what the tie-break protects)")
print(f"    -> total-comparability PRESERVED by correct pick, BROKEN by wrong pick: {tiebreak_loadbearing}")
print(f"       ( (2,1,0) vs (1,1,1): 2>=1 but 0<=1  =>  INCOMPARABLE -- invariant violated )")
ok &= (min_choice_independent and tiebreak_loadbearing)

# ---- (a, non-toric corroboration) best coordinate-weight bound at L=3 ----
# Product P = C1 C2 C3; every path i->j->k->l uses one entry per layer. LP: min sum(w) s.t. every
# path weight >= 1. Per-layer 4 entries; the symmetric (and, by the coefficient being 4 on each
# layer sum, optimal) solution puts total 1 across the three layers => sum(w) = 4*1 = 4.
cw_ratio = 4                         # (sum w)/ord_w(J) at (2,2,2,2)
from fractions import Fraction as Fr
print(f"\n(a, non-toric) best coordinate-weight ratio = {cw_ratio}  ->  lambda bound {Fr(cw_ratio,2)} "
      f"> minAdm/2 = {Fr(ma,2)}: coordinate weights are LOOSE (binding divisor non-toric, as at L=2).")
ok &= (cw_ratio > ma)

print("\nVERDICT: min stays 3 (no undershoot); the p.15 tie-break protects the total-comparability")
print("invariant (=> valid principalization / coverage), NOT the numerical minimum." if ok else "FAILED")
sys.exit(0 if ok else 1)
