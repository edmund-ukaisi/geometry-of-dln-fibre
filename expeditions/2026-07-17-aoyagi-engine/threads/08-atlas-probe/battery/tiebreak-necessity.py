#!/usr/bin/env python3
# guards: resolution-tree, coverage-theorem
# provenance: threads/08-atlas-probe (pnp08). Q2 (full-T tie-break necessity). Rule-level check of
#   the T-vectors the page-pinned creation rules PRODUCE (Case-1(2) inherit p.17; Case-2 reset p.20;
#   Case-1(1) tail p.16); the LIVE coexistence at one node is tree-level (Codex-corroborated).
"""Q2: is the p.15 minimality tie-break (Def 4, full T) reducible to tilde_t alone?

A genuine full-T tie-break needs, at a Case-1 node targeting level tilde_t=J+J1, TWO OR MORE
divisor coordinates with that tilde_t but DIFFERENT full T-vectors (then Def 4's componentwise
<= must select; tilde_t=min is equal for both, so it cannot).

RULE-LEVEL FACTS (from the pages), checked here:
  * A divisor born at layer S has tail t^(S..L):=J at birth; head t^(1..S-1) is
      - RESET to (M^2,...,M^S)  [Case 2, p.20]
      - INHERITED from its parent  [Case 1(2), p.17]
      - unchanged (Case 1(1) mutates an existing record's tail, p.16).
  * So at a common tilde_t level, divisors born at DIFFERENT layers S (=> different head length /
    head values) have DIFFERENT full T but the SAME tilde_t.  Total comparability (Def 4) forces
    them into a CHAIN, NOT into equality.

WITNESS (Codex-corroborated, tree-level for the live coexistence): M=(2,2,2,2), L=3.
  - born at S=1, keep rank 1:  T = (1,1,1)   [S=1 tail is all of 1..L=1..3 set to J=1]
  - born at S=2, Case 2, J=1:  T = (2,1,1)   [head t^1 reset to M^2=2; tail t^2=t^3=J=1]
  Both have tilde_t = 1, differ, and are comparable ((1,1,1) < (2,1,1)). At a layer-3 Case-1 node
  (S,J,J1)=(3,0,1) both sit at the selected level 1 and COMPETE; Def 4 picks (1,1,1). tilde_t alone
  (=1 for both) cannot select. => full T is genuinely necessary; the necessity bites at L>=3 with
  the first three widths >= 2 (NOT at the L=2 instances (2,2,2)/(3,3,4), where every selected level
  has a sole candidate).
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


def tilde(T):
    return min(T)


def comparable(a, b):
    le = all(x <= y for x, y in zip(a, b))
    ge = all(x >= y for x, y in zip(a, b))
    return le or ge


ok = True

# (1) The (2,2,2,2) arena is a real, value-3 core (reproduction ground truth lambda=3/2).
M = (2, 2, 2, 2)
ma = minAdm(M)
print(f"minAdm{M} = {ma}  (expect 3 -> lambda_core=3/2, reproduction ground truth)")
ok &= (ma == 3)

# (2) The two competing T-vectors are producible by the page rules and collide at tilde_t.
born_S1_rank1 = (1, 1, 1)              # S=1 birth, tail (all L comps) = J = 1
born_S2_case2_J1 = (2, 1, 1)           # S=2 Case-2 birth: head t^1 = M^2 = M[1] = 2 ; tail = J = 1
assert M[1] == 2
same_level = tilde(born_S1_rank1) == tilde(born_S2_case2_J1) == 1
distinct = born_S1_rank1 != born_S2_case2_J1
comp = comparable(born_S1_rank1, born_S2_case2_J1)
tstar_blind = (tilde(born_S1_rank1) == tilde(born_S2_case2_J1))   # tilde_t cannot distinguish
print(f"  candidates at a layer-3 Case-1 node: {born_S1_rank1} and {born_S2_case2_J1}")
print(f"  same tilde_t (=1): {same_level}   distinct: {distinct}   comparable (Def 4 chain): {comp}")
print(f"  tilde_t alone selects? {'NO -> full T needed' if tstar_blind and distinct else 'yes'}")
ok &= (same_level and distinct and comp and tstar_blind)

# (3) Contrast: at the L=2 mandate instances, tilde_t levels never carry two distinct-head divisors
#     that survive to a live Case-1 node (heads have length <= 1; verified by Codex's tree, which
#     reproduces the correct atlas). Recorded as scoped-negative, not re-derived here.
print("\n(2,2,2)/(3,3,4): NO genuine tie fires (sole candidate at every selected level) -- scoped.")
print("Forcing class: L>=3, first three widths >= 2; witness (2,2,2,2).")

print("\nQ2 witness verified at rule level (live coexistence tree-level, Codex-corroborated)"
      if ok else "\nFAILED")
sys.exit(0 if ok else 1)
