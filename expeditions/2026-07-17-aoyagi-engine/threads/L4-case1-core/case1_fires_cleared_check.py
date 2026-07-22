#!/usr/bin/env python3
# provenance: threads/L4-case1-core (SEAT-L4). C1 truth-check (team-lead assignment): can conOracle reach
# the case1 dispatch branch (EngineConstruction :2125) with cleared = 0? FAITHFUL model of the LEAN oracle
# (exact defs: divTilde=min-of-profile, widthMinUpto, runMinWidth, setTail, the 3 transitions, the
# filterMap eligibility). Enumerates ALL reachable states; flags any cleared=0 state taking case1.
"""
Lean conOracle dispatch at state s=(layer, cleared, profiles) [profiles: list of L-tuples]:
  terminal  if L ≤ layer
  rollover  elif widthMinUpto M (layer+1) ≤ cleared           → (layer+1, 0, profiles)   [cleared→0, divisors carried]
  else: eligible = {k : cleared+1 ≤ divTilde k  ∧  divTilde k + 1 ≤ widthMinUpto M layer}
        if eligible ≠ ∅:  CASE1 (target=min divTilde over eligible; f=chooseMin=componentwise-min at target)
              child11: profiles[f] ↦ setTail(layer,cleared,profiles[f]);  cleared UNCHANGED
              child12: profiles + [setTail(layer,cleared,profiles[f])];   cleared+1
        else:             CASE2:  profiles + [setTail(layer,cleared,runMinWidth M)];  cleared+1
  divTilde(prof) = min(prof);  setTail(layer,cl,T)[p] = cl if layer≤p else T[p];
  widthMinUpto M n = min(M_0..M_min(n,L));  runMinWidth M p = min(M_0..M_{p+1}).
THE QUESTION: does any reachable state have cleared=0 AND eligible≠∅ (case1 fires)?
"""
import sys
from functools import lru_cache

def widthMinUpto(M, n):
    L = len(M) - 1
    return min(M[i] for i in range(0, min(n, L) + 1))

def runMinWidth(M, p):          # p in 0..L-1 ; = min(M_0..M_{p+1})
    return min(M[i] for i in range(0, p + 2))

def divTilde(prof):
    return min(prof)

def setTail(layer, cleared, T): # T an L-tuple
    return tuple(cleared if layer <= p else T[p] for p in range(len(T)))

def choose_min(profiles, at_level):
    """chooseMin: first divisor at divTilde=at_level that is componentwise ≤ all others at that level."""
    cands = [k for k, pr in enumerate(profiles) if divTilde(pr) == at_level]
    for k in cands:
        if all(all(profiles[k][j] <= profiles[k2][j] for j in range(len(profiles[k]))) for k2 in cands):
            return k
    return None   # fallback (should not happen on a chain state)

def dispatch(M, state):
    L = len(M) - 1
    layer, cleared, profiles = state
    if L <= layer:
        return ("terminal", [])
    if widthMinUpto(M, layer + 1) <= cleared:
        return ("rollover", [(layer + 1, 0, profiles)])
    wlayer = widthMinUpto(M, layer)
    eligible = [k for k, pr in enumerate(profiles)
                if cleared + 1 <= divTilde(pr) and divTilde(pr) + 1 <= wlayer]
    if eligible:
        target = min(divTilde(profiles[k]) for k in eligible)
        f = choose_min(profiles, target)
        if f is None:
            return ("terminal(fallback)", [])
        pf = profiles[f]
        st = setTail(layer, cleared, pf)
        child11 = (layer, cleared, tuple(st if k == f else profiles[k] for k in range(len(profiles))))
        child12 = (layer, cleared + 1, profiles + (st,))
        return ("case1", [child11, child12])
    else:
        st = setTail(layer, cleared, tuple(runMinWidth(M, p) for p in range(L)))
        return ("case2", [(layer, cleared + 1, profiles + (st,))])

def enumerate_reachable(M, max_states=200000):
    L = len(M) - 1
    root = (0, 0, tuple())          # conRoot: layer 0, cleared 0, no divisors
    seen = set(); stack = [root]; case1_at_cleared0 = []
    while stack:
        s = stack.pop()
        if s in seen: continue
        seen.add(s)
        if len(seen) > max_states:
            return None, None       # blew up
        kind, children = dispatch(M, s)
        if kind == "case1" and s[1] == 0:
            case1_at_cleared0.append(s)
        for c in children:
            if c not in seen:
                stack.append(c)
    return seen, case1_at_cleared0

ok = True
def check(name, cond):
    global ok; ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

Ms = [(3,3,4), (2,2,2), (2,2,2,2), (2,2,3,2), (3,3,2,2), (3,2,4,2), (2,2,3,3,2), (4,3,3,4), (2,3,2,3)]
print("Faithful Lean-conOracle reachability sweep — case1 at cleared=0?")
any_violation = False
for M in Ms:
    seen, viol = enumerate_reachable(M)
    if seen is None:
        print(f"  M={M}: state space too large (skipped)"); continue
    n_c0 = sum(1 for s in seen if s[1] == 0)
    status = "NONE (holds)" if not viol else f"*** {len(viol)} case1-at-cleared0 states ***"
    print(f"  M={M!s:14} reachable={len(seen):5}  cleared=0 states={n_c0:3}  case1@cleared0: {status}")
    if viol:
        any_violation = True
        for v in viol[:3]:
            layer, cleared, profs = v
            tildes = [divTilde(p) for p in profs]
            print(f"      TRACE: layer={layer} cleared=0 profiles-divTilde={tildes} "
                  f"widthMinUpto(layer)={widthMinUpto(M, layer)}")

# EXPECTED: REFUTED. The lemma case1_fires_only_at_cleared_pos is FALSE — case1 fires at cleared=0
# pervasively (first state of every post-rollover layer: carried divisors from the previous layer have
# 1 ≤ divTilde < widthMinUpto(layer), hence eligible). This battery PASSES by CONFIRMING the refutation.
check("REFUTED: case1 DOES fire at cleared=0 in reachable states (every test instance, incl. rollovers)",
      any_violation)

# cross-validation: the banked (3,3,4) traversal (edgespec_traversal_334.py, all assertions pass) prints
#   S=2 J=0 case1(1) δ=1 reuse-pivot t=1  ((1,1),4)→((1,0),8)
#   S=2 J=0 case1(1) δ=1 reuse-pivot t=2  ((2,2),1)→((2,0),9)
# i.e. case1(1) MERGE edges at J=0 (cleared=0) with δ=1 — matching this model exactly.
print(f"\ncase1_fires_only_at_cleared_pos truth-check: "
      f"{'PASS — REFUTATION CONFIRMED (lemma is FALSE)' if ok else 'FAIL'}")
print("VERDICT (C1, team-lead assignment): the lemma is FALSE. case1 fires at cleared=0 REACHABLY and")
print("  PERVASIVELY — at the first state of every post-rollover layer, the carried divisors (divTilde")
print("  1..widthMinUpto−1 from the previous layer's clears) are eligible. Refuting trace (3,3,4):")
print("    case2,case2,case2,rollover → (layer=1, cleared=0, divTilde=[0,1,2]) → CASE1 (target=1).")
print("  Cross-validated by the banked (3,3,4) traversal: 'S=2 J=0 case1(1) δ=1' MERGE edges.")
print("  THE DANGER is specifically the case11 MERGE sub-branch: case11 keeps cleared UNCHANGED (=0),")
print("  so supportAt(child)=supportAt(layer,0)=blockCoords(layer) does NOT descend, yet edgeδ=[cleared=0]")
print("  =1 triggers the strict transform (shifts the residual support DOWN a layer) — the GAP-1 mismatch")
print("  ⟹ conjunct-2 breaks. case12 SPLIT / case2 at cleared=0 ADVANCE cleared (child cleared=1 ⟹")
print("  supportAt descends to blockCoords(layer+1), matching the strict transform) — those are FINE.")
print("  NB the construction USES δ=1 at these case11 merges (banked traversal: 'δ=[J=0] uniform' asserts")
print("  PASS) — the u_pivot IS removed there for conjunct-1's monomial bookkeeping — so the fix is NOT")
print("  simply δ=0. FALLBACK (elder's design call, per team-lead 'edgeδ case-aware'): reconcile the δ=1")
print("  strict-transform descend with case11's cleared-invariance — either a case-aware edgeδ, or a")
print("  case-aware supportAt/DescendView that descends the child support for a case11 merge (so S' tracks")
print("  the strict transform, not just cleared). Folds into the combined bake.")
sys.exit(0 if ok else 1)
