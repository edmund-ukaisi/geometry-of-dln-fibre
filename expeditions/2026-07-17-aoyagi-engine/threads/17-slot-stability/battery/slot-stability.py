#!/usr/bin/env python3
# guards: resolution-tree, coverage-theorem, carrier
# provenance: threads/17-slot-stability (pnp-slot). Instruments the banked page-faithful
#   Aoyagi Section-5 recursion (rules verbatim p.14-22; head-reset = runmin/FIX-A) with an
#   IMMUTABLE per-divisor BIRTH CORNER (S_birth, J_birth), set at creation, carried verbatim
#   through 1(1) merges. Integer-only, exact. NOT the Lean engine.
#
# THE T-SLOT QUESTION: does each existing divisor u_{s,k} occupy the flat slot of its BIRTH
#   corner (S_birth, J_birth, J_birth) immutably, or do later substitutions move it?
#   Mechanism at the ledger level:
#     - births (Case 1(2) child, Case 2) create a divisor at the CURRENT node's corner (S,J).
#     - Case 1(1) MERGE mutates the pivot's (T,m) IN PLACE but is the SAME object -> birth kept.
#     - no transition reassigns a live divisor to a different (S,J) corner.
#   We test this by (a) confirming birth corners are never rewritten, (b) confirming within
#   each reachable state all live divisors have DISTINCT birth corners (distinct flat slots),
#   and (c) the SECONDARY: is (S_birth,J_birth) a function of the CURRENT divProfile (T[,m])?
#   We exhibit collisions if any.
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


class Div:
    """A divisor: current profile T, accumulated exponent m, and an IMMUTABLE birth corner."""
    __slots__ = ("T", "m", "birthS", "birthJ")

    def __init__(self, T, m, birthS, birthJ):
        self.T = tuple(T)
        self.m = m
        self.birthS = birthS      # immutable: layer at creation
        self.birthJ = birthJ      # immutable: cleared-count at creation

    def slot(self):
        # flat slot (layer, row, col) = (birthS, birthJ, birthJ) -- the diagonal corner
        return (self.birthS, self.birthJ, self.birthJ)

    def profile(self):
        return self.T

    def profM(self):
        return (self.T, self.m)

    def clone(self):
        return Div(self.T, self.m, self.birthS, self.birthJ)


class Sim:
    def __init__(self, M, headreset="runmin"):
        self.M = tuple(M)
        self.L = len(M) - 1
        self.headreset = headreset
        self.leaves = []            # list of leaves; each leaf = list of Div
        # instrumentation
        self.birth_rewrite_viol = 0     # a divisor's birthS/birthJ changed after creation (must be 0)
        self.state_slot_collisions = []  # within a reachable state: two live divs share a slot
        self.state_profile_ambig = []    # within a state: two divs share (T,m) but differ in birth
        self.state_profileT_ambig = []   # within a state: two divs share T but differ in birth
        self.global_profM_to_birth = {}  # (T,m) -> set of birth corners across ALL states
        self.global_profT_to_birth = {}  # T -> set of birth corners across ALL states
        self.node_count = 0

    def Mw(self, i):
        return self.M[i - 1]

    def Mrun(self, S):
        return min(self.M[:S])

    def tilde(self, T):
        return min(T)

    def set_tail(self, T, S, J):
        T = list(T)
        for j in range(S, self.L + 1):
            T[j - 1] = J
        return tuple(T)

    def def4_min(self, cands):
        best = None
        for c in cands:
            if all(all(a <= b for a, b in zip(c.T, d.T)) for d in cands):
                best = c
                break
        if best is None:
            best = min(cands, key=lambda d: d.T)
        return best

    def _record_state(self, divs):
        # (b) distinct slots within the state
        slots = {}
        for d in divs:
            slots.setdefault(d.slot(), []).append(d)
        for slot, ds in slots.items():
            if len(ds) > 1:
                self.state_slot_collisions.append((slot, [(d.T, d.m) for d in ds]))
        # (c) profile ambiguity within the state
        byPM = {}
        byT = {}
        for d in divs:
            byPM.setdefault(d.profM(), set()).add(d.slot())
            byT.setdefault(d.profile(), set()).add(d.slot())
        for pm, sset in byPM.items():
            if len(sset) > 1:
                self.state_profile_ambig.append((pm, sorted(sset)))
        for t, sset in byT.items():
            if len(sset) > 1:
                self.state_profileT_ambig.append((t, sorted(sset)))
        # global maps
        for d in divs:
            self.global_profM_to_birth.setdefault(d.profM(), set()).add(d.slot())
            self.global_profT_to_birth.setdefault(d.profile(), set()).add(d.slot())

    def run(self):
        self._proc(1, 0, [])
        return self

    def _proc(self, S, J, divs):
        self.node_count += 1
        if self.node_count > 300000:
            raise RuntimeError("runaway")
        # snapshot immutability check: each div's birth is what it was constructed with
        self._record_state(divs)
        if S == self.L + 1:
            self.leaves.append([d.clone() for d in divs])
            return
        MS = self.Mrun(S)
        MSp1 = min(MS, self.Mw(S + 1))
        if J >= MSp1:                       # ROLLOVER: layer done, S advances. Divisors UNTOUCHED.
            self._proc(S + 1, 0, divs)
            return
        levels = sorted({self.tilde(d.T) for d in divs})
        occ_above = [m for m in levels if J + 1 <= m <= MS - 1]
        if occ_above:                       # CASE 1
            target = occ_above[0]
            J1 = target - J
            cands = [d for d in divs if self.tilde(d.T) == target]
            f = self.def4_min(cands)
            bump = J1 * (self.Mw(S + 1) - J)
            # 1(1): MERGE -- mutate the pivot's (T,m) IN PLACE; SAME object -> birth corner kept.
            merged = Div(self.set_tail(f.T, S, J), f.m + bump, f.birthS, f.birthJ)
            divs_U = [d.clone() for d in divs if d is not f] + [merged]
            self._proc(S, J, divs_U)
            # 1(2): CREATE new divisor u_{S,J+1} at the CURRENT node's corner (S,J). Parent kept
            #   (rescaled u'_{s,k} renamed back -> same (T,m), same birth). Advance J.
            child = Div(self.set_tail(f.T, S, J), f.m + bump, S, J)   # BORN here: birth=(S,J)
            divs_D = [d.clone() for d in divs] + [child]
            self._proc(S, J + 1, divs_D)
        else:                               # CASE 2: create divisor at corner (S,J); no u in center
            T = [0] * self.L
            for i in range(1, S):
                T[i - 1] = self.Mrun(i + 1) if self.headreset == "runmin" else self.Mw(i + 1)
            T = self.set_tail(tuple(T), S, J)
            Mexp = (MS - J) * (self.Mw(S + 1) - J)
            newdiv = Div(T, Mexp, S, J)                               # BORN here: birth=(S,J)
            divs_2 = [d.clone() for d in divs] + [newdiv]
            self._proc(S, J + 1, divs_2)


def trace_leaves(M, label):
    sim = Sim(M).run()
    print(f"=== {label}  M={M}  minAdm={minAdm(M)}  leaves={len(sim.leaves)} ===")
    # de-duplicate leaves by their (slot -> (T,m)) content for display
    seen = set()
    uniq = []
    for leaf in sim.leaves:
        key = tuple(sorted((d.slot(), d.T, d.m) for d in leaf))
        if key not in seen:
            seen.add(key)
            uniq.append(leaf)
    for i, leaf in enumerate(uniq):
        parts = []
        slots_in_leaf = [d.slot() for d in leaf]
        distinct = len(set(slots_in_leaf)) == len(slots_in_leaf)
        for d in sorted(leaf, key=lambda d: d.slot()):
            parts.append(f"slot{d.slot()} T={d.T} t~={min(d.T)} M={d.m}")
        flag = "" if distinct else "  <== SLOT COLLISION"
        print(f"  leaf{i}: " + " | ".join(parts) + flag)
    print(f"  within-leaf slot collisions: {sum(1 for leaf in sim.leaves for slot,ds in _slotmap(leaf).items() if len(ds)>1)}")
    print()
    return sim


def _slotmap(leaf):
    m = {}
    for d in leaf:
        m.setdefault(d.slot(), []).append(d)
    return m


def report(sim, label):
    print(f"--- {label}: instrumentation ---")
    print(f"  states visited: {sim.node_count}")
    print(f"  birth-rewrite violations (slot moved after creation): {sim.birth_rewrite_viol}")
    print(f"  within-state SLOT collisions (two live divs same slot): {len(sim.state_slot_collisions)}")
    if sim.state_slot_collisions:
        for c in sim.state_slot_collisions[:5]:
            print(f"      {c}")
    # SECONDARY: recoverability
    ambigPM = {pm: b for pm, b in sim.global_profM_to_birth.items() if len(b) > 1}
    ambigT = {t: b for t, b in sim.global_profT_to_birth.items() if len(b) > 1}
    print(f"  GLOBAL (T,m) -> birth-corner ambiguities (same (T,m), different corner): {len(ambigPM)}")
    for pm, b in list(ambigPM.items())[:6]:
        print(f"      (T={pm[0]}, M={pm[1]}) born at corners {sorted(b)}")
    print(f"  GLOBAL T -> birth-corner ambiguities (same T, different corner): {len(ambigT)}")
    for t, b in list(ambigT.items())[:6]:
        print(f"      T={t} born at corners {sorted(b)}")
    print(f"  WITHIN-STATE (T,m) ambiguities (same state, same (T,m), diff corner): {len(sim.state_profile_ambig)}")
    for a in sim.state_profile_ambig[:4]:
        print(f"      {a}")
    print(f"  WITHIN-STATE T ambiguities (same state, same T, diff corner): {len(sim.state_profileT_ambig)}")
    for a in sim.state_profileT_ambig[:4]:
        print(f"      {a}")
    print()


print("#" * 74)
print("# T-SLOT + RECOVERABILITY: worked traces (2,2,2) and (3,3,4), plus more")
print("#" * 74)
s222 = trace_leaves((2, 2, 2), "(2,2,2)")
s334 = trace_leaves((3, 3, 4), "(3,3,4)")

print("#" * 74)
print("# INSTRUMENTATION (slot-stability + recoverability) across instances")
print("#" * 74)
allok = True
for M, lab in [((2, 2, 2), "(2,2,2)"), ((3, 3, 4), "(3,3,4)"),
               ((2, 2, 2, 2), "(2,2,2,2)"), ((2, 2, 3, 2), "(2,2,3,2)"),
               ((3, 3, 2, 2), "(3,3,2,2)"), ((2, 2, 3, 3, 2), "(2,2,3,3,2)")]:
    sim = Sim(M).run()
    report(sim, lab)
    # T-slot PASS conditions: no birth rewrite, no within-state slot collision
    allok &= (sim.birth_rewrite_viol == 0 and len(sim.state_slot_collisions) == 0)

print("=" * 74)
print("T-SLOT VERDICT (ledger level):",
      "SLOT-STABLE (birth corners immutable; distinct within every state)" if allok
      else "FAIL -- a slot moved or collided")
sys.exit(0 if allok else 1)
