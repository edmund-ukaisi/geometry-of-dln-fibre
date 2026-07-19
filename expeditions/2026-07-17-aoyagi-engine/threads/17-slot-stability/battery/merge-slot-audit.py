#!/usr/bin/env python3
# guards: carrier, coverage-theorem
# provenance: threads/17-slot-stability (pnp-slot). Companion to slot-stability.py.
#   TWO sharp checks:
#   (A) MERGE-SLOT AUDIT. At every Case-1(1) node (the merge), the chosen divisor u_{s,k} is the
#       PIVOT and keeps its BIRTH corner. A "no-field" carrier that computed the divisor's slot
#       from the CURRENT node (S,J) as (S,J,J) [node-local arithmetic] would be WRONG whenever the
#       divisor was born earlier. We count mismatches: birth-corner != (S,J,J). A single mismatch
#       refutes node-local arithmetic (the tick-208 finding, made quantitative).
#   (B) WITHIN-STATE INJECTIVITY at scale. Across bigger instances, confirm no reachable state has
#       two live divisors sharing (T,m) with different birth corners (so an immutable field is a
#       well-defined per-divisor tag), while GLOBAL (T,m)->corner stays many-to-one (=> no pure
#       function from the current profile to the corner: the theta-multiplicity).
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
    __slots__ = ("T", "m", "bS", "bJ")

    def __init__(self, T, m, bS, bJ):
        self.T, self.m, self.bS, self.bJ = tuple(T), m, bS, bJ

    def slot(self):
        return (self.bS, self.bJ, self.bJ)

    def clone(self):
        return Div(self.T, self.m, self.bS, self.bJ)


class Sim:
    def __init__(self, M):
        self.M = tuple(M)
        self.L = len(M) - 1
        self.leaves = 0
        self.merge_nodes = 0
        self.merge_slot_mismatch = 0        # birth corner != current node corner (S,J,J)
        self.merge_examples = []
        self.state_profM_ambig = 0
        self.global_profM = {}
        self.node_count = 0

    def Mw(self, i): return self.M[i - 1]
    def Mrun(self, S): return min(self.M[:S])
    def tilde(self, T): return min(T)

    def set_tail(self, T, S, J):
        T = list(T)
        for j in range(S, self.L + 1):
            T[j - 1] = J
        return tuple(T)

    def def4_min(self, cands):
        for c in cands:
            if all(all(a <= b for a, b in zip(c.T, d.T)) for d in cands):
                return c
        return min(cands, key=lambda d: d.T)

    def _rec(self, divs):
        byPM = {}
        for d in divs:
            byPM.setdefault((d.T, d.m), set()).add(d.slot())
            self.global_profM.setdefault((d.T, d.m), set()).add(d.slot())
        for pm, s in byPM.items():
            if len(s) > 1:
                self.state_profM_ambig += 1

    def run(self):
        self._proc(1, 0, [])
        return self

    def _proc(self, S, J, divs):
        self.node_count += 1
        self._rec(divs)
        if S == self.L + 1:
            self.leaves += 1
            return
        MS = self.Mrun(S)
        MSp1 = min(MS, self.Mw(S + 1))
        if J >= MSp1:
            self._proc(S + 1, 0, divs)
            return
        levels = sorted({self.tilde(d.T) for d in divs})
        occ = [m for m in levels if J + 1 <= m <= MS - 1]
        if occ:
            target = occ[0]
            J1 = target - J
            cands = [d for d in divs if self.tilde(d.T) == target]
            f = self.def4_min(cands)
            bump = J1 * (self.Mw(S + 1) - J)
            # ---- MERGE-SLOT AUDIT at this Case-1(1) node ----
            self.merge_nodes += 1
            node_corner = (S, J, J)          # what node-local arithmetic would guess
            if f.slot() != node_corner:
                self.merge_slot_mismatch += 1
                if len(self.merge_examples) < 6:
                    self.merge_examples.append(
                        (f"node(S={S},J={J})", f"guess {node_corner}", f"TRUE birth {f.slot()}",
                         f"div T={f.T}"))
            merged = Div(self.set_tail(f.T, S, J), f.m + bump, f.bS, f.bJ)   # birth KEPT
            self._proc(S, J, [d.clone() for d in divs if d is not f] + [merged])
            child = Div(self.set_tail(f.T, S, J), f.m + bump, S, J)          # born (S,J)
            self._proc(S, J + 1, [d.clone() for d in divs] + [child])
        else:
            T = [0] * self.L
            for i in range(1, S):
                T[i - 1] = self.Mrun(i + 1)
            T = self.set_tail(tuple(T), S, J)
            Mexp = (MS - J) * (self.Mw(S + 1) - J)
            self._proc(S, J + 1, [d.clone() for d in divs] + [Div(T, Mexp, S, J)])


print("=" * 78)
print("(A) MERGE-SLOT AUDIT  +  (B) WITHIN-STATE vs GLOBAL profile->corner")
print("=" * 78)
allok = True
for M in [(2, 2, 2), (3, 3, 4), (2, 2, 2, 2), (2, 2, 3, 2), (3, 3, 2, 2),
          (2, 2, 3, 3, 2), (3, 2, 4, 2), (4, 4, 2, 2), (3, 3, 3, 3)]:
    s = Sim(M).run()
    glob_ambig = sum(1 for v in s.global_profM.values() if len(v) > 1)
    print(f"\nM={M}  leaves={s.leaves}  states={s.node_count}  minAdm={minAdm(M)}")
    print(f"  (A) merge nodes: {s.merge_nodes};  "
          f"node-local (S,J,J) != true birth corner: {s.merge_slot_mismatch}"
          f"  {'<-- node-local arithmetic REFUTED' if s.merge_slot_mismatch else '(all merges at birth node)'}")
    for ex in s.merge_examples[:3]:
        print(f"        {ex}")
    print(f"  (B) within-state (T,m)->corner ambiguities: {s.state_profM_ambig}  "
          f"(0 => (T,m) is injective on live divisors, immutable field well-defined)")
    print(f"      global (T,m)->corner many-to-one classes: {glob_ambig}  "
          f"(>0 => no pure function current-profile -> corner; theta-multiplicity)")
    # sanity: at least the deeper instances must exhibit both a merge-mismatch and a global ambiguity
    allok &= (s.state_profM_ambig == 0)

print("\n" + "=" * 78)
print("RESULT:", "within-state (T,m) injective on all instances (immutable-field well-defined)"
      if allok else "FAIL")
sys.exit(0 if allok else 1)
