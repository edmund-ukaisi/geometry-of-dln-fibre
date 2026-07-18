#!/usr/bin/env python3
# guards: resolution-tree, coverage-theorem
# provenance: threads/12-realization (pnp-o5), fork-13 o5-IN REALIZATION (the DERIV/⊇ half).
#   FIX-A (runmin) throughout. Integer-only, exact. Extends nonmono-2232-sim.py: same recursion,
#   but every case-1 node BRANCHES (1(1)/1(2)) and we record the decision path + per-divisor birth
#   history, so we can (a) discover the steering rule for a target profile a, (b) verify a
#   deterministic steered path reaches a leaf carrying a.
"""
o5-IN ⊇ half: for every a ∈ Adm(M), exhibit the branch-choice path (1(1)/1(2) at each case-1 node,
chooser = Def-4 minimal, forced) whose leaf carries a t̃=0 divisor with profile a.

DECISIONS along a root->leaf path occur ONLY at case-1 nodes: choose 1(1) (pull the picked eligible
minimum down to level J, stay at J) or 1(2) (fork a copy of it at level J, advance J, keep parent).
Case-2 and rollover (J>=M(S+1)) nodes are forced (single child).
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


def Mrun_of(M, S):
    return min(M[:S])


def nested_profiles(M):
    L = len(M) - 1
    out = []

    def rec(prefix, prev_bound):
        j = len(prefix) + 1
        if j == L:
            out.append(tuple(prefix) + (0,))
            return
        for tj in range(min(prev_bound, M[j]) + 1):
            rec(prefix + [tj], tj)
    if L == 1:
        return [(0,)]
    rec([], min(M[0], M[1]))
    return out


class Div:
    """A carried divisor with identity, so we can trace birth/mutation across the tree."""
    __slots__ = ("T", "M", "id", "born")
    _next = 0

    def __init__(self, T, Mexp, born):
        self.T = tuple(T)
        self.M = Mexp
        self.id = Div._next
        self.born = born          # (S,J,case) description
        Div._next += 1

    def copy_with(self, T=None, Mexp=None, born=None):
        return Div(self.T if T is None else T,
                   self.M if Mexp is None else Mexp,
                   self.born if born is None else born)


class Tracer:
    def __init__(self, M):
        self.M = tuple(M)
        self.L = len(M) - 1
        self.leaves = []          # list of (divs, path) ; path = list of decision dicts

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
        for c in cands:
            if all(all(a <= b for a, b in zip(c.T, d.T)) for d in cands):
                return c
        # not a chain -> record; fall back lex (should not happen under FIX-A)
        return min(cands, key=lambda d: d.T)

    def run(self):
        self._proc(1, 0, [], [])
        return self

    def _proc(self, S, J, divs, path):
        if S == self.L + 1:
            self.leaves.append(([d.copy_with() for d in divs], list(path)))
            return
        MS = self.Mrun(S)
        MSp1 = min(MS, self.Mw(S + 1))
        if J >= MSp1:                      # rollover (forced)
            self._proc(S + 1, 0, divs, path)
            return
        levels = sorted({self.tilde(d.T) for d in divs})
        occ_above = [m for m in levels if J + 1 <= m <= MS - 1]
        if occ_above:                      # CASE 1 (branch)
            target = occ_above[0]
            J1 = target - J
            cands = [d for d in divs if self.tilde(d.T) == target]
            f = self.def4_min(cands)
            bump = J1 * (self.Mw(S + 1) - J)
            node = dict(S=S, J=J, target=target, fid=f.id, fT=f.T,
                        levels=levels, ndivs=len(divs))
            # 1(1): pull f down to level J (tail:=J), stay at J
            fT2 = self.set_tail(f.T, S, J)
            f2 = f.copy_with(T=fT2, Mexp=f.M + bump, born=("1(1)", S, J))
            divs_U = [d for d in divs if d.id != f.id] + [f2]
            self._proc(S, J, divs_U, path + [dict(node, dec="1(1)")])
            # 1(2): fork a copy of f at level J, advance J, keep f
            childT = self.set_tail(f.T, S, J)
            child = Div(childT, f.M + bump, born=("1(2)", S, J))
            divs_D = list(divs) + [child]
            self._proc(S, J + 1, divs_D, path + [dict(node, dec="1(2)")])
        else:                              # CASE 2 (forced): head = running-min (FIX-A)
            T = [0] * self.L
            for i in range(1, S):
                T[i - 1] = self.Mrun(i + 1)
            T = self.set_tail(tuple(T), S, J)
            Mexp = (MS - J) * (self.Mw(S + 1) - J)
            new = Div(T, Mexp, born=("case2", S, J))
            self._proc(S, J + 1, divs + [new], path + [dict(S=S, J=J, dec="case2")])


def leaf_t0(divs):
    return sorted({d.T for d in divs if min(d.T) == 0})


def analyze(M):
    Div._next = 0
    tr = Tracer(M).run()
    adm = set(nested_profiles(M))
    union = set()
    for divs, path in tr.leaves:
        union |= set(leaf_t0(divs))
    print(f"M={M}  L={len(M)-1}  minAdm={minAdm(M)}  leaves={len(tr.leaves)}")
    print(f"  |Adm|={len(adm)}  |P(M) t0-union|={len(union)}  P==Adm: {union == adm}")
    missing = adm - union
    extra = union - adm
    if missing:
        print(f"  ** MISSING (in Adm, not realized): {sorted(missing)}")
    if extra:
        print(f"  ** EXTRA (realized, not in Adm): {sorted(extra)}")
    return tr, adm, union


if __name__ == "__main__":
    for M in [(2, 2, 2), (3, 3, 4), (2, 2, 2, 2), (2, 2, 3, 2),
              (2, 2, 3, 3, 2), (3, 2, 4, 2)]:
        analyze(M)
        print()
