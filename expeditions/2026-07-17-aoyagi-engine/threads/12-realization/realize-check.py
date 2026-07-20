#!/usr/bin/env python3
# guards: resolution-tree, coverage-theorem
# provenance: threads/12-realization (pnp-o5), fork-13 o5-IN REALIZATION (⊇ half). FIX-A (runmin).
"""
Realization checker for the o5-∈ ⊇ half.

Two engines share the SAME recursion (FIX-A runmin, Def-4-minimal chooser):
  * enumerate_leaves(M): the full branching tree; P(M) = union of t̃=0 leaf profiles.
  * steer(M, a): a DETERMINISTIC single path driven by the steering rule R(a); returns the leaf.

R(a): to realize a=(a^1,...,a^{L-1},0), we descend a single tracked divisor D:
  - D is born by Case-2 at (b, a^b), b = b(a) = 1 + |maximal prefix of a equal to the running-min
    envelope (M(2),M(3),...)|.  (Layer-1 case-2 births are the diagonals; the b=1 case.)
  - After birth, at each later layer S (b < S <= clear(a)), D is pulled from level a^{S-1} down to
    level a^S; at the clearing layer clear(a)=1+max{i:a^i>0} its tail is written to 0 (frozen).
The decision function at a case-1 node, given D (tracked by identity):
  - if the picked min f is NOT D: take 1(2) (fork+advance) -- clear the lower level, don't touch D.
  - if f IS D and the current level of D > a^S: take 1(1) (pull D down toward a^S), staying at J.
  - if f IS D and D is already at level a^S: take 1(2) (leave D, advance) -- freezes coord S = a^S.
Case-2/rollover nodes are forced.

We do NOT hand-tune: we RUN this rule and check the produced leaf carries a (t̃=0). Also a DFS
fallback searches all paths for a, to (a) confirm reachability independent of R, (b) expose if R
ever fails (a FINDING).
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
    __slots__ = ("T", "M", "id")
    _next = 0

    def __init__(self, T, Mexp):
        self.T = tuple(T)
        self.M = Mexp
        self.id = Div._next
        Div._next += 1

    def clone(self, T=None, Mexp=None):
        return Div(self.T if T is None else T, self.M if Mexp is None else Mexp)


class Engine:
    def __init__(self, M):
        self.M = tuple(M)
        self.L = len(M) - 1

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
            if all(all(x <= y for x, y in zip(c.T, d.T)) for d in cands):
                return c
        return min(cands, key=lambda d: d.T)   # non-chain fallback (should not occur, FIX-A)

    def case1_data(self, S, J, divs):
        """Return (target, f) if a case-1 fires at (S,J), else None (=> case-2)."""
        MS = self.Mrun(S)
        levels = sorted({self.tilde(d.T) for d in divs})
        occ_above = [m for m in levels if J + 1 <= m <= MS - 1]
        if not occ_above:
            return None
        target = occ_above[0]
        cands = [d for d in divs if self.tilde(d.T) == target]
        return target, self.def4_min(cands)

    def apply_case1_11(self, S, J, divs, f):
        bump = (self.case1_target(S, J, divs) - J) * (self.Mw(S + 1) - J)
        fT2 = self.set_tail(f.T, S, J)
        f2 = f.clone(T=fT2, Mexp=f.M + bump)
        f2.id = f.id                                  # 1(1) MUTATES: keep identity
        return [d for d in divs if d.id != f.id] + [f2], (S, J)

    def apply_case1_12(self, S, J, divs, f):
        bump = (self.case1_target(S, J, divs) - J) * (self.Mw(S + 1) - J)
        child = Div(self.set_tail(f.T, S, J), f.M + bump)
        return list(divs) + [child], (S, J + 1)       # 1(2): new identity, advance J

    def case1_target(self, S, J, divs):
        MS = self.Mrun(S)
        levels = sorted({self.tilde(d.T) for d in divs})
        return [m for m in levels if J + 1 <= m <= MS - 1][0]

    def apply_case2(self, S, J, divs):
        T = [0] * self.L
        for i in range(1, S):
            T[i - 1] = self.Mrun(i + 1)
        T = self.set_tail(tuple(T), S, J)
        Mexp = (self.Mrun(S) - J) * (self.Mw(S + 1) - J)
        return list(divs) + [Div(T, Mexp)], (S, J + 1)


def leaf_t0(divs):
    return sorted({d.T for d in divs if min(d.T) == 0})


# ---------- full-tree enumeration (P(M)) ----------
def enumerate_leaves(M):
    E = Engine(M)
    leaves = []

    def rec(S, J, divs):
        if S == E.L + 1:
            leaves.append([d.clone() for d in divs])
            return
        MSp1 = min(E.Mrun(S), E.Mw(S + 1))
        if J >= MSp1:
            rec(S + 1, 0, divs)
            return
        c1 = E.case1_data(S, J, divs)
        if c1 is None:
            nd, (S2, J2) = E.apply_case2(S, J, divs)
            rec(S2, J2, nd)
        else:
            _, f = c1
            nd, (S2, J2) = E.apply_case1_11(S, J, divs, f)
            rec(S2, J2, nd)
            nd, (S2, J2) = E.apply_case1_12(S, J, divs, f)
            rec(S2, J2, nd)
    Div._next = 0
    rec(1, 0, [])
    return leaves


# ---------- steering rule R(a): deterministic single path ----------
def envelope_prefix_len(M, a):
    """|maximal prefix i>=1 with a^i == M(i+1) (running-min)|."""
    E = Engine(M)
    k = 0
    for i in range(1, len(a) + 1):
        if a[i - 1] == E.Mrun(i + 1):
            k += 1
        else:
            break
    return k


def steer(M, a):
    E = Engine(M)
    L = E.L
    assert len(a) == L and a[-1] == 0
    clear = 1 + max([i for i in range(1, L + 1) if a[i - 1] > 0], default=0)  # 1..L
    b = 1 + envelope_prefix_len(M, a)                                         # birth layer
    b = min(b, clear)                                                         # don't outrun clearing
    tracked = {"id": None}     # identity of D once born
    decisions = []

    def target_level(S):
        # the level D should occupy at the END of layer S (its coord-S freeze value)
        if S < b:
            return E.Mrun(S + 1)     # envelope (a^S == M(S+1) for S<b by construction)
        return a[S - 1]              # a^S for S>=b

    def rec(S, J, divs):
        if S == L + 1:
            return [d.clone() for d in divs]
        MSp1 = min(E.Mrun(S), E.Mw(S + 1))
        if J >= MSp1:
            return rec(S + 1, 0, divs)
        c1 = E.case1_data(S, J, divs)
        if c1 is None:               # CASE 2 (forced)
            nd, (S2, J2) = E.apply_case2(S, J, divs)
            # is THIS the birth of D? case-2 at (b, a^b) with the tracked slot empty
            if tracked["id"] is None and S == b and J == a[b - 1]:
                tracked["id"] = nd[-1].id
            decisions.append(("case2", S, J))
            return rec(S2, J2, nd)
        target, f = c1
        f_is_D = (tracked["id"] is not None and f.id == tracked["id"])
        want = target_level(S)
        if f_is_D and E.tilde(f.T) > want:
            dec = "1(1)"             # pull D down toward its layer-S target
        elif f_is_D:                 # D already at/below target -> leave it, advance
            dec = "1(2)"
        else:
            dec = "1(2)"             # not D: fork the lower level, advance, don't disturb D
        decisions.append((dec, S, J, ("D" if f_is_D else "other"), "tgt", target, "want", want))
        if dec == "1(1)":
            nd, (S2, J2) = E.apply_case1_11(S, J, divs, f)
        else:
            nd, (S2, J2) = E.apply_case1_12(S, J, divs, f)
        return rec(S2, J2, nd)

    Div._next = 10 ** 6            # disjoint id space from enumerate
    leaf = rec(1, 0, [])
    return leaf, decisions, dict(clear=clear, b=b)


# ---------- DFS: does SOME path realize a? (independent of R) ----------
def dfs_realizes(M, a):
    for divs in enumerate_leaves(M):
        if tuple(a) in set(leaf_t0(divs)):
            return True
    return False


def check(M, verbose=False):
    adm = nested_profiles(M)
    P = set()
    for divs in enumerate_leaves(M):
        P |= set(leaf_t0(divs))
    ok = True
    r_fail, dfs_fail = [], []
    for a in adm:
        leaf, decs, info = steer(M, a)
        realized = tuple(a) in set(leaf_t0(leaf))
        if not realized:
            r_fail.append((a, info, decs))
        if not dfs_realizes(M, a):
            dfs_fail.append(a)
    print(f"M={M}  L={len(M)-1}  minAdm={minAdm(M)}  |Adm|={len(adm)}  P==Adm:{P==set(map(tuple,adm))}")
    print(f"   steering R(a) realizes ALL a in Adm: {not r_fail}"
          f"   ({len(adm)-len(r_fail)}/{len(adm)})")
    if r_fail:
        ok = False
        for a, info, decs in r_fail[:6]:
            print(f"   ** R FAILED a={a} info={info}")
            leaf, _, _ = steer(M, a)
            print(f"        leaf t0={leaf_t0(leaf)}")
    if dfs_fail:
        ok = False
        print(f"   ** DFS-UNREACHABLE (kill K1): {dfs_fail}")
    # minimizer specifically (kill K2)
    mvals = {tuple(a): _Mval(M, a) for a in adm}
    mn = min(mvals.values())
    minimizers = [a for a in adm if mvals[a] == mn]
    for a in minimizers:
        leaf, _, _ = steer(M, a)
        if tuple(a) not in set(leaf_t0(leaf)):
            ok = False
            print(f"   ** K2 minAdm minimizer {a} NOT realized by R!")
    print(f"   minAdm minimizers {minimizers} all realized: "
          f"{all(tuple(a) in set(leaf_t0(steer(M,a)[0])) for a in minimizers)}")
    return ok


def _Mval(M, t):
    L = len(M) - 1
    v = (M[0] - t[0]) * (M[1] - t[0])
    for j in range(2, L + 1):
        v += (t[j - 2] - t[j - 1]) * (M[j] - t[j - 1])
    return v


if __name__ == "__main__":
    instances = [(2, 2, 2), (3, 3, 4), (2, 2, 2, 2), (2, 2, 3, 2),
                 (2, 2, 3, 3, 2), (3, 2, 4, 2),
                 # fresh non-monotone L>=4:
                 (3, 3, 4, 2, 3), (2, 3, 2, 4, 2)]
    allok = True
    for M in instances:
        allok &= check(M)
        print()
    print("REALIZATION CHECK:", "PASS" if allok else "FAIL")
    sys.exit(0 if allok else 1)
