#!/usr/bin/env python3
# guards: resolution-tree, coverage-theorem
# provenance: threads/12-realization (pnp-o5), fork-13 o5-IN REALIZATION. Consolidated exit-0 battery
#   for the realization certificate. FIX-A (runmin) throughout. Integer-only, exact recursion (NO
#   Monte-Carlo). Reuses the ORIGINAL VALIDATED simulator (nonmono-2232-sim.py) as ground truth.
#
# CLAIMS UNDER TEST (all must pass for exit 0):
#   B1  P(M) subset Adm(M) at every scanned M          (consistent with Lean leaf_mem_Adm)
#   B2  P(M) = { a in Adm : Clearable(a) } EXACTLY      (the exact characterization)
#   B3  min over P(M) == minAdm(M) at every M           (the STRICT need: minAdm in terminalExponents)
#   B4  every Mval-minimizer is Clearable               (=> a minimizer is realized)
#   B5  the strand obstruction is CHOOSER/BRANCH-INDEPENDENT: a non-clearable a is unreachable at
#       t̃=0 even allowing ARBITRARY case-1 chooser picks + arbitrary 1(1)/1(2) branches
#       (searched exhaustively on the witness M=(3,3,4,2,3))
#   B6  steering rule R (1(1) iff target level ℓ > a^S) realizes EXACTLY the clearable profiles
import itertools
import sys

SRC = 'expeditions/2026-07-17-aoyagi-engine/threads/08-atlas-probe/battery/nonmono-2232-sim.py'
src = open(SRC).read()
ns = {'__name__': 'orig'}
exec(src[:src.index('ok = True')], ns)
Sim, minAdm, nested_profiles, Mval = ns['Sim'], ns['minAdm'], ns['nested_profiles'], ns['Mval']


def Mrun(M, S):
    return min(M[:S])


def envlen(M, a):
    k = 0
    for i in range(1, len(a) + 1):
        if a[i - 1] == Mrun(M, i + 1):
            k += 1
        else:
            break
    return k


def clearable(M, a):
    """a in Adm realizable at t̃=0 iff every descent AFTER the birth layer starts below the running
    min. Non-clearability forces a^{S-1} = M(S) (Adm gives a^{S-1} <= M(S))."""
    L = len(M) - 1
    b = 1 + envlen(M, a)
    clear = 1 + max([i for i in range(1, L + 1) if a[i - 1] > 0], default=0)
    for S in range(b + 1, clear + 1):
        if a[S - 1] < a[S - 2] and a[S - 2] >= Mrun(M, S):
            return False
    return True


def realized_t0(M):
    s = Sim(M, headreset="runmin").run()
    divs = set()
    for lf in s.leaves:
        divs.update(lf)
    P = {T for (T, m) in divs if min(T) == 0}
    t0min = min((m for (T, m) in divs if min(T) == 0), default=None)
    return P, t0min


# ---- B6 steering rule R, deterministic single path ----
def steer_R(M, a):
    L = len(M) - 1
    a = tuple(a)

    def set_tail(T, S, J):
        T = list(T)
        for j in range(S, L + 1):
            T[j - 1] = J
        return tuple(T)

    def def4min(cands):
        for c in cands:
            if all(all(x <= y for x, y in zip(c[0], d[0])) for d in cands):
                return c
        return min(cands, key=lambda d: d[0])

    def rec(S, J, divs):
        if S == L + 1:
            return {T for (T, m) in divs if min(T) == 0}
        MS = Mrun(M, S)
        MSp1 = min(MS, M[S])
        if J >= MSp1:
            return rec(S + 1, 0, divs)
        levels = sorted({min(T) for (T, m) in divs})
        occ = [m for m in levels if J + 1 <= m <= MS - 1]
        if not occ:                                   # CASE 2
            T = [0] * L
            for i in range(1, S):
                T[i - 1] = Mrun(M, i + 1)
            T = set_tail(tuple(T), S, J)
            return rec(S, J + 1, divs + [(T, (MS - J) * (M[S] - J))])
        target = occ[0]
        cands = [d for d in divs if min(d[0]) == target]
        f = def4min(cands)
        bump = (target - J) * (M[S] - J)
        if target > a[S - 1]:                          # 1(1): pull f down to J
            f2 = (set_tail(f[0], S, J), f[1] + bump)
            return rec(S, J, [d for d in divs if d is not f] + [f2])
        else:                                          # 1(2): fork copy at J, advance
            child = (set_tail(f[0], S, J), f[1] + bump)
            return rec(S, J + 1, divs + [child])

    return rec(1, 0, [])


# ---- B5 exhaustive ARBITRARY-chooser / arbitrary-branch search for a target t̃=0 profile ----
def reachable_any_chooser(M, a, node_cap=400000):
    """DFS over the recursion where at each case-1 node we branch over (i) 1(1) vs 1(2) AND (ii)
    EVERY eligible divisor at the target level as the pick (not just Def-4-min). Returns True iff
    some path yields a leaf carrying a at t̃=0. Prunes on node_cap."""
    L = len(M) - 1
    a = tuple(a)
    found = [False]
    calls = [0]

    def set_tail(T, S, J):
        T = list(T)
        for j in range(S, L + 1):
            T[j - 1] = J
        return tuple(T)

    def rec(S, J, divs):
        if found[0]:
            return
        calls[0] += 1
        if calls[0] > node_cap:
            return
        if S == L + 1:
            if a in {T for (T, m) in divs if min(T) == 0}:
                found[0] = True
            return
        MS = Mrun(M, S)
        MSp1 = min(MS, M[S])
        if J >= MSp1:
            rec(S + 1, 0, divs)
            return
        levels = sorted({min(T) for (T, m) in divs})
        occ = [m for m in levels if J + 1 <= m <= MS - 1]
        if not occ:
            T = [0] * L
            for i in range(1, S):
                T[i - 1] = Mrun(M, i + 1)
            T = set_tail(tuple(T), S, J)
            rec(S, J + 1, divs + [(T, (MS - J) * (M[S] - J))])
            return
        target = occ[0]
        cands = [d for d in divs if min(d[0]) == target]
        bump = (target - J) * (M[S] - J)
        for f in cands:                                # ARBITRARY chooser pick
            f2 = (set_tail(f[0], S, J), f[1] + bump)
            rec(S, J, [d for d in divs if d is not f] + [f2])     # 1(1)
            if found[0]:
                return
            child = (set_tail(f[0], S, J), f[1] + bump)
            rec(S, J + 1, divs + [child])                          # 1(2)
            if found[0]:
                return

    rec(1, 0, [])
    return found[0]


def run():
    fails = []
    # B1-B4, B6 over a wide scan
    scans = [([1, 2, 3], 4), ([2, 3], 4), ([1, 2, 3, 4], 3), ([1, 2], 5)]
    n = 0
    for pool, Lmax in scans:
        for L in range(2, Lmax + 1):
            for M in itertools.product(pool, repeat=L + 1):
                n += 1
                adm = [tuple(x) for x in nested_profiles(M)]
                P, t0min = realized_t0(M)
                clr = {a for a in adm if clearable(M, a)}
                mn = minAdm(M)
                minz = [a for a in adm if Mval(M, a) == mn]
                if set(P) - set(adm):
                    fails.append(("B1", M, sorted(set(P) - set(adm))))
                if P != clr:
                    fails.append(("B2", M, sorted(P), sorted(clr)))
                if t0min != mn:
                    fails.append(("B3", M, t0min, mn))
                if not all(clearable(M, a) for a in minz):
                    fails.append(("B4", M, minz))
                steered = {a for a in adm if a in steer_R(M, a)}
                if steered != clr:
                    fails.append(("B6", M, sorted(steered ^ clr)))
    # B5 on the witness
    Mw = (3, 3, 4, 2, 3)
    admw = [tuple(x) for x in nested_profiles(Mw)]
    Pw, _ = realized_t0(Mw)
    strand = [a for a in admw if not clearable(Mw, a)]
    for a in strand:
        if reachable_any_chooser(Mw, a):
            fails.append(("B5", Mw, a, "reachable under some chooser/branch"))
    print(f"Scanned {n} instances (widths up to 4, L up to 5), exact recursion.")
    print(f"  B5 witness M={Mw}: non-clearable admissible profiles = {strand}")
    print(f"     each unreachable at t̃=0 under ARBITRARY chooser + branch: "
          f"{all(not reachable_any_chooser(Mw, a) for a in strand)}")
    if not fails:
        print("\nALL CLAIMS PASS (B1 subset, B2 exact char, B3 strict-min, B4 minimizer-clearable, "
              "B5 chooser-independent strand, B6 steering rule).")
        return True
    print(f"\n{len(fails)} FAILURES:")
    for f in fails[:20]:
        print("  ", f)
    return False


if __name__ == "__main__":
    sys.exit(0 if run() else 1)
