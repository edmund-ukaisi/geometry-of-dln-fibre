#!/usr/bin/env python3
# provenance: threads/12-realization (pnp-o5). Deterministic single-path steering rule R(a), v2.
#   RULE (state-free in the decision, depends only on the case-1 node's (S, target level ℓ) and a):
#       at a case-1 node in layer S with target level ℓ:  take 1(1) iff ℓ > a^S, else 1(2).
#   ("descend every divisor sitting ABOVE a's layer-S value a^S; preserve a plateau at level a^S.")
#   case-2 / rollover forced. We RUN it (deterministic) and check the leaf carries a (t̃=0).
import sys
from functools import lru_cache
sys.path.insert(0, 'expeditions/2026-07-17-aoyagi-engine/threads/12-realization')
rc = __import__('realize-check')
Engine, Div, leaf_t0, nested_profiles, minAdm, _Mval = (
    rc.Engine, rc.Div, rc.leaf_t0, rc.nested_profiles, rc.minAdm, rc._Mval)


def steer_v2(M, a, trace=False):
    E = Engine(M)
    a = tuple(a)
    assert len(a) == E.L and a[-1] == 0
    decs = []

    def aS(S):                              # a^S for 1<=S<=L ; a^0 := +inf (never used as bound)
        return a[S - 1]

    def rec(S, J, divs):
        if S == E.L + 1:
            return [d.clone() for d in divs]
        MSp1 = min(E.Mrun(S), E.Mw(S + 1))
        if J >= MSp1:
            return rec(S + 1, 0, divs)
        c1 = E.case1_data(S, J, divs)
        if c1 is None:
            nd, (S2, J2) = E.apply_case2(S, J, divs)
            decs.append(("case2", S, J))
            return rec(S2, J2, nd)
        target, f = c1
        dec = "1(1)" if target > aS(S) else "1(2)"
        decs.append((dec, S, J, "tgt", target, "aS", aS(S)))
        if dec == "1(1)":
            nd, (S2, J2) = E.apply_case1_11(S, J, divs, f)
        else:
            nd, (S2, J2) = E.apply_case1_12(S, J, divs, f)
        return rec(S2, J2, nd)

    Div._next = 5 * 10 ** 6
    leaf = rec(1, 0, [])
    return leaf, decs


def check(M):
    adm = [tuple(x) for x in nested_profiles(M)]
    fails = []
    for a in adm:
        leaf, decs = steer_v2(M, a)
        if a not in set(leaf_t0(leaf)):
            fails.append((a, decs, leaf_t0(leaf)))
    mvals = {a: _Mval(M, a) for a in adm}
    mn = min(mvals.values())
    minz = [a for a in adm if mvals[a] == mn]
    minz_ok = all(a in set(leaf_t0(steer_v2(M, a)[0])) for a in minz)
    print(f"M={M}  L={len(M)-1}  |Adm|={len(adm)}  minAdm={minAdm(M)}  "
          f"R(a) realizes all: {not fails} ({len(adm)-len(fails)}/{len(adm)})  "
          f"minimizers {minz} realized: {minz_ok}")
    for a, decs, got in fails[:8]:
        comp = [("c2" if d[0] == "case2" else f"{d[0]}@({d[1]},{d[2]})t{d[4]}") for d in decs]
        print(f"   ** FAIL a={a}  leaf_t0={got}")
        print(f"        decs={comp}")
    return not fails


if __name__ == "__main__":
    instances = [(2, 2, 2), (3, 3, 4), (2, 2, 2, 2), (2, 2, 3, 2),
                 (2, 2, 3, 3, 2), (3, 2, 4, 2), (3, 3, 4, 2, 3), (2, 3, 2, 4, 2),
                 (4, 4, 5, 3), (2, 2, 2, 2, 2), (3, 3, 3, 3)]
    allok = True
    for M in instances:
        allok &= check(M)
    print("\nSTEER v2:", "PASS" if allok else "FAIL")
    sys.exit(0 if allok else 1)
