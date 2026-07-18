#!/usr/bin/env python3
# provenance: threads/12-realization (pnp-o5). Guided DFS: find A path realizing target a, print the
#   decision at each case-1 node with rich node-state, to reverse-engineer the steering rule.
import sys
sys.path.insert(0, 'expeditions/2026-07-17-aoyagi-engine/threads/12-realization')
rc = __import__('realize-check')
Engine, Div, leaf_t0, nested_profiles = rc.Engine, rc.Div, rc.leaf_t0, rc.nested_profiles


def find_path(M, a):
    """DFS: return the first decision-list whose leaf carries a (t̃=0). Canonical order: try 1(1)
    before 1(2) (descend-first)."""
    E = Engine(M)
    a = tuple(a)

    def rec(S, J, divs, decs):
        if S == E.L + 1:
            if a in set(leaf_t0(divs)):
                return decs
            return None
        MSp1 = min(E.Mrun(S), E.Mw(S + 1))
        if J >= MSp1:
            return rec(S + 1, 0, divs, decs)
        c1 = E.case1_data(S, J, divs)
        if c1 is None:
            nd, (S2, J2) = E.apply_case2(S, J, divs)
            return rec(S2, J2, nd, decs + [("case2", S, J)])
        target, f = c1
        # try 1(1) then 1(2)
        nd, (S2, J2) = E.apply_case1_11(S, J, divs, f)
        r = rec(S2, J2, nd, decs + [("1(1)", S, J, "tgt", target, "fT", f.T)])
        if r is not None:
            return r
        nd, (S2, J2) = E.apply_case1_12(S, J, divs, f)
        return rec(S2, J2, nd, decs + [("1(2)", S, J, "tgt", target, "fT", f.T)])

    Div._next = 0
    return rec(1, 0, [], [])


if __name__ == "__main__":
    for M in [(2, 2, 2, 2), (2, 2, 3, 2), (3, 2, 4, 2)]:
        print("=" * 72)
        print("M =", M, "  running-min envelope M(i+1):",
              [Engine(M).Mrun(i + 1) for i in range(1, len(M))])
        for a in nested_profiles(M):
            decs = find_path(M, a)
            b = 1 + rc.envelope_prefix_len(M, a)
            clr = 1 + max([i for i in range(1, len(a) + 1) if a[i - 1] > 0], default=0)
            comp = [("case2" if d[0] == "case2" else f"{d[0]}@({d[1]},{d[2]})tgt{d[4]}") for d in decs]
            print(f"  a={a}  b={b} clear={clr}:  {comp}")
        print()
