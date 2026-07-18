#!/usr/bin/env python3
# provenance: threads/12-realization (pnp-o5). EXACT characterization of the realizable t̃=0 profile
#   set P(M): P(M) = { a in Adm(M) : Clearable(a) }, where
#     Clearable(a) := for every layer S (2<=S<=L), a^S < a^{S-1}  =>  a^{S-1} < M(S)  (running min).
#   ("every strict descent of a happens from a level strictly below the running-min at that layer;
#    a divisor sitting at level >= M(S) is unclearable at layer S -- occ_above tops out at M(S)-1.")
#   Also verify: (1) P == Clearable-Adm EXACTLY over a wide scan; (2) the steering rule steer_v2
#   realizes EXACTLY the clearable profiles; (3) every minimizer is clearable (=> minAdm in P).
import itertools
import sys

SRC = 'expeditions/2026-07-17-aoyagi-engine/threads/08-atlas-probe/battery/nonmono-2232-sim.py'
src = open(SRC).read()
ns = {'__name__': 'orig'}
exec(src[:src.index('ok = True')], ns)
Sim, minAdm, nested_profiles, Mval = ns['Sim'], ns['minAdm'], ns['nested_profiles'], ns['Mval']

sys.path.insert(0, 'expeditions/2026-07-17-aoyagi-engine/threads/12-realization')
sv = __import__('steer-v2')


def Mrun(M, S):
    return min(M[:S])


def envelope_prefix_len(M, a):
    k = 0
    for i in range(1, len(a) + 1):
        if a[i - 1] == Mrun(M, i + 1):
            k += 1
        else:
            break
    return k


def clearable(M, a):
    """a in Adm is realizable at t̃=0 iff its ANCHOR (born by case-2 at layer b=b(a)) can descend
    to 0: at every descent layer S in (b, clear], a strict descent a^S<a^{S-1} must start from a
    level BELOW the running-min, a^{S-1} < M(S) (levels >= M(S) are unclearable: occ_above tops at
    M(S)-1). Coords <b are the running-min envelope, born cleared by case-2 -- no descent stranding."""
    L = len(M) - 1
    b = 1 + envelope_prefix_len(M, a)
    clear = 1 + max([i for i in range(1, L + 1) if a[i - 1] > 0], default=0)
    for S in range(b + 1, clear + 1):         # descent layers strictly after birth
        if a[S - 1] < a[S - 2] and a[S - 2] >= Mrun(M, S):
            return False
    return True


def realized_t0(M):
    s = Sim(M, headreset="runmin").run()
    divs = set()
    for leaf in s.leaves:
        divs.update(leaf)
    return {T for (T, m) in divs if min(T) == 0}


def check_instance(M):
    adm = [tuple(a) for a in nested_profiles(M)]
    P = realized_t0(M)
    clr = {a for a in adm if clearable(M, a)}
    char_ok = (P == clr)                       # EXACT characterization
    # steering realizes exactly clearable?
    steered = {a for a in adm if a in set(sv.leaf_t0(sv.steer_v2(M, a)[0]))}
    steer_ok = (steered == clr)
    # every minimizer clearable?
    mn = minAdm(M)
    minz = [a for a in adm if Mval(M, a) == mn]
    minz_clr = all(clearable(M, a) for a in minz)
    return char_ok, steer_ok, minz_clr, P, clr, minz


def scan(pool, Lmax):
    bad_char, bad_steer, bad_minz = [], [], []
    n = 0
    for L in range(2, Lmax + 1):
        for M in itertools.product(pool, repeat=L + 1):
            n += 1
            char_ok, steer_ok, minz_clr, P, clr, minz = check_instance(M)
            if not char_ok:
                bad_char.append((M, sorted(P), sorted(clr)))
            if not steer_ok:
                bad_steer.append((M,))
            if not minz_clr:
                bad_minz.append((M, minz))
    return n, bad_char, bad_steer, bad_minz


if __name__ == "__main__":
    for pool, Lmax, tag in [([1, 2, 3], 4, "widths{1,2,3}, L<=4"),
                            ([1, 2, 3, 4], 3, "widths{1,2,3,4}, L<=3")]:
        n, bad_char, bad_steer, bad_minz = scan(pool, Lmax)
        print(f"=== scan {tag}: {n} instances ===")
        print(f"  P(M) == Clearable-Adm  EXACT at all: {not bad_char}"
              f"   (counterexamples: {len(bad_char)})")
        for M, P, clr in bad_char[:5]:
            print(f"     ** {M}: P={P}  clr={clr}")
        print(f"  steer_v2 realizes EXACTLY clearable at all: {not bad_steer}"
              f"   (counterexamples: {len(bad_steer)})")
        for row in bad_steer[:5]:
            print(f"     ** {row}")
        print(f"  every minimizer is clearable (=> minAdm in P) at all: {not bad_minz}"
              f"   (counterexamples: {len(bad_minz)})")
        for M, minz in bad_minz[:5]:
            print(f"     ** {M} minz={minz}")
        print()
    sys.exit(0)
