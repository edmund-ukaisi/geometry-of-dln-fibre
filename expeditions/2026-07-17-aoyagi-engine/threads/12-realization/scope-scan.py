#!/usr/bin/env python3
# provenance: threads/12-realization (pnp-o5). SCOPE of the realization gap: scan many M, find
#   admissible profiles NOT realized as t̃=0 leaf divisors (stranded), and TEST the strict need
#   (minAdm value IN the realized t̃=0 exponent set). Uses the ORIGINAL validated Sim (defs only),
#   runmin/FIX-A. Integer-only, exact.
import itertools
import sys

# ---- load the ORIGINAL validated sim's definitions (strip its top-level driver) ----
SRC = 'expeditions/2026-07-17-aoyagi-engine/threads/08-atlas-probe/battery/nonmono-2232-sim.py'
src = open(SRC).read()
ns = {'__name__': 'orig'}
exec(src[:src.index('ok = True')], ns)
Sim, minAdm, nested_profiles, Mval, in_Adm = (
    ns['Sim'], ns['minAdm'], ns['nested_profiles'], ns['Mval'], ns['in_Adm'])


def Mrun(M, S):
    return min(M[:S])


def realized_t0(M, headreset="runmin"):
    s = Sim(M, headreset=headreset).run()
    divs = set()
    for leaf in s.leaves:
        divs.update(leaf)
    profs = sorted({T for (T, m) in divs if min(T) == 0})
    t0min = min((m for (T, m) in divs if min(T) == 0), default=None)
    return set(profs), t0min, s


def strand_predicate(M, a):
    """Predicted stranded iff SOME coordinate value equals the running-min AT A LAYER WHERE the
    running-min has ALREADY dropped to it, i.e. a^i = M(i+1) and a^i >= M(S) for some later S<=clear
    where the divisor would need to sit at level a^i but a^i > M(S)-1 (unclearable). Precise form:
      a is stranded iff there is an index p (1<=p<=L-1) with a^p > 0 and a^p >= min(M[:q+1]) for the
      FIRST later layer q>p+1 ... -- we compute it operationally below instead."""
    return None  # placeholder; we compute empirically


def scan(widths_pool, Lmax):
    rows = []
    for L in range(2, Lmax + 1):
        for M in itertools.product(widths_pool, repeat=L + 1):
            adm = set(nested_profiles(M))
            P, t0min, _ = realized_t0(M)
            missing = adm - P
            extra = P - adm
            mn = minAdm(M)
            strict_ok = (t0min == mn)                       # minAdm VALUE realized
            # is some MINIMIZER profile realized?
            minimizers = {a for a in adm if Mval(M, a) == mn}
            minimizer_realized = bool(minimizers & P)
            rows.append(dict(M=M, L=L, nAdm=len(adm), nP=len(P),
                             missing=sorted(missing), extra=sorted(extra),
                             strict_ok=strict_ok, min_real=minimizer_realized,
                             minz=sorted(minimizers), minval=mn))
    return rows


if __name__ == "__main__":
    # Scan small widths, up to L=4 (deeper gets expensive but exact).
    pool = [1, 2, 3]
    rows = scan(pool, 4)
    n = len(rows)
    with_missing = [r for r in rows if r["missing"]]
    strict_fail = [r for r in rows if not r["strict_ok"]]
    min_fail = [r for r in rows if not r["min_real"]]
    extra_any = [r for r in rows if r["extra"]]
    print(f"Scanned {n} instances (widths {pool}, 2<=L<=4).")
    print(f"  instances with MISSING profiles (P != Adm): {len(with_missing)}")
    print(f"  instances with EXTRA profiles (P not subset Adm): {len(extra_any)}")
    print(f"  instances where minAdm VALUE NOT realized (K2 strict FAIL): {len(strict_fail)}")
    print(f"  instances where NO minimizer profile realized: {len(min_fail)}")
    print()
    print("First 25 instances with a realization gap (P != Adm):")
    for r in with_missing[:25]:
        env = [Mrun(r['M'], i + 1) for i in range(1, len(r['M']))]
        print(f"  M={r['M']} env={env} minAdm={r['minval']} nAdm={r['nAdm']} nP={r['nP']}"
              f"  missing={r['missing']}  strict_ok={r['strict_ok']}")
    if strict_fail:
        print("\n** STRICT-NEED FAILURES (minAdm value NOT realized) -- would be K2 MAJOR:")
        for r in strict_fail[:20]:
            print(f"   M={r['M']} minAdm={r['minval']} minz={r['minz']} missing={r['missing']}")
    else:
        print("\nNO strict-need failure: minAdm value realized at EVERY scanned instance.")
    if min_fail:
        print("\n** MINIMIZER-PROFILE UNREALIZED (all minimizers stranded):")
        for r in min_fail[:20]:
            print(f"   M={r['M']} minz={r['minz']} P-min={min(Mval(r['M'],a) for a in nested_profiles(r['M']))}")
    if extra_any:
        print("\n** EXTRA profiles (realized t0 NOT in Adm) -- would contradict leaf_mem_Adm:")
        for r in extra_any[:20]:
            print(f"   M={r['M']} extra={r['extra']}")
    sys.exit(0)
