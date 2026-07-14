# Exact decide-check of hole (d)'s cover (LEMMA C) against the CURRENT Lean defs.
# Frame rank m = min(M1, Mlast) - j (Ky-Fan floor on the FULL product Z_full = A0.Z_deep),
# NOT M2 - j. All subtractions are Lean nat-truncated: sub(x,y)=max(0,x-y).
from functools import lru_cache
from itertools import product

def sub(x, y):            # Lean Nat subtraction (truncated)
    return x - y if x > y else 0

@lru_cache(maxsize=None)
def minAdm(M):            # matches minAdmRec / minAdm (RouteMLayerSplit)
    M = tuple(M)
    if len(M) == 1: return 0
    if len(M) == 2: return M[0] * M[1]
    return min((M[0]-t)*(M[1]-t) + minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))

def redChain(u, M):       # = (u, M2, M3, ..., Mlast)
    return (u,) + tuple(M[2:])

def bindingCut(M):        # Nat.find (exists_binding_cut): LEAST achiever of the peel-fold
    best = minAdm(M)
    for u in range(min(M[0], M[1]) + 1):
        if (M[0]-u)*(M[1]-u) + minAdm(redChain(u, M)) == best:
            return u
    raise RuntimeError("no binding cut")

def tailMinWidth(M):      # inf over i in Fin(L+2) of M(i.succ) = min(M1, M2, ..., Mlast)
    return min(M[1:])

def deepTailMin(M):       # brief's "deepTailMin" = min of the DEEP tail (M2..Mlast)
    return min(M[2:])

def scan(arity_ranges, gate="hpiv"):
    """gate: which good-case definition to use.
       'hpiv'      -> chain good iff hpiv holds at every relevant shell (the ACTUAL Lean hyp)
       'deeptail'  -> chain good iff deepTailMin(M) <= M1 (the brief's shorthand)
    Returns list of witness shells: good chain + non-empty shell (hrange holds) where hcvg FAILS."""
    witnesses = []
    stats = dict(chains=0, good=0, nonempty_shells=0, hcvg_fail_nonempty=0)
    seen = set()
    for rng, length in arity_ranges:
        for M in product(rng, repeat=length):
            if M in seen: continue
            seen.add(M)
            stats['chains'] += 1
            M0, M1, M2, Mlast = M[0], M[1], M[2], M[-1]
            tstar = bindingCut(M)
            r = min(sub(M0, tstar), sub(M1, tstar))
            Lam = min(M1, Mlast)
            # per-shell data
            shells = []
            for j in range(0, r + 1):
                u = tstar + j
                m = sub(Lam, j)                     # frame rank
                hrange = (m <= M2)                  # non-vacuity
                a, b = sub(M0, u), sub(M1, u)
                hcvg = (a + b <= m)                 # convergence
                hpiv = (minAdm(redChain(u, M)) <= u * tailMinWidth(M))
                shells.append(dict(j=j, u=u, m=m, a=a, b=b,
                                   hrange=hrange, hcvg=hcvg, hpiv=hpiv))
            # good-case gate
            if gate == "hpiv":
                # non-waist per the ACTUAL hpiv hyp: hpiv holds at every non-empty shell AND at the cut
                good = all(s['hpiv'] for s in shells if s['hrange']) and tstar >= 1
            else:  # deeptail
                good = (deepTailMin(M) <= M1) and tstar >= 1
            if not good:
                continue
            stats['good'] += 1
            for s in shells:
                if s['hrange']:
                    stats['nonempty_shells'] += 1
                    if not s['hcvg']:
                        stats['hcvg_fail_nonempty'] += 1
                        witnesses.append((M, tstar, s))
    return witnesses, stats

# arity 3 (widths 1..6), arity 4 (widths 1..6), arity 5 (widths 1..5) -- keep runtime bounded
RANGES = [(range(1,7),3), (range(1,7),4), (range(1,6),5)]

for gate in ("hpiv", "deeptail"):
    w, st = scan(RANGES, gate=gate)
    print(f"===== GATE = {gate} =====")
    print(f"  chains scanned: {st['chains']}   good chains: {st['good']}")
    print(f"  non-empty shells in good chains: {st['nonempty_shells']}")
    print(f"  non-empty shells with hcvg FAIL: {st['hcvg_fail_nonempty']}")
    if w:
        print(f"  FIRST 12 WITNESSES (good chain, t*, shell where hcvg fails):")
        for M, tstar, s in w[:12]:
            print(f"    M={M}  t*={tstar}  j={s['j']} u={s['u']}  a={s['a']} b={s['b']} m={s['m']}"
                  f"  a+b={s['a']+s['b']}  hrange={s['hrange']} hcvg={s['hcvg']} hpiv={s['hpiv']}")
    print()
