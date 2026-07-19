#!/usr/bin/env python3
# guards: resolution-tree, coverage-theorem
# provenance: threads/18-fold-regroup (pnp-fold). THE STRANDED-DIVISOR DICHOTOMY.
#
# leafOfState filters the FULL ledger to t̃=0 analytic divisors ((t0Indices s).length); the geometric
# fold produces one factor per FULL divisor s.numDiv. The headline geoAtlas_fold_det reads the ANALYTIC
# ledger. So the fold-Jacobian = headline iff every stranded (t̃>0) divisor at a reachable terminal
# contributes a TRIVIAL factor |z|^{divExp-1} = 1, i.e. divExp = 1 (WEAK), or there are none (STRONG).
# This hunts the actual conOracle recursion (FIX-A runMinWidth head-reset = the Lean) exhaustively over
# small M for the FALSE case: a reachable terminal carrying a stranded divisor with divExp > 1.
#
# The recursion below is the FIX-A (runmin) branch of the page-faithful simulator in
# threads/08-atlas-probe/battery/nonmono-2232-sim.py (validated there against the known t̃=0 atlases at
# (2,2,2),(3,3,4),(2,2,2,2)); embedded self-contained (the source runs top-level code + sys.exit on
# import). Each divisor is (T-profile tuple, divExp); t̃ = min(T); a leaf is S = L+1 (= Lean layer=L).
import itertools

def Mrun(M, S):  return min(M[:S])
def Mw(M, i):    return M[i-1]
def tilde(T):    return min(T)

def set_tail(T, S, L, J):
    T = list(T)
    for j in range(S, L+1):        # components S..L (1-indexed)
        T[j-1] = J
    return tuple(T)

def def4_min(cands):
    """componentwise-<= least (Def-4). Reachable states are a chain (SameLevelChainInv); fall back lex."""
    for c in cands:
        if all(all(a <= b for a, b in zip(c[0], d[0])) for d in cands):
            return c
    return min(cands, key=lambda d: d[0])

def leaves_of(M):
    """All terminal leaves; each leaf = list of (profile, divExp) for the FULL ledger."""
    L = len(M) - 1
    out = []
    def proc(S, J, divs):
        if S == L + 1:
            out.append(list(divs)); return
        MS = Mrun(M, S); MSp1 = min(MS, Mw(M, S+1))
        if J >= MSp1:
            proc(S+1, 0, divs); return
        levels = sorted({tilde(d[0]) for d in divs})
        occ_above = [m for m in levels if J+1 <= m <= MS-1]
        if occ_above:                                   # CASE 1
            target = occ_above[0]; J1 = target - J
            cands = [d for d in divs if tilde(d[0]) == target]
            f = def4_min(cands)
            bump = J1 * (Mw(M, S+1) - J)
            fT2 = set_tail(f[0], S, L, J)
            proc(S, J,   [d for d in divs if d is not f] + [(fT2, f[1] + bump)])   # 1(1)
            childT = set_tail(f[0], S, L, J)
            proc(S, J+1, list(divs) + [(childT, f[1] + bump)])                     # 1(2)
        else:                                           # CASE 2 (FIX-A runmin head-reset)
            T = [0]*L
            for i in range(1, S):
                T[i-1] = Mrun(M, i+1)                    # FIX-A: running-min M(i+1)
            T = set_tail(tuple(T), S, L, J)
            Mexp = (MS - J) * (Mw(M, S+1) - J)
            proc(S, J+1, list(divs) + [(T, Mexp)])
    proc(1, 0, [])
    return out

def analyze(M):
    strong = True; weak = True; false_w = []
    for leaf in leaves_of(M):
        for (T, E) in leaf:
            if tilde(T) > 0:
                strong = False
                if E != 1:
                    weak = False; false_w.append((T, E, tilde(T)))
    return strong, weak, false_w

def sweep(Ms, label):
    ns = nw = nf = 0; fset = []
    for M in Ms:
        strong, weak, fw = analyze(M)
        if fw:   nf += 1; fset.append((M, fw))
        elif not strong: nw += 1
        else:    ns += 1
    print(f"== {label} ({len(Ms)} families) ==")
    print(f"   STRONG (all leaf divisors t̃=0): {ns}")
    print(f"   WEAK-not-strong (stranded present, all divExp=1): {nw}")
    print(f"   FALSE (stranded divExp>1): {nf}")
    for (M, fw) in fset[:15]:
        for (T, E, t) in fw[:3]:
            print(f"     FALSE M={M}: profile {T}  divExp={E}  t̃={t}")
    return ns, nw, nf

if __name__ == "__main__":
    fams = {}
    for L in (1,2,3):
        fams[f"L={L}, M∈[1..3]^{L+1}"] = list(itertools.product(range(1,4), repeat=L+1))
    fams["L=4, M∈[1..3]^5"] = list(itertools.product(range(1,4), repeat=5))
    fams["L=2, M∈[1..4]^3"] = list(itertools.product(range(1,5), repeat=3))
    fams["L=3, M∈[1..4]^4"] = list(itertools.product(range(1,5), repeat=4))
    tot_false = 0; any_weak = False
    for label, Ms in fams.items():
        ns, nw, nf = sweep(Ms, label); tot_false += nf; any_weak = any_weak or nw>0; print()
    print("="*66)
    print(f"OVERALL: FALSE witnesses = {tot_false} ; stranded-with-divExp=1 seen = {any_weak}")
    if tot_false == 0 and not any_weak:
        print("VERDICT: STRONG holds on all swept reachable terminals (no stranding at all).")
    elif tot_false == 0:
        print("VERDICT: WEAK holds (stranding occurs; every stranded divisor has divExp=1).")
    else:
        print("VERDICT: FALSE (a reachable terminal carries a stranded divExp>1 divisor).")
    import sys; sys.exit(0)
