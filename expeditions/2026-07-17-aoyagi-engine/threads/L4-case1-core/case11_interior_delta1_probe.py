#!/usr/bin/env python3
# guards: the wall `case1_preserves_stepInv` case1(1)-boost δ=1 branch (interior, S<L, J=0);
#         where it is first EXERCISED (test-bed selection for the boost-readiness AUDIT).
"""PROBE/BATTERY: locate the INTERIOR case1(1)-boost edges at δ=1 (J=0, S<L).

The wall `case1_preserves_stepInv` guards `nextState.layer+1 < N` (interior). For a case1(1)
boost, `stepCase11` KEEPS (layer, cleared), so the interior guard is `S+1 < N` ⟺ `S < L`, and
δ=1 ⟺ `J = 0`. So the branch fires at a case1(1) chart executed at (S, 0) with S < L — a divisor
born in an EARLIER layer, boosted at the START of a later (non-last) layer.

KEY CONSEQUENCE (asserted below): the standing (3,3,4) matrix trace does NOT exercise the wall's
case11-δ=1 branch — (3,3,4)'s only boost fires at (S=2=L, J=0), a TERMINAL edge (owned by
`lastLayer_clear_preserves`/`terminal_edge_stepInv`, not the interior wall). The MINIMAL instance
that exercises the interior branch is (2,2,2,2) (L=3), boost at (S=2,J=0) reusing a layer-1 divisor.
So a boost-readiness residual battery must be built on (2,2,2,2)/(3,3,2,2), NOT (3,3,4).

Mechanism context (Codex xhigh, 2026-07-22, `codex/case11-delta1-mechanism-answer.md`): at such an
edge the parent residual is `Deg1SupportedOn` the BOOST CENTER `{pivot} ∪ partial-block` even though
its geometric support is the larger full block — the untouched terms carry `u_pivot` in the
non-dominant b-chain coefficient `b_i/b_1`. This probe does NOT verify that residual claim (that
needs a matrix-level trace); it fixes the test-bed and the cross-layer structure the claim rests on.

A1: (3,3,4) has NO interior case11-δ=1 hit (its boost is terminal).
A2: (2,2,2,2) HAS an interior case11-δ=1 hit (the minimal test bed).
A3: every interior case11-δ=1 hit reuses a divisor born at a STRICTLY EARLIER layer (birthS < S) —
    so the pivot is cross-layer (∉ the layer-S support block), matching `canonPivotOf case11`.

Exit 0 = all assertions hold; exit 1 = a violation (printed). Provenance: seat-L4, case11-δ=1
mechanism round. Read-only enumeration (mirrors the certified `clause3_corner_check.py` recursion).
"""
import copy, sys

def run(M):
    """Return list of (S, J, birthLayer) for interior case1(1) charts at δ=1 (J=0, S<L)."""
    L = len(M) - 1
    hits = []
    def Mrun(S): return min(M[:S])
    def tilde(T): return min(T)

    def step(S, J, divs):
        MS = Mrun(S); MS1 = M[S] if S <= L else None
        capJ = min(MS, MS1)
        if J == capJ:
            if S == L: return
            step(S + 1, 0, divs); return
        jumps = sorted({tilde(d['T']) for d in divs if J + 1 <= tilde(d['T']) <= MS - 1})
        if not jumps:                                   # CASE 2: birth at (S,J)
            Tn = [(M[k] if (k + 1) < S else J) for k in range(1, L + 1)]
            nd = divs + [{'T': Tn, 'M': (MS - J) * (MS1 - J), 'birthS': S, 'birthJ': J}]
            step(S, J + 1, nd); return
        else:
            jj = jumps[0]; J1 = jj - J
            cand = [d for d in divs if tilde(d['T']) == jj]
            ustar = min(cand, key=lambda d: tuple(d['T']))
            if J == 0 and S < L:                        # INTERIOR case1(1) at δ=1
                hits.append((S, J, ustar.get('birthS', -1)))
            d11 = copy.deepcopy(divs)
            u1 = next(d for d in d11 if d['T'] == ustar['T'] and d['M'] == ustar['M'])
            for k in range(S, L + 1): u1['T'][k - 1] = J
            u1['M'] = ustar['M'] + J1 * (MS1 - J)
            step(S, J, d11)
            d12 = copy.deepcopy(divs)
            Tn = [(ustar['T'][k - 1] if k < S else J) for k in range(1, L + 1)]
            d12.append({'T': Tn, 'M': ustar['M'] + J1 * (MS1 - J), 'birthS': S, 'birthJ': J})
            step(S, J + 1, d12); return

    step(1, 0, [])
    return hits

ok = True
viol = []

CANDIDATES = [(3, 3, 4), (3, 3, 2, 2), (2, 2, 2, 2), (2, 2, 2, 2, 2), (4, 4, 4, 4),
              (3, 3, 3, 3), (4, 4, 2, 2), (3, 3, 4, 4), (2, 2, 3, 3), (4, 4, 4, 2)]
print("interior case1(1) δ=1 (J=0, S<L) hits per instance  [(S, J, birthLayer)]:")
allhits = {}
for M in CANDIDATES:
    hits = run(M)
    allhits[M] = hits
    print(f"  M={M}: {hits}")

# A1: (3,3,4) has NO interior case11-δ=1 hit.
if allhits[(3, 3, 4)]:
    ok = False; viol.append("A1: (3,3,4) unexpectedly has an interior case11-δ=1 hit")
# A2: (2,2,2,2) HAS one.
if not allhits[(2, 2, 2, 2)]:
    ok = False; viol.append("A2: (2,2,2,2) has NO interior case11-δ=1 hit (expected the minimal test bed)")
# A3: every interior hit reuses a divisor born at a strictly earlier layer.
for M, hits in allhits.items():
    for (S, J, bS) in hits:
        if not (bS < S):
            ok = False; viol.append(f"A3: M={M} hit (S={S},J={J}) reuses birthLayer={bS} not < S")

print(f"\n[A1] (3,3,4) interior case11-δ1 absent (boost is terminal): {not allhits[(3,3,4)]}")
print(f"[A2] (2,2,2,2) is the minimal interior case11-δ1 test bed: {bool(allhits[(2,2,2,2)])}")
print(f"[A3] every interior case11-δ1 reuses a strictly-earlier-layer divisor (cross-layer pivot): "
      f"{all(bS < S for h in allhits.values() for (S, J, bS) in h)}")

if not ok:
    print("\nVIOLATIONS:")
    for v in viol: print("  ", v)
    sys.exit(1)
print("\nPROBE PASS: interior case11-δ1 test bed = (2,2,2,2)/(3,3,2,2); (3,3,4) does NOT exercise it. EXIT 0")
sys.exit(0)
