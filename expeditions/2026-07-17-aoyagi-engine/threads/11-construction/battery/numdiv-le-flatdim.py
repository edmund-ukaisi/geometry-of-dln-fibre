#!/usr/bin/env python3
# guards: resolution-tree, coverage-theorem
# provenance: threads/11-construction (architect-t05), sub-gap-1. BATTERY-FIRST per RULINGS-t04 s3:
#   verify  numDiv <= flatDim  on the sim instances BEFORE grinding the Lean reachability invariant.
#   A failure ANYWHERE = a FINDING (surface, do not grind). Reuses the ORIGINAL VALIDATED simulator
#   (nonmono-2232-sim.py, runmin/FIX-A = what the oracle transcribes). Integer-only, exact recursion.
#
# QUANTITIES:
#   flatDim(M) = sum_{s=0}^{L-1} M[s]*M[s+1]         (Lean: Fintype.card (FlatIdx M) = DLN param count)
#   leaf t0-numDiv = # divisors (T,m) at a leaf with tilde_t = min(T) = 0   (= leafOfState.numDiv)
#   state numDiv   = # ALL divisors carried at a state (full ledger; the additive invariant candidate)
#
# CLAIMS UNDER TEST (all must hold for exit 0):
#   A  every LEAF has t0-numDiv <= flatDim            (the exact clause leafOfState.divCoord needs)
#   B  every STATE has full numDiv <= flatDim         (the cleaner additive invariant, if it holds)
import sys

SRC = 'expeditions/2026-07-17-aoyagi-engine/threads/08-atlas-probe/battery/nonmono-2232-sim.py'
src = open(SRC).read()
ns = {'__name__': 'orig'}
exec(src[:src.index('ok = True')], ns)
Sim = ns['Sim']


class TrackSim(Sim):
    """Sim that records, over EVERY reachable state, the full divisor count; and per leaf the
    t0 (tilde=0) divisor count. runmin head-reset (FIX-A) = the oracle's transcription."""
    def __init__(self, M):
        super().__init__(M, headreset="runmin")
        self.max_state_numdiv = 0
        self.leaf_t0_counts = []

    def _proc(self, S, J, divs):
        # record full divisor count at THIS state (mirror of ConState.numDiv)
        if len(divs) > self.max_state_numdiv:
            self.max_state_numdiv = len(divs)
        if S == self.L + 1:
            t0 = sum(1 for (T, m) in divs if min(T) == 0)
            self.leaf_t0_counts.append(t0)
        super()._proc(S, J, divs)


def flatdim(M):
    return sum(M[i] * M[i + 1] for i in range(len(M) - 1))


# Kill-set: BOTH known failure mechanisms + corner (elder-gate7 adequacy), + a width sweep.
KILLSET = [
    (2, 2, 2), (3, 3, 4), (2, 2, 2, 2), (2, 2, 3, 2),        # baselines / monotone
    (2, 2, 3, 3, 2), (3, 2, 4, 2),                            # L>=4 non-monotone depth (mech ii)
    (3, 3, 4, 2, 3), (2, 2, 1, 1), (3, 3, 2, 2),              # interior bottleneck (mech i)
]
# width sweep: widths 1..4, L 1..4
SWEEP = []
import itertools
for L in range(1, 5):
    for M in itertools.product(range(1, 5), repeat=L + 1):
        SWEEP.append(M)

claimA = True
claimB = True
worstA = None  # (M, leaf_t0, flatDim)
worstB = None
tightA = []    # instances where t0-numDiv == flatDim (tight)

print("=== KILL-SET (mechanism-aware) ===")
for M in KILLSET:
    s = TrackSim(M).run()
    fd = flatdim(M)
    maxleaf = max(s.leaf_t0_counts, default=0)
    okA = maxleaf <= fd
    okB = s.max_state_numdiv <= fd
    claimA &= okA
    claimB &= okB
    print(f"  M={str(M):16s} flatDim={fd:3d}  max-leaf-t0-numDiv={maxleaf:3d} {'OK' if okA else 'FAIL-A'}"
          f"   max-state-numDiv={s.max_state_numdiv:3d} {'OK' if okB else 'FAIL-B'}  leaves={len(s.leaves)}")

print("\n=== WIDTH SWEEP (widths 1..4, L 1..4) ===")
n = 0
for M in SWEEP:
    n += 1
    s = TrackSim(M).run()
    fd = flatdim(M)
    maxleaf = max(s.leaf_t0_counts, default=0)
    if maxleaf > fd:
        claimA = False
        if worstA is None or (maxleaf - fd) > (worstA[1] - worstA[2]):
            worstA = (M, maxleaf, fd)
    if maxleaf == fd:
        tightA.append((M, maxleaf, fd))
    if s.max_state_numdiv > fd:
        claimB = False
        if worstB is None or (s.max_state_numdiv - fd) > (worstB[1] - worstB[2]):
            worstB = (M, s.max_state_numdiv, fd)

print(f"  scanned {n} instances")
print(f"  Claim A (leaf t0-numDiv <= flatDim): {'PASS' if claimA else 'FAIL'}")
if worstA:
    print(f"    WORST-A violation: M={worstA[0]} leaf-t0-numDiv={worstA[1]} > flatDim={worstA[2]}")
print(f"  Claim B (state full-numDiv <= flatDim): {'PASS' if claimB else 'FAIL'}")
if worstB:
    print(f"    WORST-B violation: M={worstB[0]} state-numDiv={worstB[1]} > flatDim={worstB[2]}")
print(f"  TIGHT-A instances (leaf t0-numDiv == flatDim), first 15: {tightA[:15]}")
print(f"  # tight-A instances: {len(tightA)}")

print("\nRESULT:",
      "PASS (A: leaf-clause holds everywhere)" if claimA else "FAIL-A (surface: leaf-clause FALSE)",
      "|", "B holds" if claimB else "B FALSE (use A-form invariant)")
sys.exit(0 if claimA else 1)
