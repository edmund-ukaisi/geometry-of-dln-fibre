#!/usr/bin/env python3
# guards: resolution-tree, coverage-theorem
# provenance: threads/08-atlas-probe (pnp08), THIRD task -- fork 12(b). A page-faithful RAW-T
#   simulator of Aoyagi's Section-5 recursion (rules verbatim p.14-22, incl. the p.20 raw-width
#   head-reset t^(i):=M^(i+1)). NOT the Lean engine. Integer-only, exact. VALIDATED against the
#   known t~=0 atlases at (2,2,2),(3,3,4),(2,2,2,2) before being trusted at (2,2,3,2).
"""fork 12(b): at the minimal non-monotone L=3 instance (2,2,3,2), does the raw-width Case-2
head-reset produce a NON-weakly-decreasing profile that reaches a leaf, and do leaves carry only
tilde_t=0 divisors?  KILL = a leaf divisor not in Adm(2,2,3,2).

Model (reconstructed from the pages; matches Codex's validated replay on the monotone instances):
  * process(S,J,divs). L layers. M(S)=min(M^1..M^S). Layer S clears J=0..M(S+1)=min(M(S),M^{S+1}),
    then S advances (J resets to 0). At S=L+1: leaf.
  * b-chain levels = tilde_t values. Run above J: first occupied level in [J+1, M(S)-1].
      - if such a level exists -> CASE 1 (branch): fix the Def-4-minimum divisor at that level;
        1(1) mutate it (tail:=J, M+=J1*(M^{S+1}-J), stay at J); 1(2) create child (inherit head,
        tail:=J, M=parentM+J1*(M^{S+1}-J), advance J).
      - else -> CASE 2: create divisor (head t^(i):=RAW M^{(i+1)} for i<S; tail:=J;
        M=(M(S)-J)(M^{S+1}-J); advance J).
  * Def-4 min = the componentwise-<= least among the candidates; if the candidates are NOT a chain
    (no componentwise min) we RECORD a comparability violation (a construction-invariant break).
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


class Sim:
    def __init__(self, M, headreset="raw", check_inv=False):
        self.M = tuple(M)                 # M^1..M^{L+1}, 0-indexed
        self.L = len(M) - 1
        self.headreset = headreset        # "raw" (p.20-literal M^{i+1}) or "runmin" (FIX-A: M(i+1))
        self.check_inv = check_inv        # verify the o4 supporting sub-invariants at every state
        self.leaves = []
        self.comp_violations = []
        self.node_count = 0
        self.flat_viol = 0                # FlatTail: T_S=...=T_L at state (S,J)
        self.chain_viol = 0              # full total-comparability of ALL carried pairs
        self.width_viol = 0              # width-bound: t^i <= M(i+1) (running-min)
        self.case2_tail_viol = 0         # Case 2 => every carried tilde_t <= J

    def Mw(self, i):                       # M^(i), 1-indexed
        return self.M[i - 1]

    def Mrun(self, S):                     # M(S) = min M^1..M^S
        return min(self.M[:S])

    def tilde(self, T):
        return min(T)

    def set_tail(self, T, S, J):
        T = list(T)
        for j in range(S, self.L + 1):     # components S..L (1-indexed)
            T[j - 1] = J
        return tuple(T)

    def def4_min(self, cands):
        """componentwise-<= least; record a violation if candidates are not a chain."""
        best = None
        for c in cands:
            if all(all(a <= b for a, b in zip(c[0], d[0])) for d in cands):
                best = c
                break
        if best is None:                   # no componentwise minimum -> comparability broken
            self.comp_violations.append([c[0] for c in cands])
            best = min(cands, key=lambda d: d[0])   # fall back (lex) so the run can continue
        return best

    def run(self):
        self._proc(1, 0, [])
        return self

    def _check(self, S, J, divs):
        Ts = [d[0] for d in divs]
        # FlatTail: components S..L (1-indexed) all equal
        for T in Ts:
            if len(set(T[S - 1:])) > 1:
                self.flat_viol += 1
        # full total-comparability of ALL carried pairs
        for a in range(len(Ts)):
            for b in range(a + 1, len(Ts)):
                x, y = Ts[a], Ts[b]
                if not (all(p <= q for p, q in zip(x, y)) or all(p >= q for p, q in zip(x, y))):
                    self.chain_viol += 1
        # width-bound (running-min): t^i <= M(i+1)
        for T in Ts:
            for i in range(1, self.L + 1):
                if T[i - 1] > self.Mrun(i + 1):
                    self.width_viol += 1
        # Case-2 => every carried tilde_t <= J
        MS = self.Mrun(S)
        occ = [m for m in {self.tilde(T) for T in Ts} if J + 1 <= m <= MS - 1]
        if not occ and Ts:                 # Case 2 at this node
            if any(self.tilde(T) > J for T in Ts):
                self.case2_tail_viol += 1

    def _proc(self, S, J, divs):
        self.node_count += 1
        if self.node_count > 200000:
            raise RuntimeError("runaway recursion")
        if S == self.L + 1:
            self.leaves.append(tuple(sorted((tuple(d[0]), d[1]) for d in divs)))
            return
        if self.check_inv:
            self._check(S, J, divs)
        MS = self.Mrun(S)
        MSp1 = min(MS, self.Mw(S + 1))     # M(S+1) = max pivots this layer
        if J >= MSp1:
            self._proc(S + 1, 0, divs)
            return
        levels = sorted({self.tilde(d[0]) for d in divs})
        occ_above = [m for m in levels if J + 1 <= m <= MS - 1]
        if occ_above:                      # CASE 1
            target = occ_above[0]
            J1 = target - J
            cands = [d for d in divs if self.tilde(d[0]) == target]
            f = self.def4_min(cands)
            bump = J1 * (self.Mw(S + 1) - J)
            # 1(1): mutate the fixed divisor (stay at J)
            fT2 = self.set_tail(f[0], S, J)
            divs_U = [d for d in divs if d is not f] + [(fT2, f[1] + bump)]
            self._proc(S, J, divs_U)
            # 1(2): create child inheriting parent's head, advance J
            childT = self.set_tail(f[0], S, J)          # head t^(1..S-1) = parent head (unchanged
            #   slice below S), tail t^(S..L):=J  -> identical shape to 1(1)'s target vector
            divs_D = list(divs) + [(childT, f[1] + bump)]
            self._proc(S, J + 1, divs_D)
        else:                              # CASE 2 head-reset
            T = [0] * self.L
            for i in range(1, S):          # head i=1..S-1
                if self.headreset == "runmin":
                    T[i - 1] = self.Mrun(i + 1)     # FIX-A: running-min M(i+1)
                else:
                    T[i - 1] = self.Mw(i + 1)       # p.20-literal RAW M^{(i+1)}
            T = self.set_tail(tuple(T), S, J)
            Mexp = (MS - J) * (self.Mw(S + 1) - J)
            self._proc(S, J + 1, list(divs) + [(T, Mexp)])


def Mval(M, t):
    L = len(M) - 1
    v = (M[0] - t[0]) * (M[1] - t[0])
    for j in range(2, L + 1):
        v += (t[j - 2] - t[j - 1]) * (M[j] - t[j - 1])
    return v


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


def weakly_decreasing(T):
    return all(T[i] >= T[i + 1] for i in range(len(T) - 1))


def in_Adm(M, T):
    """Adm: weakly decreasing, t^1<=min(M^1,M^2), t^j<=min(t^{j-1},M^{j+1}), t^L=0."""
    L = len(M) - 1
    if not weakly_decreasing(T):
        return False
    if T[-1] != 0:
        return False
    if T[0] > min(M[0], M[1]):
        return False
    for j in range(2, L + 1):
        if T[j - 1] > min(T[j - 2], M[j]):
            return False
    return True


def analyze(M, label, validate_against=None, headreset="raw"):
    sim = Sim(M, headreset=headreset).run()
    L = len(M) - 1
    # all distinct leaf divisors across leaves
    all_divs = set()
    for leaf in sim.leaves:
        all_divs.update(leaf)
    t0_profiles = sorted({T for (T, m) in all_divs if min(T) == 0})
    tpos = sorted({(T, m) for (T, m) in all_divs if min(T) > 0})
    t0_min = min((m for (T, m) in all_divs if min(T) == 0), default=None)
    nonwd = sorted({(T, m, min(T)) for (T, m) in all_divs if not weakly_decreasing(T)})
    t0_not_adm = sorted({(T, m) for (T, m) in all_divs if min(T) == 0 and not in_Adm(M, T)})
    leaves_with_tpos = sum(1 for leaf in sim.leaves if any(min(T) > 0 for (T, m) in leaf))

    print(f"=== {label}  M={M}  minAdm={minAdm(M)}  leaves={len(sim.leaves)}"
          f"  comparability-violations={len(sim.comp_violations)} ===")
    print(f"  t~=0 leaf profiles: {t0_profiles}")
    print(f"  t~=0 min M = {t0_min}   (minAdm={minAdm(M)}; equal: {t0_min == minAdm(M)})")
    if validate_against is not None:
        got = set(t0_profiles)
        exp = set(validate_against)
        print(f"  VALIDATE t~=0 profiles == expected {sorted(exp)}: {got == exp}")
    print(f"  leaves carrying tilde_t>0 divisors: {leaves_with_tpos}/{len(sim.leaves)}")
    if tpos:
        print(f"  distinct tilde_t>0 leaf divisors (T,M): {tpos}")
    print(f"  NON-weakly-decreasing leaf divisors (T,M,tilde_t): {nonwd if nonwd else 'NONE'}")
    print(f"  tilde_t=0 leaf divisors NOT in Adm: {t0_not_adm if t0_not_adm else 'NONE'}")
    print()
    return sim, t0_profiles, t0_min, nonwd, t0_not_adm


ok = True
# ---- VALIDATION on the three known atlases (t~=0 profile set + min) ----
_, p, mn, _, _ = analyze((2, 2, 2), "VALIDATE (2,2,2)", [t for t in nested_profiles((2, 2, 2))])
ok &= (set(p) == set(nested_profiles((2, 2, 2))) and mn == minAdm((2, 2, 2)))
_, p, mn, _, _ = analyze((3, 3, 4), "VALIDATE (3,3,4)", [t for t in nested_profiles((3, 3, 4))])
ok &= (set(p) == set(nested_profiles((3, 3, 4))) and mn == minAdm((3, 3, 4)))
_, p, mn, _, _ = analyze((2, 2, 2, 2), "VALIDATE (2,2,2,2)", [t for t in nested_profiles((2, 2, 2, 2))])
ok &= (set(p) == set(nested_profiles((2, 2, 2, 2))) and mn == minAdm((2, 2, 2, 2)))

print("VALIDATION on monotone instances:", "PASS" if ok else "FAIL", "\n" + "=" * 70 + "\n")

# ---- THE TARGET: (2,2,3,2) ----
sim, t0_profiles, t0_min, nonwd, t0_not_adm = analyze((2, 2, 3, 2), "TARGET (2,2,3,2)")
print("Admissible nested profiles (reference):", nested_profiles((2, 2, 3, 2)))
print(f"  their Mval: {[(t, Mval((2,2,3,2), t)) for t in nested_profiles((2,2,3,2))]}\n")

# ---- FULL per-leaf detail + within-leaf total-comparability check for (2,2,3,2) ----
M = (2, 2, 3, 2)


def comparable(a, b):
    return all(x <= y for x, y in zip(a, b)) or all(x >= y for x, y in zip(a, b))


print("--- per-leaf detail (2,2,3,2): each divisor (T, tilde_t, M_accumulated) ---")
for i, leaf in enumerate(sorted(set(sim.leaves))):
    divs = sorted(leaf)
    pairs = list(divs)
    # within-leaf total comparability
    bad = [(a[0], b[0]) for x, a in enumerate(pairs) for b in pairs[x + 1:]
           if not comparable(a[0], b[0])]
    ann = []
    for (T, m) in divs:
        tag = ""
        if min(T) == 0 and not in_Adm(M, T):
            tag = " <-NOT-Adm(t~=0)"
        elif not weakly_decreasing(T):
            tag = " <-non-wd(t~>0)"
        ann.append(f"{T}[t~={min(T)},M={m}]{tag}")
    print(f"  leaf {i}: " + ", ".join(ann))
    if bad:
        print(f"      ** within-leaf INCOMPARABLE pairs (total-comparability VIOLATED): {bad}")

# ---- exponent consistency: accumulated M vs p.22 Mval formula, per t~=0 divisor ----
print("\n--- accumulated M  vs  p.22 Mval formula, per t~=0 leaf profile ---")
seen = {}
for leaf in sim.leaves:
    for (T, m) in leaf:
        if min(T) == 0:
            seen[T] = m
for T in sorted(seen):
    f = Mval(M, T)
    print(f"  {T}: accumulated M={seen[T]}   p.22 Mval={f}   consistent: {seen[T]==f}"
          f"   {'(NOT in Adm)' if not in_Adm(M,T) else ''}")

# ---- FIX-A confirmation: running-min head-reset makes the (2,2,3,2) atlas Adm-clean ----
print("\n" + "=" * 70)
print("FIX-A CHECK: Case-2 head-reset = running-min M(i+1) (instead of raw M^{i+1})")
simA = Sim((2, 2, 3, 2), headreset="runmin").run()
divsA = set()
for leaf in simA.leaves:
    divsA.update(leaf)
t0A = sorted({T for (T, m) in divsA if min(T) == 0})
nonwdA = sorted({T for (T, m) in divsA if not weakly_decreasing(T)})
t0_not_admA = sorted({(T, m) for (T, m) in divsA if min(T) == 0 and not in_Adm(M, T)})
t0minA = min((m for (T, m) in divsA if min(T) == 0), default=None)
print(f"  t~=0 leaf profiles (FIX-A): {t0A}")
print(f"  t~=0 min M = {t0minA} (minAdm={minAdm(M)}; equal: {t0minA==minAdm(M)})")
print(f"  NON-weakly-decreasing leaf divisors (FIX-A): {nonwdA if nonwdA else 'NONE'}")
print(f"  t~=0 leaf divisors NOT in Adm (FIX-A): {t0_not_admA if t0_not_admA else 'NONE'}")
fixA_clean = (not t0_not_admA) and (set(t0A) == set(nested_profiles(M))) and (t0minA == minAdm(M))
print(f"  FIX-A closes the gate (atlas Adm-clean, profiles == admissible, min == minAdm): {fixA_clean}")


# ============================================================================
# PRE-COMMIT CLARIFIER (fork 13): higher-L non-monotone instances the certs never reached.
#   (i) comp_violations = reachable incomparable ELIGIBLE pair -> CompChainInv-closure kill (o1/o4).
#   (ii) t~=0 profile-set == Adm -> realization kill (o5-IN).
#   Both head-reset modes: raw (p.20-literal) and runmin (FIX-A; the oracle transcribes this).
# ============================================================================
def clarify(M, headreset):
    s = Sim(M, headreset=headreset).run()
    divs = set()
    for leaf in s.leaves:
        divs.update(leaf)
    t0 = sorted({T for (T, m) in divs if min(T) == 0})
    t0min = min((m for (T, m) in divs if min(T) == 0), default=None)
    adm = set(nested_profiles(M))
    return {"leaves": len(s.leaves), "nodes": s.node_count,
            "comp_violations": len(s.comp_violations), "pairs": s.comp_violations[:5],
            "profset_eq_Adm": set(t0) == adm, "profset_minus_Adm": sorted(set(t0) - adm),
            "min_eq_minAdm": t0min == minAdm(M), "t0min": t0min}


print("\n" + "=" * 72)
print("PRE-COMMIT CLARIFIER (fork 13) — higher-L non-monotone, both head-reset modes")
print("=" * 72)
clar_ok = True
for Mc in [(2, 2, 3, 3, 2), (3, 2, 4, 2)]:
    print(f"\n### M={Mc}   L={len(Mc)-1}   minAdm={minAdm(Mc)}   "
          f"|Adm nested profiles|={len(nested_profiles(Mc))}")
    for mode in ("raw", "runmin"):
        r = clarify(Mc, mode)
        print(f"  [{mode:6s}] leaves={r['leaves']:4d} nodes={r['nodes']:6d}  "
              f"comp_violations={r['comp_violations']}  "
              f"profile-set==Adm: {r['profset_eq_Adm']}  "
              f"min==minAdm: {r['min_eq_minAdm']} (min={r['t0min']})")
        if r["comp_violations"]:
            print(f"          ** INCOMPARABLE ELIGIBLE PAIRS: {r['pairs']}")
        if not r["profset_eq_Adm"]:
            print(f"          profile-set \\ Adm = {r['profset_minus_Adm']}")
        clar_ok &= (r["comp_violations"] == 0)
        if mode == "runmin":
            clar_ok &= r["profset_eq_Adm"] and r["min_eq_minAdm"]

print("\nCLARIFIER:", "PASS (0 comp_violations both modes; runmin profile-set==Adm)"
      if clar_ok else "FAIL — a kill fired, RESHAPE the oracle unit")


# ============================================================================
# o4 SUB-INVARIANT VERIFICATION (task 2): at EVERY reachable state, in the corrected
#   runmin (FIX-A) construction, verify the sub-invariants the CompChainInv proof consumes:
#     FlatTail  : T_S = ... = T_L                (the load-bearing fact for lemma A)
#     Chain     : ALL carried pairs comparable   (full CompChainInv, not just eligible pairs)
#     WidthBnd  : t^i <= M(i+1) (running-min)     (lemma B, case-2 head is the chain top)
#     Case2Tail : Case 2 => every carried tilde_t <= J   (lemma B, case-2 tail dominates)
# ============================================================================
print("\n" + "=" * 72)
print("o4 SUB-INVARIANT VERIFICATION (runmin/FIX-A) at every reachable state")
print("=" * 72)
inv_ok = True
for Mc in [(2, 2, 2), (3, 3, 4), (2, 2, 2, 2), (2, 2, 3, 2), (2, 2, 3, 3, 2), (3, 2, 4, 2)]:
    s = Sim(Mc, headreset="runmin", check_inv=True).run()
    v = (s.flat_viol, s.chain_viol, s.width_viol, s.case2_tail_viol)
    clean = (v == (0, 0, 0, 0))
    inv_ok &= clean
    print(f"  M={str(Mc):15s} nodes={s.node_count:6d}  FlatTail_viol={v[0]}  Chain_viol={v[1]}  "
          f"WidthBnd_viol={v[2]}  Case2Tail_viol={v[3]}  {'OK' if clean else 'VIOLATION'}")
print("\nSUB-INVARIANTS:", "ALL CLEAN (0 violations across all instances)" if inv_ok
      else "VIOLATION — the proof's supporting invariant is FALSE")

sys.exit(0 if (ok and inv_ok) else 1)
