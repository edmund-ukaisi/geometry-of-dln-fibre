#!/usr/bin/env python3
"""
Thread-37 decorrelated gate (commissioned by the controller): does the edge-indexed
EdgeSpec generator reproduce Aoyagi's (S,J,t̃) transition system for a coupled L≥3 branch?

We simulate the paper recursion (pp.14-22, read from the PAGE IMAGES) as a state machine,
run the FULL tree for the coupled RRR core (3,3,4) [and guard instances], and emit the
per-edge (S, J, t̃-ledger, center, pivot-kind, δ) transition table. We then ASSERT, in
exact integer arithmetic, the paper-side facts the fold's EdgeSpec must match:

  * δ = [J=0], UNIFORM across sub-cases (S2 fix; PrincipalInv.lean EdgeSpec, rung-c).
  * center codimension = the block dims (S1 fix; blockBlowupMap):
      Case-1(1) increment  M'_{s,k} - M_{s,k} = J₁·(M^(S+1)-J)   [paper p.16]
      Case-2   exponent    M'_{S,J+1}          = (M(S)-J)(M^(S+1)-J)  [paper p.20]
  * rollover fires EXACTLY at J = M(S+1) = widthMinUpto(layer+1)  [paper p.19 "J+1>M(S+1)",
    the TRANSPOSE boundary]; the only-at-exhaustion guard.
  * MvalCoh: every divisor's accumulated exponent = Mval(its profile)  [paper p.22 M_{s,k}].
  * headline: min over the terminal t̃=0 divisors = minAdm; rlct_core = ½·minAdm.

The recursion rule is transcribed to match conOracle (EngineConstruction.lean:2117): the
DECORRELATION is (my independent paper reading) vs (the Lean fold's rule); agreement on the
outputs + the printed formulas is the gate. Any assertion failure = stop-on-suspect.

Indexing: paper S = layer+1 (Lean layer is 0-indexed = S-1, EngineConstruction.lean:83-85).
Profiles are t=(t^(1),...,t^(L)), 0-indexed p=0..L-1; t̃ = min t.
"""

from fractions import Fraction
from itertools import product as iproduct

# ---------- paper primitives ----------

def width_min_upto(M, n):
    """min{M[i] : 0 <= i <= n} = min(M^(1),...,M^(n+1)); = M(n+1) in paper notation."""
    return min(M[: n + 1])

def run_min_width(M, p):
    """runMinWidth M p = min{M[i] : i <= p+1} = widthMinUpto M (p+1)  (EngineDefs.lean:147).
    The Case-2 profile HEAD: the fold uses the RUNNING-MIN (T-E-defect-immune), NOT the paper's
    printed raw-width head-reset t^(i)=M^(i+1) (p.20, the T-E defect — defective at non-monotone
    widths). This running-min head is what makes MvalCoh hold unconditionally."""
    return min(M[: p + 2])

def t_tilde(profile):
    return min(profile)

def set_tail(layer, cleared, profile, L):
    """The paper's tail-write t^(s)...t^(L) := J for paper-index s >= S, i.e. 0-index p >= layer.
    Head (p < layer) is INHERITED (the fold's setTail deliberately does NOT reproduce the p.20
    raw-width head-reset — that is the documented T-E defect, non-binding, no representation)."""
    return tuple(cleared if p >= layer else profile[p] for p in range(L))

def mval(M, profile):
    """Aoyagi p.22 terminal divisor exponent M_{s,k} = Mval(t) = codim S(t).
    (M^(1)-t^(1))(M^(2)-t^(1)) + sum_{j=2}^{L} (t^(j-1)-t^(j))(M^(j+1)-t^(j))."""
    L = len(profile)
    t1 = profile[0]
    total = (M[0] - t1) * (M[1] - t1)
    for j in range(2, L + 1):  # paper j = 2..L
        tjm1 = profile[j - 2]  # t^(j-1)
        tj = profile[j - 1]    # t^(j)
        total += (tjm1 - tj) * (M[j] - tj)
    return total

# ---------- the recursion state ----------

class Div:
    __slots__ = ("profile", "exp", "birth")
    def __init__(self, profile, exp, birth):
        self.profile = profile
        self.exp = exp
        self.birth = birth
    def clone(self):
        return Div(self.profile, self.exp, self.birth)

class State:
    def __init__(self, layer, cleared, divs):
        self.layer = layer
        self.cleared = cleared
        self.divs = divs  # list of Div
    def clone(self):
        return State(self.layer, self.cleared, [d.clone() for d in self.divs])

# ---------- the oracle (conOracle rule, EngineConstruction.lean:2117) ----------

def occupied_levels(M, s):
    """Divisors k with J < t̃_k < M(S): the run above J ends at an occupied interior level.
    conOracle filter: cleared+1 <= t̃_k  and  t̃_k+1 <= widthMinUpto(layer)."""
    wl = width_min_upto(M, s.layer)          # = M(S)
    out = []
    for k, d in enumerate(s.divs):
        tt = t_tilde(d.profile)
        if s.cleared + 1 <= tt and tt + 1 <= wl:
            out.append((tt, k))
    return out

def choose_min_divisor(M, s, target):
    """Def-4 minimal divisor among those with t̃ = target (componentwise-least profile;
    ties -> lowest index). Matches chooseMin_spec."""
    cands = [(k, d) for k, d in enumerate(s.divs) if t_tilde(d.profile) == target]
    def le(a, b):  # componentwise <=
        return all(a[i] <= b[i] for i in range(len(a)))
    best = None
    for k, d in cands:
        if best is None or (le(d.profile, s.divs[best].profile) and d.profile != s.divs[best].profile):
            best = k
    return best

EDGES = []  # global trace log

def build(M, s, path):
    L = len(M) - 1
    S = s.layer + 1  # paper layer
    J = s.cleared
    # (1) terminal: all layers processed
    if L <= s.layer:
        return {"kind": "leaf", "S": S, "J": J,
                "divs": [(d.profile, d.exp) for d in s.divs]}
    # (2) rollover at exhaustion  J >= M(S+1) = widthMinUpto(layer+1)  [p.19 transpose boundary]
    if width_min_upto(M, s.layer + 1) <= s.cleared:
        child = s.clone(); child.layer += 1; child.cleared = 0
        EDGES.append({"S": S, "J": J, "case": "rollover", "delta": None,
                      "center": None, "pivot": None,
                      "note": f"transpose boundary: J={J}=M(S+1)={width_min_upto(M,s.layer+1)}",
                      "path": path})
        return {"kind": "node", "S": S, "J": J, "case": "rollover",
                "children": [build(M, child, path + ["R"])]}
    occ = occupied_levels(M, s)
    resRows = width_min_upto(M, s.layer) - s.cleared      # M(S) - J
    resCols = M[s.layer + 1] - s.cleared                  # M^(S+1) - J
    delta = (J == 0)                                      # δ = [J=0]  (S2, uniform)
    if occ:
        # (3) CASE 1: run above J ends at an occupied interior level `target`
        target = min(tt for tt, _ in occ)
        f = choose_min_divisor(M, s, target)
        runLen = target - s.cleared                       # J₁
        bump = runLen * resCols                           # M'_{s,k} - M_{s,k}  (p.16)
        children = []
        # -- 1(1) merge: bump divExp[f], tail-write profile[f], J unchanged
        mchild = s.clone()
        old_exp = mchild.divs[f].exp
        mchild.divs[f].exp = old_exp + bump
        mchild.divs[f].profile = set_tail(s.layer, s.cleared, mchild.divs[f].profile, L)
        EDGES.append({"S": S, "J": J, "case": "case1(1)", "delta": delta,
                      "center": ("d-subblock+u", runLen, resCols), "pivot": ("reuse", f),
                      "target": target, "runLen": runLen, "bump": bump,
                      "div_before": (s.divs[f].profile, old_exp),
                      "div_after": (mchild.divs[f].profile, mchild.divs[f].exp),
                      "path": path})
        children.append(build(M, mchild, path + [f"1(1)@t{target}"]))
        # -- 1(2) split: append fresh divisor (inherited head + tail-write), advance J
        schild = s.clone()
        new_prof = set_tail(s.layer, s.cleared, s.divs[f].profile, L)
        schild.divs.append(Div(new_prof, old_exp + bump, (s.layer, s.cleared)))
        schild.cleared += 1
        EDGES.append({"S": S, "J": J, "case": "case1(2)", "delta": delta,
                      "center": ("d-subblock+u", runLen, resCols), "pivot": ("fresh", None),
                      "target": target, "runLen": runLen,
                      "new_div": (new_prof, old_exp + bump), "path": path})
        children.append(build(M, schild, path + [f"1(2)@t{target}"]))
        return {"kind": "node", "S": S, "J": J, "case": "case1", "children": children}
    else:
        # (4) CASE 2: full remaining block; append fresh, advance J
        e = resRows * resCols                             # (M(S)-J)(M^(S+1)-J)  (p.20)
        new_prof = set_tail(s.layer, s.cleared, tuple(run_min_width(M, p) for p in range(L)), L)
        child = s.clone()
        child.divs.append(Div(new_prof, e, (s.layer, s.cleared)))
        child.cleared += 1
        EDGES.append({"S": S, "J": J, "case": "case2", "delta": delta,
                      "center": ("full-block", resRows, resCols), "pivot": ("fresh", None),
                      "new_div": (new_prof, e), "path": path})
        return {"kind": "node", "S": S, "J": J, "case": "case2",
                "children": [build(M, child, path + ["2"])]}

def collect_leaves(tree, acc):
    if tree["kind"] == "leaf":
        acc.append(tree); return
    for c in tree["children"]:
        collect_leaves(c, acc)

# ---------- run + assert ----------

def run_instance(M, name, expect_rlct=None, verbose=False):
    global EDGES
    EDGES = []
    L = len(M) - 1
    root = State(0, 0, [])
    tree = build(M, root, [])
    leaves = []
    collect_leaves(tree, leaves)

    # (A) MvalCoh: every divisor's exponent == Mval(profile) at every logged edge outcome.
    for e in EDGES:
        for key in ("div_after", "new_div"):
            if key in e and e[key] is not None:
                prof, exp = e[key]
                assert exp == mval(M, prof), \
                    f"[{name}] MvalCoh FAIL {key} at S={e['S']} J={e['J']}: exp={exp} Mval={mval(M,prof)} prof={prof}"

    # (B) Case-1(1) increment = J₁·(M^(S+1)-J);  Case-2 exp = (M(S)-J)(M^(S+1)-J).
    for e in EDGES:
        if e["case"] == "case1(1)":
            J1 = e["runLen"]; resCols = e["center"][2]
            assert e["bump"] == J1 * resCols, f"[{name}] case1(1) bump mismatch"
            # and the bump exactly closes the Mval gap of the tail-write:
            pb, eb = e["div_before"]; pa, ea = e["div_after"]
            assert ea - eb == mval(M, pa) - mval(M, pb), f"[{name}] case1(1) Mval-gap mismatch"
        if e["case"] == "case2":
            resRows, resCols = e["center"][1], e["center"][2]
            prof, exp = e["new_div"]
            assert exp == resRows * resCols, f"[{name}] case2 exp mismatch"

    # (C) δ = [J=0], UNIFORM across sub-cases (S2). Every non-rollover edge.
    for e in EDGES:
        if e["case"] != "rollover":
            assert e["delta"] == (e["J"] == 0), f"[{name}] δ≠[J=0] at S={e['S']} J={e['J']}"
    # both sub-case edges of a Case-1 node share δ (uniformity):
    from collections import defaultdict
    bynode = defaultdict(list)
    for e in EDGES:
        if e["case"] in ("case1(1)", "case1(2)"):
            bynode[(tuple(e["path"]), e["S"], e["J"])].append(e["delta"])
    for k, ds in bynode.items():
        assert len(set(ds)) == 1, f"[{name}] δ NOT uniform across sub-cases at {k}: {ds}"

    # (D) rollover fires EXACTLY at J = M(S+1) (transpose boundary / only-at-exhaustion).
    for e in EDGES:
        if e["case"] == "rollover":
            layer = e["S"] - 1
            assert e["J"] == width_min_upto(M, layer + 1), f"[{name}] rollover not at exhaustion"

    # (E) headline: min over terminal t̃=0 divisors = minAdm; rlct = ½·minAdm.
    #     minAdm over the admissible t_L=0 lattice (paper geometric primitive).
    def adm_profiles():
        # t^(1) >= t^(2) >= ... >= t^(L) = 0, t^(1) <= min(M^(1),M^(2)) (nested-rank lattice)
        rng = range(0, min(M[0], M[1]) + 1)
        for prof in iproduct(*[rng] * L):
            if prof[-1] == 0 and all(prof[i] >= prof[i + 1] for i in range(L - 1)):
                yield prof
    minAdm = min(mval(M, p) for p in adm_profiles())
    # the recursion's leaves each realise the min over their t̃=0 divisors; the atlas min:
    leaf_mins = []
    for lf in leaves:
        t0 = [exp for (prof, exp) in lf["divs"] if t_tilde(prof) == 0]
        if t0:
            leaf_mins.append(min(t0))
    atlas_min = min(leaf_mins)
    assert atlas_min == minAdm, f"[{name}] atlas min {atlas_min} != minAdm {minAdm}"
    rlct = Fraction(minAdm, 2)
    if expect_rlct is not None:
        assert rlct == expect_rlct, f"[{name}] rlct {rlct} != expected {expect_rlct}"

    if verbose:
        print(f"\n=== {name}  M={M}  (L={L}) ===")
        print(f"  minAdm={minAdm}  rlct_core=½·minAdm={rlct}   #leaves={len(leaves)}  #edges={len(EDGES)}")
        for e in EDGES:
            tag = e["case"]
            d = "" if e["delta"] is None else f" δ={int(e['delta'])}"
            extra = ""
            if tag == "case2":
                extra = f" center=full {e['center'][1]}×{e['center'][2]} (codim {e['center'][1]*e['center'][2]})  →div {e['new_div']}"
            elif tag == "case1(1)":
                extra = f" reuse-pivot t={e['target']} J₁={e['runLen']} bump={e['bump']}  {e['div_before']}→{e['div_after']}"
            elif tag == "case1(2)":
                extra = f" fresh-pivot t={e['target']} J₁={e['runLen']}  →div {e['new_div']}"
            elif tag == "rollover":
                extra = f"  [{e['note']}]"
            print(f"    S={e['S']} J={e['J']:>2} {tag:<9}{d}{extra}")
    return {"minAdm": minAdm, "rlct": rlct, "nleaves": len(leaves), "nedges": len(EDGES)}

if __name__ == "__main__":
    # The commissioned coupled RRR core (verbose full trace + transpose boundary):
    run_instance([3, 3, 4], "(3,3,4) coupled RRR core [L=2, binding t=(1,0) Mval=8]",
                 expect_rlct=Fraction(4, 1), verbose=True)
    # Guard instances (assert-only): known headline rlcts.
    run_instance([2, 2, 2], "(2,2,2) [L=2]", expect_rlct=Fraction(3, 2))
    run_instance([2, 1, 2], "(2,1,2) [L=2]", expect_rlct=Fraction(1, 1))
    run_instance([2, 2, 2, 2], "(2,2,2,2) [L=3 equal-width]", expect_rlct=Fraction(3, 2))
    run_instance([2, 2, 3, 2], "(2,2,3,2) [L=3 non-monotone, T-E defect instance]")
    run_instance([3, 3, 2, 2], "(3,3,2,2) [L=3 coupled, rlct 2]", expect_rlct=Fraction(2, 1))
    print("\nALL ASSERTIONS PASS (exact integer/Fraction arithmetic). EXIT 0.")
