"""
GM delta-SPECIFY (414862c64) cleared-locus CORE — pnp verification under the #82-winning def (reading (i),
couplingCoords keyed on the STORED pivot). Three targets (ClearedFold.lean):

(a) couplingClear_parent_fixes_stepMap_child  [LOAD-BEARING]:
      couplingClear p (stepMap ed (couplingClear (p.extend ed) u)) = stepMap ed (couplingClear (p.extend ed) u)
    i.e. stepMap sends L_child into L_parent — after clearing the child's couplings and stepping, the
    ANCESTOR couplings (couplingCoords p) are still zero (spectators of the current shear+blow-up).
(b) pivot_notMem_couplingCoords_extend:  ed.pivot ∉ couplingCoords (p.extend ed).
(c) couplingCoords_mono_extend:  couplingCoords p ⊆ couplingCoords (p.extend ed)  [definitional].

Defs (SourceClearedResid.lean / MonumentAtlas.lean, transcribed):
  belowPivotCol (L,a,b) = {(L,r,b): r>a}
  couplingCoords(path) = ∪ over case2/case12 edges of belowPivotCol(edge.pivot)   [keyed on STORED pivot]
  couplingClear(path)(u) = zero the couplingCoords, else u
  stepMap(ed) = blockBlowupMap(center,pivot) ∘ edgeShear(ed)
     edgeShear: case2/case12 → u + canonNormalizationOf(pivot);  case11/rollover → u
     blockBlowupMap(center,pivot)(w): pivot↦w[pivot]; k∈center↦w[pivot]·w[k]; else w[k]
"""
import sympy as sp
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import (dims_coords, canonNormalizationOf, oracle_edges, wmu)

def belowPivotCol(pivot):
    L, a, b = pivot
    # {(L, r, b): r > a} intersected with valid rows handled by caller's coord universe
    return lambda coords: {(LL, r, c) for (LL, r, c) in coords if LL == L and c == b and r > a}

def couplingCoords(d, edges, coords):
    S = set()
    for (case, sL, sC, piv, cen, delta) in edges:
        if case in ("case2", "case12"):
            S |= belowPivotCol(piv)(coords)
    return S

def couplingClear(d, edges, u, coords):
    cc = couplingCoords(d, edges, coords)
    return {k: (sp.Integer(0) if k in cc else u[k]) for k in u}

def edgeShear(u, d, case, sL, sC, piv, scoped=True):
    if case in ("case11", "rollover"):
        return dict(u)
    phi = canonNormalizationOf(u, d, sL, sC, piv, scoped)
    return {k: u[k] + phi[k] for k in u}

def blockBlowupMap(w, piv, cen):
    return {k: (w[piv] if k == piv else (w[piv] * w[k] if k in cen else w[k])) for k in w}

def stepMap(u, d, edge, scoped=True):
    case, sL, sC, piv, cen, delta = edge
    w = edgeShear(u, d, case, sL, sC, piv, scoped)
    return blockBlowupMap(w, piv, cen)

def check_targets(d, edges, coords, label, fan_note=""):
    N, u = dims_coords(d)
    print(f"\n{'='*90}\n{label}{fan_note}\n  branch = {[(e[0], e[3]) for e in edges]}")
    ok_a = ok_b = ok_c = True
    step_edges = [e for e in edges if e[0] != "terminal"]
    for i, ed in enumerate(step_edges):
        parent = step_edges[:i]; child = step_edges[:i + 1]
        cc_p = couplingCoords(d, parent, coords)
        cc_c = couplingCoords(d, child, coords)
        # (c) mono
        mono = cc_p <= cc_c
        # (b) pivot notMem child couplings
        piv_notmem = ed[3] not in cc_c
        # (a) parent fixes stepMap child
        v = couplingClear(d, child, u, coords)
        w = stepMap(v, d, ed)
        fixes = all(sp.expand(sp.sympify(w[k])) == 0 for k in cc_p)
        # diagnostic: which parent coupling coord (if any) is nonzero after stepMap
        bad = [k for k in cc_p if sp.expand(sp.sympify(w[k])) != 0]
        ok_a &= fixes; ok_b &= piv_notmem; ok_c &= mono
        flag = "" if (fixes and piv_notmem and mono) else "  <<< FAIL"
        print(f"  edge {i} {ed[0]:9s} piv={ed[3]}: (a)fixes={fixes} (b)pivNotMem={piv_notmem} "
              f"(c)mono={mono}{flag}")
        if bad:
            print(f"      (a) parent-coupling coords NONZERO after stepMap: {sorted(bad)}")
            for k in bad:
                print(f"          w[{k}] = {sp.expand(sp.sympify(w[k]))}")
    print(f"  SUMMARY: (a)parent-fixes-stepMap-child={ok_a}  (b)pivot-notMem={ok_b}  (c)mono={ok_c}")
    return ok_a, ok_b, ok_c

def center_case2(d, S, J):
    """canonCenterOf shape for a case2/case12 clear at (S,J): {(S,r,c): r>=J, J<=c<wmu}."""
    return {(S, r, c) for r in range(d[S + 1]) for c in range(d[S]) if r >= J and J <= c < wmu(d, S)}

def couplingCoords_diag(d, edges, coords):
    """VARIANT keyed on the DIAGONAL ledger corner cornerToFlat(layer,cleared)=(layer,cleared,cleared)
    instead of the STORED pivot (the #84 alternative). belowPivotCol of the diagonal corner = the
    strictly-below-diagonal entries of the *cleared-index* column."""
    from capstone_adjudication import cornerToFlat
    S = set()
    for (case, sL, sC, piv, cen, delta) in edges:
        if case in ("case2", "case12"):
            S |= belowPivotCol(cornerToFlat(d, sL, sC))(coords)
    return S

def fan_probe():
    """THE FAN STRESS — d=(3,3,3,3), layer 0 (wmu=3): ancestor clear at a HIGH column (col 2, pivot
    (0,0,2)) then col 1 then the FORCED corner (0,2,2). Genuine IsRealBranch: each fan pivot ∈ its
    canonCenterOf (confirmed counter-based `cleared ≤ col < widthMinUpto`), and at cleared=2 canonCenterOf
    = {(0,2,2)} FORCES the third pivot. Two findings:
      (a) SPECTATOR claim ROBUST — the ancestor coupling col 2 sits inside the current block and the shear
          WRITES it, but always as a product -read(row,b_cur)*read(a_cur,col) with a CLEARED factor, so it
          stays 0. Target (a) holds on the fan.
      (b) FAILS under STORED-pivot keying (current def / #82 (i)): edge0's fan pivot (0,0,2) contributes
          belowPivotCol = {(0,1,2),(0,2,2)}, so the FORCED third pivot (0,2,2) ∈ couplingCoords → cleared
          to 0 → foldB_cleared VANISHES → S1 breaks. This is the #84 asymmetry: foldB's factors (STORED
          pivots) vs the clear targets. Under DIAGONAL-corner keying the cleared columns are {0,1}, the
          pivot (0,2,2) is col 2 ∉ them, so (b) HOLDS — the witness that the two roles need different refs."""
    d = (3, 3, 3, 3)
    N, u = dims_coords(d)
    coords = set(u.keys())
    fan = [
        ("case2", 0, 0, (0, 0, 2), center_case2(d, 0, 0), 1),   # cleared=0, HIGH col 2
        ("case2", 0, 1, (0, 1, 1), center_case2(d, 0, 1), 1),   # cleared=1, col 1 (< prev col 2)
        ("case2", 0, 2, (0, 2, 2), center_case2(d, 0, 2), 1),   # cleared=2, FORCED corner (0,2,2)
    ]
    res = check_targets(d, fan, coords, "FAN STRESS d=(3,3,3,3) layer-0 [pivot cols 2,1,2]",
                        fan_note="  (ancestor coupling col 2 >= later cleared 1 ⟹ inside current block)")
    # #84 asymmetry witness: (b) under STORED vs DIAGONAL keying for the FORCED pivot (0,2,2)
    cc_stored = couplingCoords(d, fan, coords)
    cc_diag = couplingCoords_diag(d, fan, coords)
    print(f"\n  #84 ASYMMETRY WITNESS (forced 3rd pivot (0,2,2)):")
    print(f"    STORED-keyed couplingCoords = {sorted(cc_stored)}  ⟹ pivot∈coords: {(0,2,2) in cc_stored}"
          f"  ⟹ foldB pivot factor CLEARED (foldB_cleared=0, S1 breaks)")
    print(f"    DIAGONAL-keyed couplingCoords = {sorted(cc_diag)}  ⟹ pivot∈coords: {(0,2,2) in cc_diag}"
          f"  ⟹ foldB factor SURVIVES")
    return res

def run():
    results = {}
    for d in [(2, 2, 2, 2), (2, 3, 2, 2), (3, 3, 2, 2)]:
        edges, meta = oracle_edges(d)
        N, u = dims_coords(d)
        coords = set(u.keys())
        results[d] = check_targets(d, edges, coords, f"CANONICAL d={d}")
    fan = fan_probe()
    canon_ok = all(all(r) for r in results.values())
    print(f"\n{'#'*90}\nCANONICAL VERDICT: all three targets (a)(b)(c) hold on every node/case: {canon_ok}")
    print(f"FAN-STRESS: (a) spectator-fixes robust = {fan[0]}; (c) mono robust = {fan[2]}; "
          f"(b) pivot-notMem under STORED keying = {fan[1]} (EXPECTED-FALSE — #84 witness, not a regression)")
    assert canon_ok, "canonical must hold on every node/case"
    assert fan[0] and fan[2], "target (a) and (c) must be robust to the fan"

if __name__ == "__main__":
    run()
