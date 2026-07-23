"""
GM's TWO STRUCTURAL CERTIFICATES (pnp; team-lead relay for GM's proofs of target (a) + S2).

CERT (i) — SHEAR-WRITE-CLEARED-FACTOR (behind target (a) couplingClear_parent_fixes_stepMap_child):
  For every ANCESTOR coupling coord k ∈ couplingCoords d p, the current step's edgeShear
  (canonNormalizationOf …) writes ZERO at k on the CHILD cleared locus (couplingClear d (p.extend ed) u),
  and blockBlowupMap keeps it 0. Mechanism (the a8a956809 structural argument), by canonNormalizationOf arm:
   - branch (i) INTERIOR (L=S, row≠a, col≠b): write = -readEntry(row,b_cur)·readEntry(a_cur,col). At an
     ancestor coupling k=(S,r,b_anc) [r>a_anc], one factor is ALWAYS a cleared coupling:
       * r>a_cur ⟹ readEntry(r,b_cur)=(S,r,b_cur) is below the CURRENT pivot ⟹ current couplingCoords ⟹ 0;
       * r<a_cur ⟹ a_cur>r>a_anc ⟹ readEntry(a_cur,b_anc)=(S,a_cur,b_anc) is below the ANCESTOR pivot ⟹ 0.
   - branch (ii) L=S+1: ancestor couplings live at layers ≤ S (clears advance upward), so NEVER touched.
   - branch (iii) L=S-1, row=b_cur: write vanishes on the cleared locus too (verified; same factor argument).
  VERIFIED: shear writes 0 at every ancestor coupling on the child cleared locus, every edge, 3 witnesses.

CERT (ii) — S2 EXTEND, WITH A DESIGN SIGNAL. The sourceClearedResid child↔parent extend needs the
  δ-transform applied to the CHILD-cleared input:
    sourceClearedResid(child) j u = foldResid(parent) j ( δ-transform( couplingClear_child u ) )
      [δ=1: δ-transform = blockBlowupCoordQuot(pivot)∘edgeShear;  δ=0: = stepMap]
  = sourceClearedResid(parent) j ( δ-transform( couplingClear_child u ) )   [couplingClear_parent is a no-op
    on the δ-transform of the cleared input, by CERT (i)].
  *** DESIGN SIGNAL: the form stated in ClearedFold.lean (:222 δ=1) has the δ-transform on RAW u
      (`edgeShear d ed u`), NOT the cleared input. That form is FALSE for case2/case12 FRESH clears —
      the fresh clear ADDS belowPivotCol(pivot) to couplingCoords(child), the fresh shear READS that coord,
      and couplingClear_parent (RHS) never clears it (it is child-only) ⟹ the coupling term survives on the
      RHS but is zeroed on the LHS. It happens to hold for case11 (shear = id, no fresh coupling). ***
"""
import sympy as sp, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, coreGen, Phi_p, canonNormalizationOf
from capstone_locus_core import couplingCoords, couplingClear

def edgeShear(u, d, ed):
    case, S, cl, piv, cen, delta = ed
    if case in ("case11", "rollover"):
        return dict(u)
    phi = canonNormalizationOf(u, d, S, cl, piv, True)
    return {k: u[k] + phi[k] for k in u}

def dtransform(u, d, ed):
    case, S, cl, piv, cen, delta = ed
    w = edgeShear(u, d, ed)
    if case == "rollover":
        return w
    if delta == 1:
        return {k: (sp.Integer(1) if k == piv else w[k]) for k in w}
    return {k: (w[piv] if k == piv else (w[piv] * w[k] if k in cen else w[k])) for k in w}

def srcResid(d, path, u, coords):
    return [sp.expand(f) for f in coreGen(Phi_p(couplingClear(d, path, u, coords), d, path, True), d)]

def cert_i(d):
    N, u = dims_coords(d); coords = set(u.keys()); edges, meta = oracle_edges(d)
    br = [e for e in edges if e[0] != "terminal"]; ok = True
    for i, ed in enumerate(br):
        case, S, cl, piv, cen, delta = ed
        if case in ("case11", "rollover"):
            continue
        v = couplingClear(d, br[:i + 1], u, coords)
        phi = canonNormalizationOf(v, d, S, cl, piv, True)
        for k in couplingCoords(d, br[:i], coords):
            if sp.expand(sp.sympify(phi.get(k, 0))) != 0:
                ok = False
    return ok

def cert_ii(d):
    """the CORRECTED extend (arg = δ-transform of couplingClear_child u) holds; report the stated RAW-u
    form's failures too."""
    N, u = dims_coords(d); coords = set(u.keys()); edges, meta = oracle_edges(d)
    br = [e for e in edges if e[0] != "terminal"]
    corrected_ok = True; raw_fails = []
    for i, ed in enumerate(br):
        if ed[0] == "rollover":
            continue
        parent = br[:i]; child = br[:i + 1]
        L = srcResid(d, child, u, coords)
        # corrected: δ-transform of couplingClear_child u
        argC = dtransform(couplingClear(d, child, u, coords), d, ed)
        RC = srcResid(d, parent, argC, coords)
        eqC = (len(L) == len(RC)) and all(sp.expand(L[j] - RC[j]) == 0 for j in range(min(len(L), len(RC))))
        corrected_ok &= eqC
        # stated RAW-u form
        argR = dtransform(u, d, ed)
        RR = srcResid(d, parent, argR, coords)
        eqR = (len(L) == len(RR)) and all(sp.expand(L[j] - RR[j]) == 0 for j in range(min(len(L), len(RR))))
        if not eqR:
            raw_fails.append((i, ed[0], ed[5]))
    return corrected_ok, raw_fails

def run():
    for d in [(2, 2, 2, 2), (3, 3, 2, 2), (2, 3, 3, 3)]:
        ci = cert_i(d)
        cc, rf = cert_ii(d)
        print(f"d={d}:")
        print(f"  CERT (i)  shear writes 0 at all ancestor couplings on cleared locus: {ci}")
        print(f"  CERT (ii) CORRECTED extend (δ-transform of couplingClear_child u) holds all edges: {cc}")
        print(f"            stated RAW-u extend FAILS at edges: {rf}  (case11 always holds; case2/12 fresh fail)")
        assert ci and cc

if __name__ == "__main__":
    run()
