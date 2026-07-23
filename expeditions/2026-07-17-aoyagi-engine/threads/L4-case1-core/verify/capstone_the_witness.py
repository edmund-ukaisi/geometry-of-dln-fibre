"""
THE WITNESS (#84 disambiguator / #85 phantom, team-lead commission). At a case11 MERGE that reuses a
divisor born at an OFF-DIAGONAL fan pivot: does the fold REALIGN the reused divisor to the diagonal
(⟹ e2=diagonal faithful, elder's SPLIT stands) or REUSE it at its STORED birth column (⟹ PURE-STORED,
and canonPivotOf/IsRealBranch's case11 pin implicated on fan-free branches — a MonumentAtlas finding)?

DEF FACT (DivBirthReach.lean:128): a case2/case12 birth does `Fin.snoc divBirthCoord (layer, cleared)`
— the birth coord is the COUNTER corner, so canonPivotOf(case11) = cornerToFlat(layer,cleared) = DIAGONAL,
independent of the fan pivot. So e2 = diagonal at the def level (REALIGNS). Open: is that FAITHFUL to the
fold (does the fold's off-diagonal-born divisor actually sit at the diagonal at the merge)?

Witness = (3,3,2,2), case11 @edge4 (e2=(0,1,1)) reuses the cleared1 divisor (birth center size 4 = fan).
Three variants for the cleared1 birth pivot (edge 1), everything else canonical incl. e2=(0,1,1):
  A canonical diagonal (0,1,1)            — baseline (birth col = merge col = 1)
  B ROW-off-diagonal  (0,2,1)             — col = merge col 1, NO below-coupling ⟹ no phantom collision;
                                            isolates the case11 row-faithfulness
  C COL-off-diagonal  (0,1,2)             — birth col 2 ≠ merge col 1; below-coupling (0,2,2) ⟹ #85 phantom
For each: the proper δ-aware cleared StepInv S1 under (i).

VERDICT: REALIGNS (e2=diagonal, def + foldB) — the δ=1 case11 merge places the divisor's foldB factor at
the diagonal, NOT at the δ=0 case2 birth's fan column; so the elder's §9.4 canonical-pin is the right frame
and PURE-STORED (e2=stored birth col) is NOT what the fold does. BUT raw S1 holds ONLY on the diagonal
branch — ANY off-diagonal fan birth (row B or col C) breaks raw S1 (birth≠merge coord), so the fan needs
the §9.4 canonical-frame TRANSPORT (the named L5 equivariance obligation). #85 refinement: option (2)
non-phantom-hypothesis is INSUFFICIENT (variant B is non-phantom yet fails).
"""
import sympy as sp, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, Phi_p, coreGen
from capstone_locus_core import couplingCoords, couplingClear
from capstone_stepinv_exists_q import foldG, foldB

def in_ideal(f, gens, allv):
    f = sp.expand(f)
    if f == 0: return True
    nz = [sp.expand(g) for g in gens if sp.expand(g) != 0]
    if not nz: return False
    return sp.expand(sp.groebner(nz, *allv, order='grevlex').reduce(f)[1]) == 0

def run_variant(d, edges, coords, u, allv, label, birth_pivot):
    br = [e for e in edges if e[0] != "terminal"]
    # locate the cleared1 birth edge (layer0, the 2nd case2) and override its pivot
    idx1 = [i for i, e in enumerate(br) if e[0] == "case2" and e[1] == 0][1]
    e1 = br[idx1]; br[idx1] = ("case2", e1[1], e1[2], birth_pivot, e1[4], e1[5])
    # the case11 that reuses cleared1 (e2 = diagonal (0,1,1), UNCHANGED — the def pins it there)
    c11idx = next(i for i, e in enumerate(br) if e[0] == "case11" and e[3] == (0, 1, 1))
    c11 = br[c11idx]
    child = br[:c11idx + 1]                                    # the sub-branch up to & incl. the case11 merge
    cc = couplingCoords(d, child, coords)
    clr = couplingClear(d, child, u, coords)                   # (i)-keyed source-clear
    # PROPER cleared StepInv (per capstone_cleared_stepinv): the δ-aware foldB/foldG on the cleared input
    FGc = [sp.expand(f) for f in coreGen(foldG(clr, d, child), d)]        # coreGen∘foldG_cleared
    Cj = [sp.expand(f) for f in coreGen(Phi_p(clr, d, child, True), d)]   # sourceClearedResid_j
    Bc = sp.expand(foldB(clr, d, child))                                 # foldB_cleared
    Bfac = list(Bc.free_symbols)
    divok = all(all(sp.expand(f.subs(g, 0)) == 0 for g in Bfac) for f in FGc) if Bfac else (Bc != 0)
    gens = [sp.expand(Bc * c) for c in Cj]
    memb = all(in_ideal(f, gens, allv) for f in FGc)
    dpv = all(sp.expand(f.subs({v: 0 for v in allv})) == 0 for f in FGc)
    s1 = (Bc != 0) and divok and memb and dpv
    print(f"\n[{label}] cleared1 birth pivot = {birth_pivot}; case11 e2 = {c11[3]} (diagonal)")
    print(f"  birth col {birth_pivot[2]} vs merge(e2) col {c11[3][2]}: "
          f"{'SAME' if birth_pivot[2]==c11[3][2] else 'DIFFER — merge at diagonal ≠ birth col'}")
    print(f"  couplingCoords(child) = {sorted(cc)}")
    print(f"  foldB_cleared = {Bc}  {'<-- VANISHES (#85 phantom)' if Bc == 0 else ''}")
    print(f"  divisibility(foldB_cleared | coreGen∘foldG_cleared): {divok};  "
          f"ideal-membership: {memb};  deepest-pt vanish: {dpv}")
    print(f"  ⟹ cleared StepInv S1 under (i): {s1}")
    return s1

def run():
    d = (3, 3, 2, 2)
    N, u = dims_coords(d); coords = set(u.keys()); allv = list(u.values())
    edges, meta = oracle_edges(d)
    print(f"d={d} canonical edges: {[(e[0], e[3]) for e in edges]}")
    sA = run_variant(d, edges, coords, u, allv, "A canonical", (0, 1, 1))
    sB = run_variant(d, edges, coords, u, allv, "B row-off-diag (no phantom)", (0, 2, 1))
    sC = run_variant(d, edges, coords, u, allv, "C col-off-diag (phantom)", (0, 1, 2))
    print("\n" + "#" * 90)
    print("VERDICT (THE WITNESS, #84/#85):")
    print(f"  A canonical (diagonal birth):        S1 = {sA}  (holds — the canonical frame)")
    print(f"  B row-off-diagonal (NON-phantom):    S1 = {sB}  (FAILS — no foldB-vanish, no re-clear)")
    print(f"  C col-off-diagonal (phantom #85):    S1 = {sC}  (FAILS)")
    print("  DEF FACT: e2 = canonPivotOf = cornerToFlat(divBirthCoord=(layer,cleared)) = DIAGONAL always")
    print("            (DivBirthReach.lean:128 snocs the COUNTER corner) ⟹ the merge REALIGNS to diagonal.")
    print("  FOLD FACT: the divisor's foldB factor is placed by the δ=1 case11 MERGE at the diagonal e2,")
    print("             NOT by the δ=0 case2 birth (fan pivot) ⟹ foldB is canonical-frame.")
    print("  CONSEQUENCE: raw S1 holds ONLY on the diagonal branch; ANY off-diagonal fan birth (row OR col)")
    print("             breaks raw S1 — the birth (fan pivot) and merge (diagonal) are different coords, so")
    print("             the raw fan branch is not self-consistent and needs the §9.4 canonical-frame TRANSPORT.")
    print("  #85 REFINEMENT: option (2) non-phantom-hypothesis is INSUFFICIENT — variant B is non-phantom yet")
    print("             fails; the resolution needs (1) fan-faithful def-edit OR (2′) canonical-pin transport.")
    assert sA, "canonical (diagonal) branch S1 must hold"
    assert not sB and not sC, "off-diagonal fan branches must fail raw S1 (transport-required) — the finding"

if __name__ == "__main__":
    run()
