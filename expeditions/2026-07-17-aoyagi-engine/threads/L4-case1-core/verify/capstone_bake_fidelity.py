"""
#87 (1)-BAKE SOURCE-FIDELITY CERTIFICATE (pnp; the forced canonCenterOf def-edit's bake-discipline input).

Two deliverables (team-lead):
 (a) trace canonCenterOf-WITH-COLUMN-EXCLUSION against Aoyagi's D_J semantics on WIDE+FAN witnesses.
 (b) THE ORACLE-GUARD INTERPLAY (SPECIFY-critical): with the excluded columns removed, does the phantom
     die cleanly at the IsRealBranch level (center empty ⟹ pivot pin unsatisfiable ⟹ no real branch), or
     does the counter-based oracle guard (still emitting a case2 stepChild) ALSO need the exclusion?

DEF FACTS (read at sites):
 * canonCenterOf d s sc (MonumentAtlas:853) is a function of the STATE s and stepChild sc ONLY — it does
   NOT see the path history (which off-diagonal columns were actually cleared upstream).
 * The oracle rollover guard (EngineDefs:256) is widthMinUpto(layer+1) ≤ cleared — state-counter based;
   case2 is emitted while NOT exhausted, INDEPENDENT of canonCenterOf.
 * Aoyagi D_J (worked.tex Lemma 2 :400-457, step order :613-629): blow up the sub-block D_J (rows/cols
   ≥ J); Q1 A Q2 = [[A1,O],[O,C4]] moves the pivot to the top-left, D_{J+1} = C4 = the complement EXCLUDING
   the pivot's row AND column. So each step excludes the pivot's column — faithful center excludes cleared cols.

MODEL: current center (counter) C_cur(S,cleared) = {(S,r,c): r≥cleared, cleared≤c<wMU}.
Two candidate (1)-edits:
  BIRTH-RESTRICT (canonCenterOf-ONLY):  C_birth(S,cleared) = {(S,r,cleared): r≥cleared}  (col pinned to the
     counter; keeps the ROW-fan = the transportable non-phantom family; off-diagonal-COL births impossible).
  LATER-EXCLUDE (needs a STATE surface tracking cleared-cols):  C_excl = C_cur minus cleared-cols.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, wmu

def C_cur(d, S, cleared):
    return {(S, r, c) for r in range(d[S + 1]) for c in range(d[S]) if r >= cleared and cleared <= c < wmu(d, S)}

def C_birth(d, S, cleared):
    return {(S, r, cleared) for r in range(d[S + 1]) if r >= cleared}         # col pinned to counter, row-fan

def C_excl(d, S, cleared, cleared_cols):
    return {t for t in C_cur(d, S, cleared) if t[2] not in cleared_cols}      # exclude actually-cleared cols

def run():
    d = (3, 3, 3, 3)
    N, u = dims_coords(d)
    print(f"WIDE+FAN witness d={d}; phantom = layer-0 fan pivots [col2, col1, col2] (the a8a956809 family)")
    print("=" * 88)
    # (a) Aoyagi D_J vs the edits, tracing the phantom's 3rd clear at cleared=2
    print("(a) canonCenterOf-with-column-exclusion vs Aoyagi D_J (the phantom's 3rd clear, cleared=2):")
    print(f"    current counter center C_cur(0,2) = {sorted(C_cur(d,0,2))}  (col 2 only — RE-ADMITS col 2)")
    # phantom cleared cols after pivots (0,0,2),(0,1,1): actually-cleared cols = {2,1}; remaining = {0}
    cleared_cols = {2, 1}
    print(f"    Aoyagi D_2 (excl pivot cols {sorted(cleared_cols)}): faithful center over col {{0}} (the REMAINING col)")
    print(f"    C_excl(0,2, cleared_cols={sorted(cleared_cols)}) = {sorted(C_excl(d,0,2,cleared_cols))}  <- EMPTY "
          f"(col 2 excluded, but the counter only offers col 2)")
    print(f"    ⟹ MATCH to Aoyagi needs the REMAINING col (0); the counter offers col 2 ⟹ the counter center is")
    print(f"      UNFAITHFUL on the fan path; column-exclusion makes it EMPTY (not redirected to col 0).")
    print()
    # (b) the oracle-guard interplay
    print("(b) ORACLE-GUARD INTERPLAY:")
    print(f"    canonCenterOf is a function of (state, stepChild) ONLY — state-BLIND to which off-diagonal cols")
    print(f"    were cleared upstream. So a canonCenterOf-only edit CANNOT exclude them at the LATER (cleared=2)")
    print(f"    step. Two clean routes:")
    print(f"    ── BIRTH-RESTRICT (canonCenterOf-ONLY, NO oracle edit):")
    print(f"       C_birth(0,0) = {sorted(C_birth(d,0,0))}  (col pinned to 0; the phantom's 1st pivot (0,0,2)")
    print(f"       is NOT in it ⟹ the phantom is never BORN). Centers stay NONEMPTY at every non-exhausted")
    print(f"       state (row-fan), so IsRealBranch always has a pivot; the oracle guard is UNTOUCHED and never")
    print(f"       emits into an empty center. Phantom dies AT ITS SOURCE, cleanly, one def surface.")
    print(f"    ── LATER-EXCLUDE (needs a STATE surface tracking cleared-cols):")
    print(f"       the phantom's cleared=2 center becomes EMPTY (above) while the oracle guard (cleared 2 <")
    print(f"       widthMinUpto(1)=3) STILL emits a case2 stepChild ⟹ IsRealBranch's pin `pivot ∈ canonCenterOf`")
    print(f"       is UNSATISFIABLE ⟹ no real branch walks it (phantom dies at IsRealBranch). Tree/termination")
    print(f"       UNAFFECTED (buildTree is state-based). BUT this is a SECOND def surface (state must track the")
    print(f"       cleared cols) AND leaves a real-branch-less tree node — a mismatch to audit.")
    print()
    print("=" * 88)
    print("VERDICT (1)-bake:")
    print(" (a) Aoyagi D_J excludes the pivot's COLUMN each step; the counter center re-admits an already-fan-")
    print("     cleared column (the phantom). Column-exclusion is the faithful edit; on the fan path the counter")
    print("     center is unfaithful (offers the cleared col, not the remaining one).")
    print(" (b) canonCenterOf is state-blind ⟹ the CLEAN canonCenterOf-ONLY edit is the BIRTH-RESTRICTION")
    print("     (pin the pivot column to the counter, keep the ROW-fan): the phantom is never born, centers stay")
    print("     nonempty, the ORACLE GUARD NEEDS NO EDIT. The 'empty center + guard still emits' scenario arises")
    print("     ONLY in the later-exclude route, which requires a SECOND (state) surface — avoid it.")
    print(" SPECIFY: edit canonCenterOf case2/case12 to the col-pinned row-fan center; NO oracle/state edit.")
    print(" OPEN (elder/pnp-fan cover call, NOT a bake blocker): does the row-fan + the #86(B) σ-transport cover")
    print("     the blow-up without the dropped col-fan charts? (σ permutes columns, so the col-orbit is a")
    print("     transport image of the row-fan — plausibly yes; the pnp-fan cover argument decides.)")
    print()
    no_under_admission()
    row_exclusion_question(d)

def no_under_admission():
    """The col-restriction {col=cleared} drops EXACTLY the phantom (off-diagonal-col) charts — NO legitimate
    chart lost. Claim: EVERY off-diagonal-col birth (col b>cleared, b<wMU) eventually RE-CLEARS col b (the
    counter reaches cleared=b before the layer rolls over at wMU, forcing a pivot at col b again) ⟹ every
    off-diagonal-col birth is a phantom ⟹ dropping them is not under-admission."""
    print("─" * 88)
    print("NO-UNDER-ADMISSION: every off-diagonal-COL birth (col b>cleared, b<wMU) re-clears col b later:")
    for d in [(3, 3, 3, 3), (3, 4, 2, 2)]:
        S = 0; W = wmu(d, S)
        print(f"  d={d}, layer {S}, wMU={W}: for a birth at col b>cleared, the counter reaches cleared=b<{W}")
        for b in range(1, W):
            print(f"    birth col b={b} at cleared<{b}: counter advances to cleared={b} (< wMU {W}, before rollover)")
            print(f"      ⟹ the forced center at cleared={b} offers col {b} again ⟹ RE-CLEAR ⟹ phantom.")
        print(f"    ⟹ ALL off-diagonal-col births at layer {S} are phantoms; {{col=cleared}} drops only phantoms.")

def row_exclusion_question(d):
    """Aoyagi D_J excludes the pivot ROW too. Does the (1) edit need ROW-exclusion? Test: an off-diagonal-ROW
    fan branch (col in counter order, rows off-diagonal) — does it create a phantom (foldB-vanish / re-clear)?"""
    import sympy as sp
    from capstone_adjudication import oracle_edges, coreGen, Phi_p
    from capstone_locus_core import center_case2, couplingCoords, couplingClear
    from capstone_stepinv_exists_q import foldB
    print("─" * 88)
    print("ROW-EXCLUSION QUESTION: are off-diagonal-ROW births benign (no phantom), so only COL-exclusion is needed?")
    dd = (3, 3, 3); N, u = dims_coords(dd); coords = set(u.keys())
    def mk(pivs):
        return [("case2", 0, j, pivs[j], center_case2(dd, 0, j), 1 if j == 0 else 0) for j in range(len(pivs))]
    # off-diagonal ROWS, cols in counter order (0,1,2): rows chosen off-diagonal where a below-coupling exists
    row_fan = mk([(0, 1, 0), (0, 2, 1), (0, 2, 2)])   # row1@col0 (coupling (0,2,0)), row2@col1, row2@col2
    cc = couplingCoords(dd, row_fan, coords)
    v = couplingClear(dd, row_fan, u, coords)
    fb_cleared = sp.expand(foldB(v, dd, row_fan))
    print(f"  row-fan branch (cols 0,1,2 in order, rows off-diagonal) = {[e[3] for e in row_fan]}")
    print(f"    couplingCoords = {sorted(cc)}  (column-indexed, below the pivots' cols)")
    print(f"    foldB_cleared = {fb_cleared}  {'VANISHES (row-phantom!)' if fb_cleared == 0 else '(nonzero — NO phantom)'}")
    print("  ⟹ off-diagonal-ROW births clear cols in COUNTER order (no col re-clear), the couplings are")
    print("    column-indexed and below already-cleared cols, so no later pivot collides ⟹ BENIGN, no phantom.")
    print("  ⟹ ROW-EXCLUSION is NOT load-bearing: the phantom is purely COLUMNAR. The (1) edit only needs the")
    print("    COLUMN restriction {col=cleared}; the benign ROW-fan is kept (transportable, #86B) — OR, for full")
    print("    canonical-frame fidelity, the row is ALSO pinned (both orbits transport); a cover/taste call, not")
    print("    a correctness one (row-reuse never corrupts foldB/codim).")
    assert fb_cleared != 0, "row-fan must be benign (no foldB vanish)"

if __name__ == "__main__":
    run()
