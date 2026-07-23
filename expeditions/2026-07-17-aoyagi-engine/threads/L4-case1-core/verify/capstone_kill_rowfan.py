"""
#92 (V3) CONSULT + KILL-BREAKER (pnp). Two findings for seat-KILL:

(V3) STRUCTURE on DIAGONAL-pivot branches: the escaped-coeff vanishing on cleared inputs is TRIVIAL
termwise — every monomial of the escaped coefficient carries a couplingCoords factor, so couplingClear
zeros it term-by-term. NOT a cancellation, NOT a Q₁⁻¹ absorption identity. (seat-KILL's "direct (a)
non-coupling term" — on a diagonal branch that entry, e.g. A_0 row-2 col-1 = (0,2,1), IS itself a coupling:
the below-column of the diagonal (0,1,1)-clear. So there is no surviving coupling-free term to cancel.)
⟹ the render on DIAGONAL branches is a simple "each escaped-coeff monomial has a coupling factor,
couplingClear ↦ 0" — no Q₁⁻¹ machinery.

*** KILL-BREAKER: the KILL is FALSE on post-#87 ROW-FAN branches. *** #87 pinned only pivot.col=cleared
(row FREE). A branch may then REPEAT a pivot row (a ROW-phantom — Aoyagi's D_J excludes the pivot ROW AND
col; #87's col-pin gives column-completeness but not row-completeness). Witness (2,3,3,3), layer-0 pivots
(0,2,0),(0,2,1) [both row 2]: belowPivotCol(row-2 pivot) = ∅ ⟹ couplingCoords = ∅ ⟹ couplingClear = id ⟹
sourceClearedResid = raw foldResid reads the escaped columns (coeff u_(2,0,0), a pure layer-2 coord, NO
coupling). The KILL FAILS. NO couplingCoords variant rescues it (below / r≠a / diagonal-below all tested):
the diagonal-below rule rescues SINGLE-off-diagonal rows (1,2)/(0,2) but NOT the repeated row (2,2) — the
fold with row-repeated pivots genuinely produces a coupling-free escaped coefficient.

⟹ seat-KILL cannot render the KILL at ∀ IsRealBranch (post-#87). ESCALATION: the KILL needs the pivot ROW
pinned to the diagonal too — the (1) def-edit must be the FULL DIAGONAL PIN (pivot = (S,cleared,cleared)),
correcting #87's col-only ROW-FAN pin. This makes the coverage rider LOAD-BEARING (diagonal charts + the
#86 transport must cover; pnp-fan #11-14 arbiter).
"""
import sympy as sp, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, coreGen, Phi_p
from capstone_kill_invariant import escaped

def run():
    d = (2, 3, 3, 3); N, u = dims_coords(d); coords = set(u.keys())
    edges, meta = oracle_edges(d); br = [e for e in edges if e[0] != "terminal"]

    def rowfan(rows):
        b = [e for e in br]; idxs = [i for i, e in enumerate(b) if e[0] == "case2" and e[1] == 0]
        for k, i in enumerate(idxs):
            cl = b[i][2]; b[i] = ("case2", 0, cl, (0, rows[k], cl), b[i][4], b[i][5])   # col=cleared (post-#87), row free
        return b

    def couplings(b, rule):
        cc = set()
        for e in b:
            if e[0] not in ("case2", "case12"):
                continue
            L, a, col = e[3]; cl = e[2]
            for r in range(d[L + 1]):
                if rule == 'below' and r > a: cc.add((L, r, col))       # belowPivotCol (current #82/#87 def)
                if rule == 'colall' and r != a: cc.add((L, r, col))      # full uncleared pivot column
                if rule == 'diag' and r > cl: cc.add((L, r, col))        # below the DIAGONAL (full-diag-pin equiv)
        return cc

    def kill(b, rule):
        idxs = [i for i, e in enumerate(b) if e[0] == "case2" and e[1] == 0]; path = b[:idxs[-1] + 1]
        cc = couplings(path, rule)
        clr = {k: (sp.Integer(0) if k in cc else u[k]) for k in u}
        res = [sp.expand(f) for f in coreGen(Phi_p(clr, d, path, True), d)]
        return not any(u[e] in f.free_symbols for f in res for e in escaped(d, 1))

    print(f"d={d}  KILL(sourceClearedResid ignores escaped(layer 1)) per layer-0 pivot ROWS, couplingCoords rule:")
    results = {}
    for rows in [(0, 1), (1, 2), (0, 2), (2, 2)]:
        b = rowfan(rows)
        row = {rule: kill(b, rule) for rule in ['below', 'colall', 'diag']}
        results[rows] = row
        tag = "DIAGONAL" if rows == (0, 1) else ("ROW-PHANTOM (repeated row)" if rows == (2, 2) else "row-fan")
        print(f"  pivots row={rows} [{tag}]: below={row['below']}  colall={row['colall']}  diag={row['diag']}")
    diag_only_ok = all(results[(0, 1)].values())
    rowfan_breaks = not results[(2, 2)]['below'] and not results[(2, 2)]['diag']
    print(f"\n  diagonal branch: KILL holds under the current def: {diag_only_ok}")
    print(f"  ROW-PHANTOM (2,2): KILL FAILS under EVERY couplingCoords variant: {rowfan_breaks}")
    print("  ⟹ the KILL needs the pivot ROW pinned to the diagonal (FULL DIAGONAL PIN), correcting #87's")
    print("    col-only ROW-FAN; on diagonal branches (V3) is trivial termwise (no Q₁⁻¹).")
    assert diag_only_ok and rowfan_breaks

if __name__ == "__main__":
    run()
