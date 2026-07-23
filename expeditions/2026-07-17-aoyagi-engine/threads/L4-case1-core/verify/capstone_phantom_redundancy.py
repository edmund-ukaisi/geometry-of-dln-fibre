"""
#86(A) — PHANTOM-COVER-REDUNDANCY / THE (2′) GATE (pnp; elder §9.5). Is proving the phantom charts
REDUNDANT (droppable, so the counter-based oracle is salvageable without a def-edit) QUICK? The (2′) gate:
"not quick ⟹ the (1) fan-faithful def-edit is FORCED."

Phantom = a fan branch that RE-CLEARS a fan-cleared column (canonCenterOf is counter-based `cleared≤col<wMU`,
so an off-diagonal-COLUMN fan birth advances the counter without excluding the column, and a later FORCED
pivot lands on it). Aoyagi's D_1 (excludes the pivot's row AND column) forbids this — phantoms have no
Aoyagi source (#85 (1)-language).

TWO probes to characterize whether a quick redundancy argument exists:
 (1) is the phantom's RAW fold a valid (generically invertible) chart? If DEGENERATE (jacDet ≡ 0) it is
     trivially droppable (quick). If VALID (jacDet ≠ 0) it is a genuine chart of the blow-up cover, so
     dropping it needs a fan-cover-CONTAINMENT argument (image ⊆ ∪ other charts) — NOT quick.
 (2) on the CLEARED object (couplingClear precompose, where the resolution/RLCT is read per §7), does the
     phantom degenerate (foldB_cleared = 0)?
"""
import sympy as sp, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, coreGen
from capstone_locus_core import center_case2, couplingCoords, couplingClear
from capstone_stepinv_exists_q import foldG, foldB

def mk(d, pivs):
    return [("case2", 0, j, pivs[j], center_case2(d, 0, j), 1 if j == 0 else 0) for j in range(len(pivs))]

def probe(d, label, pivs, full_edges=None):
    N, u = dims_coords(d); coords = set(u.keys())
    br = mk(d, pivs)
    fg = foldG(u, d, br)
    fb_raw = sp.expand(foldB(u, d, br))
    L0 = [k for k in u if k[0] == 0]
    J = sp.Matrix([[sp.diff(sp.expand(fg[a]), u[b]) for b in L0] for a in L0])
    detJ = sp.expand(J.det())
    # cleared-object degeneracy (couplingClear on the FULL branch incl. later case11 merges, if given)
    branch = full_edges if full_edges else br
    clr = couplingClear(d, branch, u, coords)
    fb_cleared = sp.expand(foldB(clr, d, branch))
    print(f"[{label}] pivots={pivs}")
    print(f"   RAW jacDet(foldG|layer0) = {sp.factor(detJ) if detJ != 0 else 0}"
          f"  {'DEGENERATE' if detJ == 0 else 'VALID CHART (nonzero)'}")
    print(f"   foldB_cleared (full branch) = {fb_cleared}  {'<-- degenerate on cleared object' if fb_cleared == 0 else ''}")
    return detJ != 0

def run():
    d = (3, 3, 3)
    print("=" * 84)
    valid_canon = probe(d, "canonical (diagonal)", [(0, 0, 0), (0, 1, 1), (0, 2, 2)])
    valid_phantom = probe(d, "phantom [col2,col1,col2]", [(0, 0, 2), (0, 1, 1), (0, 2, 2)])
    print("\n" + "#" * 84)
    print("VERDICT (#86(A) — the (2′) gate):")
    print(f"  phantom RAW chart valid (nonzero Jacobian): {valid_phantom}")
    print("  ⟹ the phantom is a GENUINE raw coordinate chart of the blow-up (not trivially degenerate), so")
    print("    NO quick degeneracy dismissal exists. Dropping it needs a fan-cover CONTAINMENT argument")
    print("    (phantom image ⊆ ∪ non-phantom charts), which is resolution-cover geometry ENTANGLED with #81")
    print("    (is a degenerate-on-cleared chart a valid Resolution piece?). That is NOT quick.")
    print("  ⟹ (2′) GATE RESOLVES: not-quick ⟹ the (1) FAN-FAITHFUL DEF-EDIT is FORCED (canonCenterOf must")
    print("    exclude actually-cleared columns, per Aoyagi's D_1 row+col exclusion, so phantoms never arise).")
    print("    Matches #85's (1) = FIDELITY END-STATE; phantoms have no canonical source.")
    assert valid_phantom, "phantom raw chart is valid (nonzero Jacobian) — no quick degeneracy drop"

if __name__ == "__main__":
    run()
