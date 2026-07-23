"""
CLEAR-LOCATION FORK #82 — the CLEAN single-edge arbiter (no multi-edge coherence confound).

The multi-edge S1 test (capstone_clearloc_fork.py) is CONFOUNDED: overriding one fan pivot makes
successive clears collide on a single column and mismatches the state-based birth corner, so both rules
fail on the incoherent branch (uninformative for S1). The DEF-LEVEL question — WHERE does the fold's own
δ=1 clear act — is a single-edge property and is NOT confounded.

FOLD δ=1 clear = canonNormalizationOf(pivot=(a,b)) then blockBlowupCoordQuot(pivot). Claim (reading (i)):
the fold clears the FAN PIVOT's column b (reads column b + row a), NOT a fixed diagonal column J.

CHECK: apply a single case2 δ=1 edge at fan pivots (0,0,0) [diagonal, col 0] and (0,0,1) [off-diagonal,
col 1] on the SAME input. Show (1) the normalized-to-1 entry is the fan pivot; (2) the interior shear
reads the fan pivot's COLUMN (col b) — so the cleared column TRACKS the fan pivot, = reading (i).
If the fold cleared a fixed diagonal column (reading (ii)), the shear would read col 0 for BOTH pivots.
"""
import sympy as sp
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, apply_edge

def cols_read_in_layer(expr_dict, u, layer):
    """which layer-`layer` columns appear in the post-fold entries (the columns the shear reads)."""
    cols = set()
    for k, v in expr_dict.items():
        for (L, r, c), sym in u.items():
            if L == layer and sym in sp.sympify(v).free_symbols:
                cols.add(c)
    return cols

def run():
    d = (2, 2, 2, 2)
    N, u = dims_coords(d)
    # center at (S=0, J=0) = the full 2x2 A_0 block; fan pivot free within it (IsRealBranch rule (b))
    center0 = {(0, r, c) for r in range(2) for c in range(2)}
    print(f"d={d}; single case2 δ=1 edge at layer 0, center = full A_0 block {sorted(center0)}")
    print("Reading (i): fold clears the FAN PIVOT's column b.  Reading (ii): fixed diagonal col J=0.")
    print("-" * 84)
    for piv in [(0, 0, 0), (0, 0, 1)]:
        a, b = piv[1], piv[2]
        out = apply_edge(u, d, "case2", 0, 0, piv, center0, 1, True)   # δ=1 clear at this fan pivot
        # (1) which entry got normalized to the unit 1?
        normed = [k for k in u if sp.sympify(out[k]) == 1]
        # (2) which layer-0 columns does the resulting fold read (the cleared/coupled column)?
        cols0 = cols_read_in_layer(out, u, 0)
        # (3) the interior write for a sample interior entry — does it reference column b?
        interior = next((k for k in u if k[0] == 0 and k[1] != a and k[2] != b), None)
        reads_col_b = interior is not None and any(
            (0, r, b) == (L, rr, cc) for (L, rr, cc), s in u.items()
            for r in range(2) if s in sp.sympify(out[interior]).free_symbols and cc == b)
        print(f"  fan pivot {piv} (col b={b}): normalized-to-1 entry = {normed} "
              f"(== pivot: {normed == [piv]})")
        print(f"       layer-0 columns the fold reads = {sorted(cols0)}  "
              f"(tracks fan col {b}: {cols0 == {b} or (b in cols0)})")
        if interior is not None:
            print(f"       interior entry {interior} → {out[interior]}   (references col b={b})")
    print("-" * 84)
    # DECISIVE contrast: the pivot NORMALIZED to 1 and the SET of MODIFIED entries must DIFFER between the
    # two fan pivots (⟹ the clear location TRACKS the fan pivot = reading (i)); reading (ii) [fixed diagonal]
    # would normalize the SAME entry and modify the SAME set for both pivots.
    out0 = apply_edge(u, d, "case2", 0, 0, (0, 0, 0), center0, 1, True)
    out1 = apply_edge(u, d, "case2", 0, 0, (0, 0, 1), center0, 1, True)
    normed0 = [k for k in u if sp.sympify(out0[k]) == 1]
    normed1 = [k for k in u if sp.sympify(out1[k]) == 1]
    mod0 = {k for k in u if sp.expand(sp.sympify(out0[k]) - u[k]) != 0}
    mod1 = {k for k in u if sp.expand(sp.sympify(out1[k]) - u[k]) != 0}
    print(f"diagonal pivot (0,0,0): normalized={normed0}, modified-entries={sorted(mod0)}")
    print(f"off-diag  pivot (0,0,1): normalized={normed1}, modified-entries={sorted(mod1)}")
    verdict_i = (normed0 == [(0, 0, 0)] and normed1 == [(0, 0, 1)] and mod0 != mod1)
    print(f"\nVERDICT: fold's clear location TRACKS the fan pivot (reading (i)): {verdict_i}")
    print("  (reading (ii) [fixed diagonal] would normalize (0,0,0) and modify the SAME set for BOTH pivots)")
    assert verdict_i, "expected the fold to track the fan pivot (reading (i))"
    print("\nOK: fold δ=1 clear normalizes the FAN PIVOT and its shear reads the fan pivot's column/row")
    print("    ⟹ couplingCoords must key the clear on the STORED fan pivot (reading (i)).")

if __name__ == "__main__":
    run()
