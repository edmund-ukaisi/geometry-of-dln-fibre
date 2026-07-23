"""
#86(C) — LABELED-JAC PRESERVATION (§9.6, codim-load-bearing; pnp). The codim is read from the fold's
labeled Jacobian exponents (jacWeight = the block monomial ∏ coord^exp). (C) checks: under the per-step
reindex σ (#86(B)), the TRANSPORTED fan chart's labeled-jac EXPONENTS equal the canonical chart's — so the
codim is transport-invariant. Covers BOTH birth sub-species (team-lead's settled split):
  * δ=1-born off-diagonal (cleared=0 fan pivot): foldB carries the fan factor at the FAN column (the
    double-carry) — the jac exponent lands at the fan coord, must σ-realign to the diagonal.
  * δ=0-born off-diagonal (cleared≥1 fan pivot): no foldB factor; blockBlowupMap SCALES center coords by
    u_fan — the scaling coord must σ-realign.
CORRUPTION (exponent multiset changes, or a coord fails to σ-realign) ⟹ (2′) fails at the codim ⟹ (1)-FULL
[BOTH counter-site def-edits: canonCenterOf column-exclusion + divBirthCoord]. PRESERVED ⟹ (1)-ALONE suffices.

σ = the intermediate/boundary-space basis permutation that maps each fan pivot's off-diagonal index to the
cleared (diagonal) index; it acts on jac coords by relabeling. Check: multiset of (exponent) over σ-images
of the fan jac == multiset over the canonical jac, coord-for-coord.
"""
import sympy as sp, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, coreGen
from capstone_locus_core import center_case2
from capstone_stepinv_exists_q import foldG

def mk(d, pivs):
    return [("case2", 0, j, pivs[j], center_case2(d, 0, j), 1 if j == 0 else 0) for j in range(len(pivs))]

def jac_exponents(d, br):
    """the labeled-jac = the exponent vector of jacDet(foldG) as a monomial in the layer-0 coords."""
    N, u = dims_coords(d)
    fg = foldG(u, d, br)
    L0 = [k for k in u if k[0] == 0]
    J = sp.Matrix([[sp.diff(sp.expand(fg[a]), u[b]) for b in L0] for a in L0])
    detJ = sp.factor(sp.expand(J.det()))
    # extract exponents: detJ is a monomial ± c·∏ u_k^e_k
    poly = sp.Poly(detJ, *[u[k] for k in L0])
    if len(poly.monoms()) != 1:
        return None, detJ                       # not a pure monomial — flag
    exps = {L0[i]: e for i, e in enumerate(poly.monoms()[0]) if e > 0}
    return exps, detJ

def sigma_col(d, layer, i, j):
    """σ on the layer-`layer` block COLUMN indices (the d[layer] space): swap col i<->j. Acts on a coord
    (layer,r,c) by swapping c∈{i,j}. (Used to realign a δ=1 fan pivot col to the diagonal.)"""
    def s(coord):
        (L, r, c) = coord
        if L == layer:
            c = j if c == i else (i if c == j else c)
        return (L, r, c)
    return s

def sigma_row(d, layer, i, j):
    """σ on the layer-`layer` block ROW indices (the d[layer+1] space): swap row i<->j."""
    def s(coord):
        (L, r, c) = coord
        if L == layer:
            r = j if r == i else (i if r == j else r)
        return (L, r, c)
    return s

def check(d, label, fan_pivs, sigma):
    canon = mk(d, [(0, k, k) for k in range(len(fan_pivs))])
    fan = mk(d, fan_pivs)
    ec, dc = jac_exponents(d, canon)
    ef, df = jac_exponents(d, fan)
    if ec is None or ef is None:
        print(f"[{label}] NON-MONOMIAL jacDet (canon={dc}, fan={df}) — flag"); return False
    # transport the fan exponents by σ
    ef_sigma = {sigma(k): e for k, e in ef.items()}
    match = (ef_sigma == ec)
    print(f"[{label}] fan pivots={fan_pivs}")
    print(f"   canonical jac exps      = {dict(sorted(ec.items()))}")
    print(f"   fan jac exps            = {dict(sorted(ef.items()))}")
    print(f"   σ(fan) jac exps         = {dict(sorted(ef_sigma.items()))}")
    print(f"   exponent MULTISET preserved: {sorted(ef.values()) == sorted(ec.values())};  "
          f"σ-aligned to canonical: {match}")
    return match

def run():
    d = (3, 3, 3)
    print("=" * 84)
    # δ=1-born off-diagonal: first pivot col 2 (cleared0, δ=1) — σ swaps d[0] cols 0<->2
    ok1 = check(d, "δ=1-born col-off-diag", [(0, 0, 2), (0, 1, 1), (0, 2, 2)], sigma_col(d, 0, 0, 2))
    # δ=0-born off-diagonal: second pivot row 2 (cleared1, δ=0) — σ swaps d[1] rows 1<->2 (rows of A_0)
    ok2 = check(d, "δ=0-born row-off-diag", [(0, 0, 0), (0, 2, 1), (0, 2, 2)], sigma_row(d, 0, 1, 2))
    print("\n" + "#" * 84)
    print(f"VERDICT (#86(C) labeled-jac preservation):")
    print(f"  δ=1-born (foldB fan-factor double-carry): exps σ-preserved = {ok1}")
    print(f"  δ=0-born (scaling-only mismatch):         exps σ-preserved = {ok2}")
    print(f"  ⟹ labeled-jac (codim data) TRANSPORT-INVARIANT under the per-step σ: {ok1 and ok2}")
    print("  PRESERVED ⟹ (2′) does NOT fail at the codim ⟹ (1)-ALONE (canonCenterOf column-exclusion)")
    print("  suffices; divBirthCoord's counter-recording is the her-frame TARGET, not a second defect.")
    assert ok1 and ok2, "labeled-jac exponents must be σ-preserved (else (1)-FULL forced)"

if __name__ == "__main__":
    run()
