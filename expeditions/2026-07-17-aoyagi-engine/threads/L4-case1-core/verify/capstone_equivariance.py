"""
#86(B) — THE §9.4 EQUIVARIANCE CHECK (pnp; elder §9.5 / #84 canonical-pin transport). Does a non-phantom
fan chart TRANSPORT to the canonical chart under the per-step Q,P reindex, so raw-S1 (canonical only)
carries to the fan? THE WITNESS proved no GLOBAL permutation works (birth-merge mismatch intrinsic), so
the transport must be the PER-STEP intermediate-space basis permutation σ. Two decisive facts imply it:

 (i)  coreGen is INVARIANT under σ = an intermediate-space basis permutation (swap two basis vectors of the
      d[k] space, 0<k<N): A_{k-1} → P·A_{k-1}, A_k → A_k·P⁻¹, so the product ∏A is unchanged (P⁻¹P=id).
      This is the DLN gauge symmetry restricted to a permutation subgroup.
 (ii) the CLEAR operation is σ-EQUIVARIANT: the fan clear at an off-diagonal pivot equals the canonical
      (diagonal) clear conjugated by the σ that swaps the pivot's row to the cleared row —
      σ⁻¹ ∘ (clear at diagonal) ∘ σ = (clear at fan pivot). The exceptional coord (the δ=0 blockBlowupMap
      scaling by u_pivot) is carried by σ to the diagonal (the "double-carry").

(i)+(ii) ⟹ the per-step reindex takes the fan branch to the canonical branch coordinate-for-coordinate,
coreGen sees the same value, so sourceClearedResid and S1 transport. FAILURE of either ⟹ re-open FAN-CARRIED.
"""
import sympy as sp, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, coreGen, apply_edge, canonNormalizationOf

def perm_basis(d, u, k, i, j):
    """σ: swap basis vectors i,j of the d[k] space (0<k<N). A_{k-1} rows i↔j (rows index d[k]); A_k cols
    i↔j (cols index d[k]). Returns (σ·u): (σ·u)[coord] = u[σ⁻¹ coord]; a transposition is its own inverse."""
    def sw(t):
        (L, r, c) = t
        if L == k - 1:                       # A_{k-1}: rows index d[k]
            r = j if r == i else (i if r == j else r)
        if L == k:                           # A_k: cols index d[k]
            c = j if c == i else (i if c == j else c)
        return (L, r, c)
    return {t: u[sw(t)] for t in u}

def check_coreGen_invariance(d):
    N, u = dims_coords(d)
    ok = True
    for k in range(1, N):                    # intermediate spaces d[1..N-1]
        if d[k] < 2:
            continue
        su = perm_basis(d, u, k, 0, 1)        # swap basis 0,1 of the d[k] space
        lhs = [sp.expand(f) for f in coreGen(su, d)]
        rhs = [sp.expand(f) for f in coreGen(u, d)]
        inv = (lhs == rhs)
        print(f"  coreGen invariant under σ (swap d[{k}] basis 0,1): {inv}")
        ok &= inv
    return ok

def check_clear_equivariance(d, S, cleared, fan_pivot):
    """(ii): σ⁻¹ ∘ clear_canon ∘ σ = clear_fan, where σ swaps the fan pivot's ROW to the cleared row in the
    d[S+1] space (rows of A_S). Test on the shear+δ=1 clear at layer S."""
    N, u = dims_coords(d)
    a_fan, b = fan_pivot[1], fan_pivot[2]
    diag = (S, cleared, cleared)
    # σ acts on the d[S+1] space: A_S rows (index d[S+1]) swap cleared↔a_fan; A_{S+1} cols swap cleared↔a_fan.
    def sigma(w):
        return perm_basis(d, w, S + 1, cleared, a_fan)
    # clear op: shear canonNormalizationOf(pivot) then blockBlowupCoordQuot(pivot) (δ=1)
    def clear(w, piv):
        phi = canonNormalizationOf(w, d, S, cleared, piv, True)
        sh = {t: w[t] + phi[t] for t in w}
        return {t: (sp.Integer(1) if t == piv else sh[t]) for t in w}
    # but the fan pivot's COLUMN must also map to the diagonal for a clean conjugation; here b may ≠ cleared.
    # Use a fan pivot with b == cleared (ROW-only off-diagonal, the non-phantom family) so σ (a row swap) alone
    # conjugates.  fan_pivot = (S, a_fan, cleared).
    lhs = sigma(clear(sigma(u), diag))        # σ⁻¹ ∘ clear_canon ∘ σ  (σ is an involution ⟹ σ⁻¹=σ)
    rhs = clear(u, fan_pivot)                 # clear_fan
    eq = all(sp.expand(sp.sympify(lhs[t]) - sp.sympify(rhs[t])) == 0 for t in u)
    print(f"  clear σ-equivariant (σ⁻¹∘clear_diag∘σ = clear_fan) at layer {S}, "
          f"fan pivot {fan_pivot} (row {a_fan}→cleared {cleared}): {eq}")
    return eq

def run():
    print("=" * 84)
    print("(i) coreGen σ-invariance (the DLN intermediate-basis permutation symmetry):")
    inv22 = check_coreGen_invariance((3, 3, 2, 2))
    inv333 = check_coreGen_invariance((2, 3, 3, 3))
    print("\n(ii) clear σ-equivariance (row-off-diagonal fan pivot, the non-phantom family):")
    eqA = check_clear_equivariance((3, 3, 2, 2), 0, 1, (0, 2, 1))   # fan pivot row 2 → cleared 1, col 1
    eqB = check_clear_equivariance((2, 3, 3, 3), 0, 1, (0, 2, 1))
    print("\n" + "#" * 84)
    verdict = inv22 and inv333 and eqA and eqB
    print(f"(i) coreGen σ-invariant: {inv22 and inv333}")
    print(f"(ii) clear σ-equivariant: {eqA and eqB}")
    print(f"⟹ per-step reindex TRANSPORTS the fan chart to canonical (S1 carries): {verdict}")
    print("  (i)+(ii): σ is an intermediate-basis permutation that (a) leaves coreGen fixed and (b) conjugates")
    print("  the diagonal clear to the fan clear, carrying the exceptional coord to the diagonal. So the")
    print("  fan branch = canonical branch after per-step σ; sourceClearedResid & S1 transport. No FAN-CARRIED.")
    assert verdict, "equivariance must hold — else re-open FAN-CARRIED"

if __name__ == "__main__":
    run()
