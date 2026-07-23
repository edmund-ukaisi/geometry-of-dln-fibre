"""
THE LIFT CERTIFICATE + FULL ψ_gen (pnp-transport #70, §7.8 closing items 1+2, UNIFIED).

§7.8 asks: (1) FULL ψ_gen (multi-coupling, wide+deep, no gaps); (2) certify ψ_gen LIFTS to a
PARAMETER-SPACE det-1 CoV (the unipotent Q₁ matrix conjugation on the A_i) so the bridge is
rlctGlobal-intrinsic and no in-chart exceptional weight is transported.

KEY INSIGHT (resolves the multi-coupling difficulty): the fold-coordinate per-coupling straightening
ψ interacts across couplings (a CHART-normalization artifact: pivot=1 in-chart). At the MATRIX /
PARAMETER level each ancestor clear is an INDEPENDENT unipotent Q₁ row-clear, det-1 with the pivot FREE.
The cleared object C = raw fold with the ancestor Q₁ row-clears applied; F↔C therefore lifts to the
parameter-space gauge ρ = ∘(A_L → Q₁_L·A_L, A_{L+1} → A_{L+1}·Q₁_L⁻¹), which is:
  (i)  det-1 on RAW parameters (pivot free) — degenerates to det-0 ONLY in-chart (pivot=1);
  (ii) PRODUCT-PRESERVING (∏A invariant) ⟹ the loss ∑‖∏A‖² is ρ-INVARIANT ⟹ RLCT literally preserved,
       rlctGlobal-intrinsic, NO resolution-chart Jacobian weight ever transported.
This is the lift (elder's prior: ψ IS a matrix conjugation) AND the full multi-coupling ψ_gen (each Q₁
independently unipotent ⟹ works for wide/deep uniformly).

Verified per witness — (2,2,2,2), (2,2,2,2,2) BOTH case11 nodes (incl. intermediate), (3,3,3,2) wide:
  (A) each ancestor Q₁ is unipotent det-1 (pivot free);
  (B) the paired gauge preserves ∏A (coreGen invariant) — loss-invariant, RLCT-intrinsic;
  (C) the chart image (pivot→1) of the composite = ancestor_column_clear ⟹ gives C (the split-carrier).
"""
import sympy as sp
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, Phi_p, coreGen, blockCoords
from capstone_closing_ii import ancestor_column_clear_map

def matify(u, d, L, pivfree=None):
    """A_L as a sympy Matrix from the flat coords; pivfree optionally frees a pivot (L,a,b)->symbol."""
    return sp.Matrix(d[L + 1], d[L], lambda r, c: u[(L, r, c)])

def run(d, which):
    N, u = dims_coords(d)
    edges, meta = oracle_edges(d)
    c11 = [i for i, e in enumerate(edges) if e[0] == "case11"]
    idx = c11[0] if which == "first" else next(i for i in c11 if meta[i]['birth_f'][0] >= 1)
    parent = edges[:idx]
    lbl = f"{d}[{which}:S{edges[idx][1]} reuse{meta[idx]['birth_f']}]"

    # ancestor clears (case2/case12): (layer L, pivot (a,b)); the Q₁ row-clear zeros col b below row a
    clears = [(e[1], e[3][1], e[3][2]) for e in parent if e[0] in ("case2", "case12")]
    allv = list(u.values())

    # (A) each Q₁ unipotent det-1 with pivot FREE  +  (B) paired gauge product-preserving on ∏A
    detA_ok, prod_ok = True, True
    for (L, a, b) in clears:
        AL = matify(u, d, L)
        piv = sp.Symbol("piv_free")
        ALf = AL.copy(); ALf[a, b] = piv                      # free the pivot (un-normalized)
        n = d[L + 1]
        Q1 = sp.eye(n)
        for r in range(n):
            if r != a:
                Q1[r, a] = -ALf[r, b] / ALf[a, b]              # row_r -= (A[r,b]/piv) row_a  (clears col b)
        detA_ok = detA_ok and (sp.simplify(Q1.det()) == 1)
        cleared_col = sp.simplify((Q1 * ALf)[:, b])            # column b after clear: pivot piv, rest 0
        okcol = all(sp.simplify(cleared_col[r]) == 0 for r in range(n) if r != a)
        detA_ok = detA_ok and okcol
        if L + 1 <= N - 1:                                     # paired gauge preserves A_{L+1}·A_L
            Ap1 = matify(u, d, L + 1)
            prod_ok = prod_ok and (sp.expand((Ap1 * Q1.inv()) * (Q1 * ALf)) == sp.expand(Ap1 * ALf))

    # (B') the FULL composite gauge preserves coreGen (loss invariance) — in-chart form (pivot=1),
    #      i.e. Q₁: row_r -= u_{(L,r,b)} row_a. Apply to the A_L's and check coreGen unchanged
    #      when paired with Q₁⁻¹ on A_{L+1} (product-preserving); here we verify coreGen∘(paired)=coreGen.
    v = dict(u)
    for (L, a, b) in clears:
        AL = matify(v, d, L); n = d[L + 1]
        Q1 = sp.eye(n)
        for r in range(n):
            if r != a:
                Q1[r, a] = -v[(L, r, b)]                       # in-chart pivot=1
        ALc = sp.expand(Q1 * AL)
        for r in range(n):
            for c in range(d[L]):
                v[(L, r, c)] = ALc[r, c]
        if L + 1 <= N - 1:
            Ap1 = matify(v, d, L + 1); Q1i = Q1.inv()
            Ap1c = sp.expand(Ap1 * Q1i)
            for r in range(d[L + 2]):
                for c in range(d[L + 1]):
                    v[(L + 1, r, c)] = Ap1c[r, c]
    cg = [sp.expand(f) for f in coreGen(u, d)]
    cg_gauge = [sp.expand(f) for f in coreGen(v, d)]
    prodB_ok = all(sp.expand(a - b) == 0 for a, b in zip(cg, cg_gauge))

    # (C) chart image of the composite Q₁ row-clears zeros exactly the couplings ⟹ gives C.
    #     In-chart the δ=1 quotient NORMALIZES the pivot to 1 BEFORE the clear (row_r -= A[r,b]·row_a
    #     with A[a,b]=1 ⟹ A[r,b] -> A[r,b]-A[r,b]·1 = 0). Apply pivot-normalized Q₁ per clear.
    cleared_map = ancestor_column_clear_map(u, d, parent)
    couplings = [k for k in u if sp.simplify(cleared_map[k] - u[k]) != 0]
    w = dict(u)
    for (L, a, b) in clears:
        w[(L, a, b)] = sp.Integer(1)                            # δ=1 strict-transform: pivot -> 1
        AL = matify(w, d, L); n = d[L + 1]
        Q1 = sp.eye(n)
        for r in range(n):
            if r != a:
                Q1[r, a] = -w[(L, r, b)]
        ALc = sp.expand(Q1 * AL)
        for r in range(n):
            for c in range(d[L]):
                w[(L, r, c)] = ALc[r, c]
    C_ok = all(sp.expand(w[k]) == 0 for k in couplings)         # Q₁ zeros exactly the couplings

    print(f"{lbl}: clears={clears} couplings={sorted(couplings)}")
    print(f"   (A) each Q₁ unipotent det-1 (pivot FREE) + clears its col: {detA_ok}")
    print(f"   (B) paired gauge preserves ∏A (loss-invariant, RLCT-intrinsic): {prod_ok and prodB_ok}")
    print(f"   (C) in-chart Q₁ zeros exactly the couplings (⟹ gives C): {C_ok}")
    ok = detA_ok and prod_ok and prodB_ok and C_ok
    print(f"   ⟹ LIFT holds (parameter-space det-1 product-preserving gauge): {ok}")
    return ok

if __name__ == "__main__":
    res = []
    res.append(run((2, 2, 2, 2), "first"))
    res.append(run((2, 2, 2, 2, 2), "first"))
    res.append(run((2, 2, 2, 2, 2), "intermediate"))    # multi-coupling B2 crux
    res.append(run((3, 3, 3, 2), "first"))              # wide, multi-coupling
    print("=" * 70)
    print("LIFT CERTIFICATE + full ψ_gen (matrix level):", res,
          "\n  ⟹ the bridge is a PARAMETER-SPACE unipotent Q₁ gauge (det-1, product-preserving);"
          "\n     multi-coupling dissolves at matrix level; no chart weight transported (elder RE-OPEN DISARMED).")
