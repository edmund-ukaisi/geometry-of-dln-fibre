"""
CERTIFICATE-STRUCTURE Q1-Q3 for CAPR's INV spine (pnp-transport, team-lead priority-2).

Q1 IgnoresCoords TARGET T (live tension): is ed.center ⊆ supportAt ∪ couplingCoords (Codex's
   ledgerCenter — expected NO, since e₂=birth-corner ∉ either), or ⊆ accumulatedExceptionals ∪ block
   (L4D's T — expected YES, contains e₂ by construction)?  T must ⊇ every case11 ed.center (IgnoresCoords
   monotonicity). Verified set-containment at case11 nodes across witnesses.
Q2 μ ACCUMULATION (the b-ledger, worked.tex:562-577): read the per-slot exceptional-monomial b_i off the
   CLEARED residual (sourceClearedResid = b_i·clean-support-coord) and the step law empirically, incl the
   MULTI-STEP double-boost (3,3,2,2). Explicit Finsupp vs ∃-bound multiset: does the multiset thread the
   multi-step cancellation?
Q3 RESTRICTION at the case11 read-off: part-rows → the exceptional monomial has NO e₂ factor (µ.restrict
   center=0 on part); extra-rows → exactly one e₂ (b_i = u_{e₂}·rest) — the boost/divisibility structure.

Exact sympy. Reports; CAPR bakes the spine on the answers.
"""
import sympy as sp
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, Phi_p, coreGen, blockCoords, wmu, cornerToFlat
from capstone_closing_ii import ancestor_column_clear_map

def layer_of(k): return k[0]

# ---------- Q1: the IgnoresCoords target ----------
def couplingCoords(u, d, parent):
    cl = ancestor_column_clear_map(u, d, parent)
    return {k for k in u if sp.simplify(cl[k] - u[k]) != 0}

def accumulatedExceptionals(d, parent_plus_case11):
    """birth corners / pivots of all clears (case2/case12 diagonal + case11 reused-birth) along the path."""
    exc = set()
    for e in parent_plus_case11:
        if e[0] in ("case2", "case12", "case11") and e[3] is not None:
            exc.add(e[3])
    return exc

def Q1(d):
    N, u = dims_coords(d)
    edges, meta = oracle_edges(d)
    res = []
    for idx, e in enumerate(edges):
        if e[0] != "case11":
            continue
        parent = edges[:idx]; S, J = e[1], e[2]; center = e[4]
        supp = blockCoords(d, S)
        coup = couplingCoords(u, d, parent)
        exc = accumulatedExceptionals(d, edges[:idx + 1])
        block = supp
        A = supp | coup                       # Codex ledgerCenter
        B = exc | block                        # L4D's T
        inA = center <= A; inB = center <= B
        missA = sorted(center - A)
        res.append((S, J, inA, inB, missA))
        print(f"  {d} case11@(S={S},J={J}): ed.center={sorted(center)}")
        print(f"     ⊆ supportAt∪couplingCoords (Codex): {inA}  (missing: {missA})")
        print(f"     ⊆ accumExceptionals∪block (L4D):     {inB}")
    return res

# ---------- Q2/Q3: the per-slot exceptional monomial off the cleared residual ----------
def cleared_resid(u, d, path):
    return [sp.expand(f) for f in coreGen(Phi_p(ancestor_column_clear_map(u, d, path), d, path, True), d)]

def per_slot_bmonomial(fj, u, d, S):
    """foldResid_j = ∑_{i∈support} c_i·u_i; each c_i = b_i·(clean). Extract the exceptional monomial part
       of c_i = the product of NON-support (exceptional/earlier-layer) coords. Return {support_i: bmon}."""
    supp = blockCoords(d, S); out = {}
    for i in supp:
        ci = sp.expand(fj.coeff(u[i], 1))
        if ci == 0:
            continue
        # the exceptional (b) monomial = ci with all NON-exceptional (output-layer) coords set to 1,
        # i.e. keep only earlier-layer (< S) coords = the b-ledger exceptionals.
        earlier = [u[k] for k in u if k[0] < S]
        bmon = ci
        for k in u:
            if k[0] >= S:          # zero out output/support-layer coords -> keep exceptional monomial * const
                bmon = bmon  # leave; we instead read exponents of earlier-layer coords below
        out[i] = ci
    return out

def Q2Q3(d):
    N, u = dims_coords(d)
    edges, meta = oracle_edges(d)
    print(f"  witness {d}:")
    for idx, e in enumerate(edges):
        if e[0] != "case11":
            continue
        parent = edges[:idx]; S, J = e[1], e[2]; e2 = e[3]; center = e[4]
        supp = blockCoords(d, S); part = supp & center; extra = supp - center
        R = cleared_resid(u, d, parent)        # sourceClearedResid at the PARENT (the split object)
        ue2 = u[e2]
        print(f"   case11@(S={S},J={J}) e₂={e2} part={sorted(part)} extra={sorted(extra)}")
        for j, fj in enumerate(R[:2]):         # first 2 slots as representatives
            cs = {}
            for i in supp:
                ci = sp.expand(fj.coeff(u[i], 1))
                if ci == 0:
                    continue
                e2exp = sp.Poly(ci, ue2).degree() if ci.has(ue2) else 0
                cs[i] = (str(sp.factor(ci)), e2exp)
            part_e2 = {i: cs[i][1] for i in part if i in cs}
            extra_e2 = {i: cs[i][1] for i in extra if i in cs}
            print(f"     slot{j}: part-coord e₂-exponents={part_e2} (Q3: expect 0); "
                  f"extra-coord e₂-exponents={extra_e2} (Q3: expect 1)")
    print()

if __name__ == "__main__":
    print("=" * 84); print("Q1 — the IgnoresCoords carried target T:")
    for d in [(2, 2, 2, 2), (3, 3, 2, 2), (2, 3, 2, 2)]:
        Q1(d)
    print("=" * 84); print("Q2/Q3 — per-slot exceptional monomial + restriction laws (incl double-boost 3,3,2,2):")
    for d in [(2, 2, 2, 2), (3, 3, 2, 2)]:
        Q2Q3(d)
