"""
THE DECISIVE ∃q CHECK (pnp-transport, team-lead — biggest fork): does the RAW child StepInv hold at a
case11 δ=1 child, ROUTE-INDEPENDENTLY (∃ continuous q), even though the pointwise pivot-mul crux fails?

StepInv (PrincipalInv:82): coreGen_i(foldG_child u) = ∑_j q_ij(u)·(foldB_child(u)·foldResid_child_j(u)),
q ContinuousOn, plus (coreGen_i∘foldG_child)(0)=0.  Def-exact objects (MonumentAtlas):
 - foldG (:373):  root=id; step = foldG_parent ∘ stepMapRaw  (FULL blow-up, blockBlowupMap — NOT the quot)
 - foldB (:402):  root=1;  step = (u pivot)^δ · foldB_parent(stepMapRaw u)   (δ = edgeδ parent = [cleared=0])
 - foldResid (:474): the fold recursion (blockBlowupCoordQuot at δ=1, stepMapRaw at δ=0)  [my machinery]
 - F = coreGen.

CHECK: coreGen∘foldG_child_i ∈ ⟨foldB_child·foldResid_child_j : j⟩ (continuous q)?  Since foldB is a
common SCALAR factor, split:
 (a) foldB_child | coreGen∘foldG_child_i  (exact divisibility);
 (b) (coreGen∘foldG_child_i)/foldB_child ∈ ⟨foldResid_child_j⟩  (polynomial module membership, Gröbner).
Both ⟹ polynomial (hence continuous) q exists ⟹ ∃q HOLDS (raw), route-independent — a PER-NODE bridge,
NO global re-architecture.  Also compare to the pointwise q=identity (coreGen∘foldG_i == foldB·foldResid_i):
if that FAILS but (a)+(b) HOLD, the ∃ absorbs a non-identity witness (the exact point of the fork).
Witnesses: (2,2,2,2) minimal + (2,3,2,2) wide.
"""
import sympy as sp
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, coreGen, canonNormalizationOf

def edgeShearRaw(u, d, case, sL, sC):
    if case in ("case11", "rollover"):
        return dict(u)
    phi = canonNormalizationOf(u, d, sL, sC, None, True)  # placeholder; recompute with pivot below
    return {k: u[k] + phi[k] for k in u}

def shear(u, d, case, sL, sC, piv):
    if case in ("case11", "rollover"):
        return dict(u)
    phi = canonNormalizationOf(u, d, sL, sC, piv, True)
    return {k: u[k] + phi[k] for k in u}

def stepMapRaw_apply(u, d, e):
    case, sL, sC, piv, cen, delta = e
    w = shear(u, d, case, sL, sC, piv)
    out = {}
    for k in u:
        if piv is not None and k == piv:
            out[k] = w[piv]
        elif piv is not None and k in cen:
            out[k] = w[piv] * w[k]
        else:
            out[k] = w[k]
    return out

def fold_transform_apply(u, d, e):
    """the FOLD's argument transform: blockBlowupCoordQuot at δ=1, stepMapRaw at δ=0."""
    case, sL, sC, piv, cen, delta = e
    w = shear(u, d, case, sL, sC, piv)
    out = {}
    for k in u:
        if case == "rollover":
            out[k] = w[k]
        elif delta == 1:
            out[k] = sp.Integer(1) if k == piv else w[k]
        else:
            out[k] = (w[piv] if k == piv else (w[piv] * w[k] if (piv is not None and k in cen) else w[k]))
    return out

def foldG(u, d, edges):
    v = dict(u)
    for e in reversed(edges):
        v = stepMapRaw_apply(v, d, e)
    return v

def foldResid(u, d, edges):
    v = dict(u)
    for e in reversed(edges):
        v = fold_transform_apply(v, d, e)
    return coreGen(v, d)

def foldB(u, d, edges):
    if not edges:
        return sp.Integer(1)
    en = edges[-1]; rest = edges[:-1]
    piv, delta = en[3], en[5]
    fac = (u[piv] ** delta) if (piv is not None) else sp.Integer(1)
    return sp.expand(fac * foldB(stepMapRaw_apply(u, d, en), d, rest))

def in_ideal(f, gens, allv):
    f = sp.expand(f)
    if f == 0:
        return True
    nz = [sp.expand(g) for g in gens if sp.expand(g) != 0]
    if not nz:
        return False
    G = sp.groebner(nz, *allv, order='grevlex')
    return sp.expand(G.reduce(f)[1]) == 0

def run(d):
    print("=" * 88)
    N, u = dims_coords(d)
    edges, meta = oracle_edges(d)
    idx = next(i for i, e in enumerate(edges) if e[0] == "case11")
    child = edges[:idx + 1]                      # path INCLUDING the case11 edge → the case11 δ=1 CHILD
    allv = list(u.values())
    print(f"d={d}: case11 child path = {[(e[0], e[1], e[2]) for e in child]}")
    FG = coreGen(foldG(u, d, child), d)          # coreGen ∘ foldG_child
    R = foldResid(u, d, child)                   # foldResid_child slots
    B = foldB(u, d, child)                        # foldB_child (scalar)
    FG = [sp.expand(f) for f in FG]; R = [sp.expand(f) for f in R]; B = sp.expand(B)
    print(f"  foldB_child = {B}")
    # deepest-point vanishing
    zero = {v: 0 for v in allv}
    dpv = all(sp.expand(f.subs(zero)) == 0 for f in FG)
    # ∃ POLYNOMIAL q  ⟺  coreGen∘foldG_i ∈ ⟨foldB·foldResid_j⟩  (Gröbner ideal membership; ⟹ ∃ continuous q)
    gens = [sp.expand(B * rj) for rj in R]
    per_i = [in_ideal(f, gens, allv) for f in FG]
    modok = all(per_i)
    print(f"  coreGen∘foldG_i ∈ ⟨foldB·foldResid_j⟩ per-slot: {per_i}")
    # also the WHOLE-PRODUCT (aggregated) reading L4D flagged: ∑ coreGen∘foldG_i² ∈ ⟨foldB·foldResid_j⟩ ?
    whole = in_ideal(sum(f * f for f in FG), gens, allv)
    # pointwise q=identity comparison: coreGen∘foldG_i == foldB·foldResid_i ?
    ptwise = all(sp.expand(FG[i] - B * R[i]) == 0 for i in range(len(FG))) if len(FG) == len(R) else False
    # NECESSARY condition for ANY continuous q: foldB (a product of COORDINATES) must divide coreGen∘foldG_i.
    # (RHS = foldB·∑q·foldResid ⟹ RHS/foldB continuous ⟹ divisible by each coord factor of foldB.)
    Bfac = [g for g in B.free_symbols]                      # the coord factors of foldB (squarefree monomial)
    div_by_foldB = []
    for f in FG:
        ok = all(sp.expand(f.subs(g, 0)) == 0 for g in Bfac)   # f|_{coord=0}=0 for each coord factor
        div_by_foldB.append(ok)
    print(f"  foldB={B} factors={sorted(str(g) for g in Bfac)}; foldB | coreGen∘foldG_i per-slot: {div_by_foldB}")
    print(f"  ∃ polynomial q (all slots ∈ ideal): {modok}   [whole-product ∈ ideal: {whole}]")
    print(f"  ⟹ CONTINUOUS-q NECESSARY condition (foldB | all slots): {all(div_by_foldB)} "
          f"— if FALSE, NO continuous q exists (∃q FAILS definitively)")
    print(f"  [pointwise q=identity holds: {ptwise}]  deepest-point vanish: {dpv}")
    verdict = modok and dpv
    print(f"  ⟹ RAW child StepInv ∃(polynomial)q HOLDS (route-independent): {verdict}"
          + ("  (∃ absorbs a NON-identity q — pointwise fails but ideal-membership holds)" if verdict and not ptwise else ""))
    return verdict, ptwise

if __name__ == "__main__":
    res = {}
    for d in [(2, 2, 2, 2), (2, 3, 2, 2)]:
        res[d] = run(d)
    print("=" * 88)
    for d, (v, p) in res.items():
        print(f"  {d}: ∃q RAW StepInv = {'HOLDS' if v else 'FAILS'} (pointwise-identity {'holds' if p else 'FAILS'})")
    print("  ∃q HOLDS ⟹ per-node bridge, NO global re-architecture; ∃q FAILS ⟹ global move (FoldStepInvAt on C) forced.")
