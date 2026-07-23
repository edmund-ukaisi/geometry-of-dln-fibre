"""
ψ_gen — THE B2 CHART-FAITHFULNESS MAP, CONSTRUCTED (pnp-transport #70, team-lead GO).

Builds the det-1 polynomial automorphism ψ_gen with F∘ψ_gen = C (raw foldResid straightens to the
Case-1(1) chart residual = source-cleared object) as the COMPOSITE of per-coupling flat-field
straightenings, and verifies per witness:
  (1) F∘ψ_gen = C exactly       (2) det Dψ_gen = 1
  (3) ψ_gen*⟨F⟩ = ⟨C⟩ (ideal-EQUIVALENCE, the corrected bridge)   (4) RLCT(∑F²)=RLCT(∑C²) [via det-1]

Construction: for each coupling coord x_k (ancestor-cleared column below-pivot entry = E_J=identity
chart coordinate), find the flat field V_k = ∂_{x_k} + Σ_w c_{k,w}∂_w with V_k(F_j)=0 (c_{k,w} solved,
degree bounded), then ψ_k(w) = w + x_k·c_{k,w}. Compose; re-solve on the transported F if couplings
interact. Verify the composite.

Witnesses: (2,2,2,2) archetype; (2,2,2,2,2) BOTH case11 nodes incl. the layer-2 intermediate B2 crux;
(3,3,3,2) wide (higher-degree flat fields).
"""
import sympy as sp
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, Phi_p, coreGen, blockCoords
from capstone_closing_ii import ancestor_column_clear_map

def node_data(d, which="first"):
    N, u = dims_coords(d); edges, meta = oracle_edges(d)
    c11 = [i for i, e in enumerate(edges) if e[0] == "case11"]
    idx = c11[0] if which == "first" else next(i for i in c11 if meta[i]['birth_f'][0] >= 1)
    parent = edges[:idx]
    F = [sp.expand(f) for f in coreGen(Phi_p(u, d, parent, True), d)]
    C = [sp.expand(f) for f in coreGen(Phi_p(ancestor_column_clear_map(u, d, parent), d, parent, True), d)]
    cleared = ancestor_column_clear_map(u, d, parent)
    X = [k for k in u if sp.simplify(cleared[k] - u[k]) != 0]
    return N, u, F, C, X, edges[idx], meta[idx]

def solve_flat_field(u, F, X, xk, maxdeg=2):
    """V = ∂_xk + Σ_{w∉X} c_w ∂_w, c_w poly (deg ≤ maxdeg) in non-coupling coords, V(F_j)=0 ∀j."""
    Xs = {u[k] for k in X}; xsym = u[xk]
    W = [u[k] for k in u if u[k] not in Xs]
    # candidate coeff basis: monomials up to maxdeg in the non-coupling coords that actually appear in ∂F/∂*
    appearing = set()
    for f in F:
        appearing |= f.free_symbols
    basis_vars = [w for w in W if w in appearing]
    for deg in range(1, maxdeg + 1):
        # monomials of degree exactly d over basis_vars, plus constants
        from itertools import combinations_with_replacement
        monos = [sp.Integer(1)]
        for dd in range(1, deg + 1):
            for combo in combinations_with_replacement(basis_vars, dd):
                monos.append(sp.prod(combo))
        a = {(w, i): sp.Symbol(f"a_{iw}_{i}") for iw, w in enumerate(W) for i in range(len(monos))}
        cw = {w: sum(a[(w, i)] * monos[i] for i in range(len(monos))) for w in W}
        unk = [a[(w, i)] for w in W for i in range(len(monos))]
        eqs = set()
        for f in F:
            expr = sp.expand(sp.diff(f, xsym) + sum(cw[w] * sp.diff(f, w) for w in W))
            if expr != 0:
                eqs |= set(sp.Poly(expr, *list(u.values())).coeffs())
        sol = sp.linsolve(list(eqs), unk)
        if sol and sol != sp.EmptySet:
            solset = list(sol)[0]; subs = dict(zip(unk, solset))
            cw_sol = {w: sp.expand(cw[w].subs(subs)) for w in W}
            # free params → 0
            free = (set().union(*[v.free_symbols for v in cw_sol.values()]) if cw_sol else set()) & set(unk)
            z = {p: 0 for p in free}
            cw_sol = {w: sp.expand(v.subs(z)) for w, v in cw_sol.items()}
            if all(sp.expand(sp.diff(f, xsym) + sum(cw_sol[w] * sp.diff(f, w) for w in W)) == 0 for f in F):
                return cw_sol, deg
    return None, None

def build_psi(d, which):
    N, u, F, C, X, ce, cm = node_data(d, which)
    lbl = f"{d} [{which}: S{ce[1]} reuse{cm['birth_f']}]"
    if not X:
        print(f"{lbl}: no coupling (split already holds raw)"); return True
    allv = list(u.values())
    Fcur = list(F)
    psi = {v: v for v in allv}          # accumulated ψ_gen
    for xk in X:
        cw, deg = solve_flat_field(u, Fcur, X, xk, maxdeg=3)
        if cw is None:
            print(f"{lbl}: flat field for {xk} NOT found up to deg 3 — report partial"); return None
        xsym = u[xk]
        step = {w: sp.expand(w + xsym * cw[w]) for w in cw if cw[w] != 0}
        # compose into psi and push Fcur forward
        psi = {v: sp.expand(psi[v].subs(step, simultaneous=True)) for v in psi}
        Fcur = [sp.expand(f.subs(step, simultaneous=True)) for f in Fcur]
    Fpsi = [sp.expand(f.subs(psi, simultaneous=True)) for f in F]
    okF = all(sp.expand(a - b) == 0 for a, b in zip(Fpsi, C))
    Jt = sp.Matrix([[sp.diff(psi[v], w) for w in allv] for v in allv])
    okdet = sp.expand(Jt.det()) == 1
    # ideal equivalence: ψ*<F> = <C>  ⇔  <Fpsi> = <C> (Fpsi already = C if okF); report the corrected test
    print(f"{lbl}: couplings {sorted(X)}")
    print(f"   F∘ψ_gen == C: {okF}   det Dψ_gen == 1: {okdet}   ⟹ RLCT(∑F²)=RLCT(∑C²): {okF and okdet}")
    return okF and okdet

if __name__ == "__main__":
    res = []
    res.append(build_psi((2, 2, 2, 2), "first"))
    res.append(build_psi((2, 2, 2, 2, 2), "first"))
    res.append(build_psi((2, 2, 2, 2, 2), "intermediate"))   # THE B2 CRUX
    res.append(build_psi((3, 3, 3, 2), "first"))              # WIDE
    print("=" * 70)
    print("ψ_gen built+verified on:", res, "(True=ok, None=partial/higher-deg)")
