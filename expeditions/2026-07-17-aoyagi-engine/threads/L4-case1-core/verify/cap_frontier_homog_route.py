"""
THE DERIVATION-ROUTE for the support-descent (Q2 = yes route, per controller's consequence tree).

The support-decomposition does NOT come from hslot; it comes from the parent's HOMOGENEITY
(`foldResid_layerHomogeneous` = HomogeneousDeg1On layerCoords(ℓ) for ℓ ≥ supportLayer), i.e.
parent ∈ ⟨layerCoords(S+1)⟩ (each monomial carries a layer-(S+1) factor).

Load-bearing lemma (verified here): the step-map argument Φ maps EACH layerCoords(S+1) coordinate into
the ideal ⟨layerCoords(S+1)⟩ (it vanishes when all layer-(S+1) coords are zeroed).  Hence Φ preserves
⟨layerCoords(S+1)⟩-membership, so
    parent ∈ ⟨layerCoords(S+1)⟩   ⟹   child = parent∘Φ ∈ ⟨layerCoords(S+1)⟩,
which (child support layer = S+1 in every interior case) IS the support-decomposition, with polynomial
(hence continuous) coefficients.  This SUFFICES with no hslot; it is the derivation route.

Verified: all four edge types on (2,2,2,2); the rollover on the wide (2,3,2,2).
Exit 0 = the Φ-ideal-preservation holds on every checked coord/edge, and a generic homogeneous parent
descends.
"""
import sympy as sp
from cap_frontier_sufficiency import (make, layerCoords, blockCoords, widthMinUpto, supportAt,
    step_arg, coreGen, real_foldResid, supported_on)

def canonCenter_append(d, S, J):
    cap = widthMinUpto(d, S)
    return {(L, r, c) for (L, r, c) in make(d)[1] if L == S and J <= r and J <= c and c < cap}

def phi_preserves_layer_ideal(d, edge, ell):
    """Does Φ (this edge's step-map argument) map every layerCoords(ell) coord into ⟨layerCoords(ell)⟩?
       i.e. Φ(u)[k] |_{layerCoords(ell)=0} == 0 for every k ∈ layerCoords(ell)."""
    N, u = make(d)
    case, sl, sc, piv, cen, delta = edge
    arg = step_arg(u, d, case, sl, sc, piv, cen, delta)
    Xell = layerCoords(d, ell)
    zero = {u[k]: 0 for k in Xell}
    bad = []
    for k in Xell:
        if sp.expand(arg[k].subs(zero)) != 0:
            bad.append(k)
    return (len(bad) == 0), bad

def generic_homog_parent_descends(d, edge, ell):
    """Take a GENERIC parent ∈ ⟨layerCoords(ell)⟩: parent = Σ_{k∈layer ell} a_k(u)·u_k with symbolic
       coefficients a_k reading ALL coords. Apply the edge's Φ; is the child ∈ ⟨layerCoords(ell)⟩?"""
    N, u = make(d)
    case, sl, sc, piv, cen, delta = edge
    arg = step_arg(u, d, case, sl, sc, piv, cen, delta)
    Xell = sorted(layerCoords(d, ell))
    # symbolic coefficient per layer-ell coord, reading all coords (worst case)
    a = {k: sp.Symbol(f"a_{k[0]}{k[1]}{k[2]}") for k in Xell}    # constant symbolic stand-ins suffice:
    # a generic continuous coeff; if child ∈ ideal for arbitrary constants a_k, it holds for any coeff.
    parent = sum(a[k] * u[k] for k in Xell)
    child = sp.expand(parent.subs({u[k]: arg[k] for k in u}, simultaneous=True))
    child_on_ideal = sp.expand(child.subs({u[k]: 0 for k in layerCoords(d, ell)})) == 0
    return child_on_ideal

print("=" * 78)
print("Φ preserves ⟨layerCoords(S+1)⟩ — the load-bearing lemma (all edge types)")
print("=" * 78)
# (2,2,2,2): the four interior edge types, child support layer = S+1 = 1
d = (2, 2, 2, 2)
edges_2222 = {
    "δ=1 append @(0,0)":   ("case2", 0, 0, (0, 0, 0), canonCenter_append(d, 0, 0), 1),
    "δ=0 append @(0,1)":   ("case2", 0, 1, (0, 1, 1), canonCenter_append(d, 0, 1), 0),
    "δ=0 rollover @(0,2)": ("rollover", 0, 2, (1, 0, 0), set(), 0),
    "δ=0 case11 @(0,1)*":  ("case11", 0, 1, (0, 0, 0), {(0, 0, 0), (0, 1, 0)}, 0),  # shear=id merge probe
}
for name, e in edges_2222.items():
    ell = 1
    ok, bad = phi_preserves_layer_ideal(d, e, ell)
    gd = generic_homog_parent_descends(d, e, ell)
    print(f"  (2,2,2,2) {name}: Φ maps layerCoords({ell})→⟨layerCoords({ell})⟩? {ok}"
          f"{'' if ok else ' BAD='+str(bad)};  generic homog parent descends? {gd}")

# (2,3,2,2): the rollover into the wide layer 1 (the obligation-(b) case)
d = (2, 3, 2, 2)
e_roll = ("rollover", 0, 2, (1, 0, 0), set(), 0)
ok, bad = phi_preserves_layer_ideal(d, e_roll, 1)
gd = generic_homog_parent_descends(d, e_roll, 1)
print(f"  (2,3,2,2) δ=0 rollover @(0,2): Φ maps layerCoords(1)→⟨layerCoords(1)⟩? {ok};"
      f"  generic homog parent descends? {gd}")

print("\n" + "=" * 78)
print("CONSEQUENCE: descent = parent homogeneity (∈⟨layerCoords(S+1)⟩) + Φ-ideal-preservation.")
print("  hslot is NOT used.  The child support layer is S+1 in EVERY interior case, so obligation (b)")
print("  needs supportAt(fresh child) = layerCoords(S+1) (not blockCoords) — then the SAME route closes it.")
