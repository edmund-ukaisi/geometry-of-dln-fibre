"""
THE STRAIGHTENING ψ — raw↔cleared is a DET-1 CoV (pnp-transport #68/#70, decorrelated-Codex-found,
VERIFIED here). Corrects my earlier "dimension obstruction" over-claim.

Codex (capstone-bridge-iii-answer.md) found, on (2,2,2,2), a polynomial automorphism ψ with F∘ψ = C
(raw foldResid straightens to the source-cleared object), det Dψ = 1. I re-derive it exactly here (never
paste Codex's algebra unrun). Consequence: raw and cleared are RLCT-EQUIVALENT (RLCT(∑F²)=RLCT(∑C²)),
so fixing the coupling coord is RLCT-preserving — Option 1 is RLCT-SOUND. BUT ψ CONJUGATES the center
(I=(z,b₀,d₀) ↦ ψ-images), so it repairs the split on a MOVED pivot, not the original z-edge: the bridge
is ideal-EQUIVALENCE (ψ*⟨F⟩=⟨C⟩), NOT ideal-equality (which stays false). This is the chart-faithfulness
(B2) structure.

x=u₀₁₀ (coupling), y=u₀₀₁, z=u₀₁₁=e₂, b₀=u₁₀₀,b₁=u₁₀₁,d₀=u₁₁₀,d₁=u₁₁₁.
ψ: b₀↦b₀−2x·b₁, d₀↦d₀−2x·d₁, z↦z+2x·y (others fixed).
"""
import sympy as sp
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, Phi_p, coreGen
from capstone_closing_ii import ancestor_column_clear_map

def run_2222():
    d = (2, 2, 2, 2); N, u = dims_coords(d)
    edges, meta = oracle_edges(d); idx = next(i for i, e in enumerate(edges) if e[0] == "case11")
    parent = edges[:idx]; center = edges[idx][4]
    x, y, z = u[(0, 1, 0)], u[(0, 0, 1)], u[(0, 1, 1)]
    b0, b1, d0, d1 = u[(1, 0, 0)], u[(1, 0, 1)], u[(1, 1, 0)], u[(1, 1, 1)]
    F = [sp.expand(f) for f in coreGen(Phi_p(u, d, parent, True), d)]
    C = [sp.expand(f) for f in coreGen(Phi_p(ancestor_column_clear_map(u, d, parent), d, parent, True), d)]
    psi = {b0: b0 - 2 * x * b1, d0: d0 - 2 * x * d1, z: z + 2 * x * y}
    Fpsi = [sp.expand(f.subs(psi, simultaneous=True)) for f in F]
    allv = list(u.values())
    img = {k: k for k in allv}; img.update(psi)
    J = sp.Matrix([[sp.diff(img[v], w) for w in allv] for v in allv])
    def V(f):  # flat vector field
        return sp.expand(sp.diff(f, x) - 2 * b1 * sp.diff(f, b0) - 2 * d1 * sp.diff(f, d0) + 2 * y * sp.diff(f, z))
    r = {}
    r["F∘ψ == C (all slots)"] = all(sp.expand(a - b) == 0 for a, b in zip(Fpsi, C))
    r["det Dψ == 1"] = sp.expand(J.det()) == 1
    r["flat field V(F_j)=0 ∀j, V(x)=1"] = all(V(f) == 0 for f in F) and V(x) == 1
    r["center CONJUGATED (ψ(z)≠z)"] = sp.expand(z.subs(psi, simultaneous=True) - z) != 0
    # RLCT-equivalence corollary (det-1 CoV): the losses are related by a volume-preserving map
    r["∑F² = (∑C²)∘ψ⁻¹  (RLCT-equivalent)"] = sp.expand(sum(f**2 for f in F)
        - sum(c**2 for c in C).subs({b0: b0 + 2 * x * b1, d0: d0 + 2 * x * d1, z: z - 2 * x * y},
                                    simultaneous=True)) == 0
    print("(2,2,2,2) straightening ψ:  b₀↦b₀−2x·b₁, d₀↦d₀−2x·d₁, z↦z+2x·y")
    for k, v in r.items():
        print(f"  {k}: {v}")
    return all(r.values())

if __name__ == "__main__":
    ok = run_2222()
    print(f"\nψ VERIFIED: {ok}  ⟹ raw↔cleared det-1 CoV; RLCT preserved; bridge = ideal-EQUIVALENCE "
          f"(center conjugated), NOT ideal-equality.")
