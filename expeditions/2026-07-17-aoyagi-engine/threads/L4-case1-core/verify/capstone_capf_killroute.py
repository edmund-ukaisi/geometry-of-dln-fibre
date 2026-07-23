"""
CAPF KILL-ROUTE CONSULT (pnp-transport; team-lead relay of seat-CAPF #5, CapDescent.lean @ 8c0ace5ef).

CAPF's kill: IgnoresCoords (sourceClearedResid (p.extend ed) j) (layerCoords S' ∖ blockCoords S') at the
rollover-fresh wide node — the cleared residual does not read the ESCAPED columns (layer-S' cols ≥ wMU).
Two candidate Lean routes:
  (a) PATH INDUCTION (parallel to foldResid_layerHomogeneous') carrying "reads-escaped-only-via-couplings",
      step introducing the coupling factor per δ=1 ancestor clear — tracks the WHOLE path.
  (b) LOCALIZATION: ONLY the immediately-preceding layer's (S'−1) recoord writes the escaped layer-S'
      columns, its mixing coefficients factor through the ancestor couplings — one lemma + the precompose.
CAPF leaned (b).

THE SHARP QUESTION: is the escaped-column dependence introduced EXCLUSIVELY by the single preceding
layer's (S'−1) recoord (⟹ (b) exact), or do deeper ancestors also write escaped columns through composed
shears (⟹ (a) required)?

DISCRIMINATOR: at the rollover-to-layer-S' node (S' ≥ 2, so a deeper ancestor S'−2… exists), clear ONLY
the layer-(S'−1) couplings and check whether the escaped dependence dies. If it survives until deeper
layers are cleared ⟹ deeper ancestors contribute ⟹ route (a).
"""
import sympy as sp, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, Phi_p, coreGen, blockCoords, wmu
from capstone_locus_core import couplingCoords

def layerCoords(d, S):
    return {(S, r, c) for r in range(d[S + 1]) for c in range(d[S])}

def reads(fs, cs, u):
    s = set()
    for f in fs:
        for k in cs:
            if u[k] in f.free_symbols:
                s.add(k)
    return s

def run(d):
    print("=" * 84)
    N, u = dims_coords(d); coords = set(u.keys())
    edges, meta = oracle_edges(d)
    ridx = next((i for i, e in enumerate(edges) if e[0] == "rollover" and e[1] + 1 >= 2 and e[1] + 1 < N), None)
    if ridx is None:
        print(f"  {d}: no rollover to layer >= 2 (need a deeper ancestor to discriminate)"); return None
    path = edges[:ridx + 1]; Sc = edges[ridx][1] + 1
    if not (d[Sc] > wmu(d, Sc)):
        print(f"  {d}: rollover child layer {Sc} not wide"); return None
    escaped = layerCoords(d, Sc) - blockCoords(d, Sc)
    cc = couplingCoords(d, path, coords)
    by_layer = {}
    for k in cc:
        by_layer.setdefault(k[0], set()).add(k)
    print(f"  {d}: rollover→layer S'={Sc} (WIDE d={d[Sc]}>wMU={wmu(d,Sc)}); escaped={sorted(escaped)}")
    print(f"  couplingCoords by layer: " + ", ".join(f"L{L}:{sorted(s)}" for L, s in sorted(by_layer.items())))
    raw = [sp.expand(f) for f in coreGen(Phi_p(u, d, path, True), d)]
    print(f"  RAW residual reads escaped: {sorted(reads(raw, escaped, u))}")

    def clear_layers(layers):
        killset = set().union(*[by_layer.get(L, set()) for L in layers]) if layers else set()
        return {k: (sp.Integer(0) if k in killset else u[k]) for k in u}

    verdict_b_exact = True
    for label, layers in [("S'-1 only", [Sc - 1]), ("S'-1 down to 0", list(range(0, Sc)))]:
        src = [sp.expand(f) for f in coreGen(Phi_p(clear_layers(layers), d, path, True), d)]
        esc = reads(src, escaped, u)
        killed = not esc
        print(f"    clear {label:16s} (layers {layers}): reads escaped={sorted(esc)} -> {'KILLED' if killed else 'STILL READS (deeper needed)'}")
        if label == "S'-1 only" and not killed:
            verdict_b_exact = False
    print(f"  ⟹ route (b) [S'-1 localization] exact here: {verdict_b_exact}")
    return verdict_b_exact

def run_all():
    res = {}
    for d in [(2, 2, 3, 3), (2, 3, 3, 3)]:
        r = run(d)
        if r is not None:
            res[d] = r
    print("\n" + "#" * 84)
    print("VERDICT (CAPF kill-route):")
    for d, r in res.items():
        print(f"  {d}: route (b) S'-1-localization exact = {r}")
    b_general = all(res.values())
    print(f"\n  Route (b) exact IN GENERAL: {b_general}")
    print("  (2,3,3,3) shows S'-1-only does NOT kill the escaped dependence — the escaped col-S' factors")
    print("  through layer-(S'-1) couplings that THEMSELVES factor through layer-(S'-2..0) via composed")
    print("  shears (layer-(S'-1) branch-ii writes A_{S'} reading A_{S'-1}, whose rows carry layer-(S'-2)")
    print("  branch-ii contributions). So DEEPER ancestors contribute ⟹ ROUTE (a) PATH INDUCTION REQUIRED.")
    assert not b_general, "expected route (b) to fail in general (deeper ancestors contribute)"

if __name__ == "__main__":
    run_all()
