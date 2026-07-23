"""
CAP-TRANSPORT HINGE (pnp-transport, team-lead/navigator commission).

Q: does obligation-(b) `realBranch_appendResidDescent_fresh_sourceCleared` — the cleared residual's
confinement to blockCoords(child.layer) at the ROLLOVER-fresh interior wide node — TRANSPORT from the raw
UNCAPPED descent (Deg1 on layerCoords(child.layer)) via the couplingClear precompose, or is it INDEPENDENT?
Decides whether a cap-frontier render runs PARALLEL to GM's unit.

Node (SourceClearedResid.lean:222, CAPR lane): rollover child (hroll, cleared=0, layer S+1 < N),
support = blockCoords d (S+1) (running-min CAPPED). The raw fold reads out-of-cap (layerCoords∖blockCoords)
on a wide branch (§9 artifact).

LEVEL 1 (L4D's sufficient condition — cheap): escaped set (layerCoords(S+1) ∖ blockCoords(S+1) = child-layer
cols ≥ widthMinUpto) ⊆ couplingCoords (ancestor below-pivot {(L,r,b): r>a})? Expected FALSE (escaped at the
CHILD layer; couplings at ancestor layers).
LEVEL 2 (the hinge): at the rollover-fresh wide node, (a) does raw foldResid read the escaped cols? (b) does
sourceClearedResid = foldResid∘couplingClear confine to blockCoords (escaped cols NOT read)? If (a)&(b) ⟹
the escaped-col dependence DIES AT THE PRECOMPOSE (its coefficients factor through the ancestor couplings
that couplingClear zeroes) ⟹ (b) = raw-uncapped-fact ∘ couplingClear ⟹ TRANSPORTS (cap render parallel).
If raw reads escaped AND cleared STILL reads them ⟹ INDEPENDENT (needs own induction, holds behind GM).

Witnesses: (2,3,2,2), (2,3,3,2) — rollover 0→1, layer 1 WIDE interior. Exact sympy.
"""
import sympy as sp
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, Phi_p, coreGen, blockCoords, wmu
from capstone_closing_ii import ancestor_column_clear_map

def layerCoords(d, S):
    return {(S, r, c) for r in range(d[S + 1]) for c in range(d[S])}

def couplingCoords(u, d, path):
    cl = ancestor_column_clear_map(u, d, path)
    return {k for k in u if sp.simplify(cl[k] - u[k]) != 0}

def run(d):
    print("=" * 88)
    N, u = dims_coords(d)
    edges, meta = oracle_edges(d)
    ridx = next((i for i, e in enumerate(edges) if e[0] == "rollover"
                 and e[1] + 1 < N and e[1] + 1 >= 1), None)   # rollover to interior layer S+1≥1
    if ridx is None:
        print(f"  {d}: no interior rollover"); return None
    path = edges[:ridx + 1]                                    # up to & including the rollover
    Sc = edges[ridx][1] + 1                                     # child layer = S+1
    if not (d[Sc] > wmu(d, Sc)):
        print(f"  {d}: rollover child layer {Sc} not wide"); return None
    block = blockCoords(d, Sc); layer = layerCoords(d, Sc)
    escaped = layer - block
    coup = couplingCoords(u, d, path)
    print(f"  {d}: rollover→child layer S+1={Sc} (WIDE: d={d[Sc]} > wMU={wmu(d,Sc)})")
    print(f"     blockCoords(S+1) (capped) = {sorted(block)}")
    print(f"     escaped (layerCoords∖blockCoords) = {sorted(escaped)}")
    print(f"     couplingCoords = {sorted(coup)}")
    # LEVEL 1
    lvl1 = escaped <= coup
    print(f"  (1) escaped ⊆ couplingCoords: {lvl1}  {'(sufficient cond HOLDS)' if lvl1 else '(FAILS — escaped at child layer, coupling at ancestor)'}")
    # LEVEL 2
    raw = [sp.expand(f) for f in coreGen(Phi_p(u, d, path, True), d)]
    src = [sp.expand(f) for f in coreGen(Phi_p(ancestor_column_clear_map(u, d, path), d, path, True), d)]
    def reads(fs, coords):
        s = set()
        for f in fs:
            for k in coords:
                if u[k] in f.free_symbols:
                    s.add(k)
        return s
    raw_esc = reads(raw, escaped); src_esc = reads(src, escaped)
    print(f"  (2a) RAW foldResid reads escaped cols: {sorted(raw_esc)}")
    print(f"  (2b) sourceClearedResid reads escaped cols: {sorted(src_esc)}")
    # confinement: is sourceClearedResid Deg1-supported within blockCoords (reads no escaped)?
    confined = not src_esc
    transports = bool(raw_esc) and confined
    verdict = "TRANSPORTS" if transports else ("INDEPENDENT" if src_esc else "trivial(raw reads none)")
    print(f"  ⟹ raw reads escaped & cleared confined to blockCoords: {transports}  VERDICT: {verdict}")
    return verdict

if __name__ == "__main__":
    res = {d: run(d) for d in [(2, 3, 2, 2), (2, 3, 3, 2)]}
    print("=" * 88)
    print("CAP-TRANSPORT HINGE:")
    for d, v in res.items():
        print(f"  {d}: {v}")
    print("TRANSPORTS ⟹ (b) = raw-uncapped-descent ∘ couplingClear; the escaped dependence dies at the")
    print("  precompose (coeffs factor through ancestor couplings); cap-frontier render can run PARALLEL to GM.")
