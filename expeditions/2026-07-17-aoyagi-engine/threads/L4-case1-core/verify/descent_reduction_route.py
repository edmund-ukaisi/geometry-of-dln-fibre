"""
seat-descent — VALIDITY CHECK of the FP+AT+IH reduction ROUTE for the step case of
sourceClearedResid_ignoresEscapedBelow (CapDescent.lean:603).

The route (per seat-KILL Q1) reduces each step to:
  sourceClearedResid(node) u = g(σ_full u),  g = sourceClearedResid(parent),  σ_full u = τ(clr_node u)
where τ = apply_edge(·, step-edge) (the fold step map), clr_node = couplingClear over the child's edges.
g ignores killZ(parent) = couplingCoords(parent) ∪ escapedBelow(parent)   [IH + ignoresCouplingCoords].
So `g ∘ σ_full` ignores killZ(parent) IF σ_full is killZ(parent)-PRESERVING:
    for every output k ∉ killZ(parent), (σ_full u)_k reads NO input coord in killZ(parent).
(cc(parent) ⊆ cc(child) is zeroed by clr_node, so the only worry is EB(parent) reads.)

THE WORRY (branch (iii), the input recoord at layer S-1): a branch-(iii) output k=(S-1,b,col_k) with
k ∉ killZ(parent) reads readEntry(S,a,k')·readEntry(S-1,k',col_k); the first factor can be an escaped(S)
coord (∈ EB(parent)) when k' ≥ wmu(S). Does the second factor always vanish (coupling) so the term drops?
This script decides it EMPIRICALLY on the on-branch sympy model, at EVERY case2/case12 node, across
witnesses INCLUDING wmu(S) < wmu(S-1) (a layer narrower than a predecessor — where the worry bites).

PASS  => the reduction route is valid (build FP+AT+IH for all non-growth arms).
FAIL  => case2/case12 needs a deeper argument than FP+AT+IH; report the leaking (node, k, read).
"""
import sympy as sp, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, wmu, apply_edge
from capstone_locus_core import couplingCoords, couplingClear

def layerCoords(d, S):
    return {(S, r, c) for r in range(d[S + 1]) for c in range(d[S])}

def escaped(d, M):
    N = len(d) - 1
    return set() if M >= N else (layerCoords(d, M) - {(M, r, c) for r in range(d[M+1]) for c in range(d[M]) if c < wmu(d, M)})

def state_of(d, br, i):
    if i == 0:
        return 0, 0
    e = br[i - 1]
    if e[0] == "rollover":
        return e[1] + 1, 0
    return e[1], e[2] + (1 if e[0] in ("case2", "case12") else 0)

def escapedBelow(d, S, c):
    N = len(d) - 1
    Z = set()
    for M in range(1, S + 1):
        Z |= escaped(d, M)
    if S + 1 <= N and c >= wmu(d, S + 1):
        Z |= escaped(d, S + 1)
    return Z

def killZ(d, br, i, coords):
    S, c = state_of(d, br, i)
    return couplingCoords(d, br[:i], coords) | escapedBelow(d, S, c)

def check(d):
    N, u = dims_coords(d); coords = set(u.keys()); edges, meta = oracle_edges(d)
    br = [e for e in edges if e[0] != "terminal"]
    print(f"\n{'='*80}\nd={d}  wmu by layer: " + ", ".join(f"wmu({M})={wmu(d,M)}" for M in range(N+1)))
    ok = True
    for i in range(1, len(br) + 1):
        e = br[i - 1]                                    # the step edge (parent i-1 -> child i)
        if e[0] not in ("case2", "case12"):
            continue                                     # rollover/case11 clean by hand-analysis
        kzP = killZ(d, br, i - 1, coords)                # killZ(parent)
        clr = couplingClear(d, br[:i], u, coords)        # clr over CHILD edges
        sig = apply_edge(clr, d, *e)                     # σ_full = τ(clr_node u)
        # symbol -> coord map (to name any leaking read)
        sym2coord = {u[k]: k for k in coords}
        for k in coords:
            if k in kzP:
                continue                                 # k ∈ killZ(parent): g ignores it, no constraint
            reads = {sym2coord[s] for s in sp.expand(sig[k]).free_symbols if s in sym2coord}
            leak = reads & kzP                           # cc(parent) already zeroed by clr; leak = EB(parent) reads
            if leak:
                ok = False
                print(f"  LEAK node{i} [{e[0]} S={e[1]} c={e[2]}] out k={k} reads killZ(parent): {sorted(leak)}")
    print(f"  route valid (no non-killZ output reads killZ(parent)) for all case2/case12 nodes: {ok}")
    return ok

if __name__ == "__main__":
    res = {}
    for d in [(2, 3, 2, 2), (2, 3, 3, 3), (3, 2, 2, 2), (2, 4, 3, 3), (3, 3, 2, 2), (2, 2, 3, 2), (3, 2, 3, 2)]:
        res[d] = check(d)
    print(f"\n{'#'*80}\nREDUCTION ROUTE (killZ(parent)-preservation) valid on all witnesses: {all(res.values())}")
    for d, v in res.items():
        print(f"  {d}: {'OK' if v else 'LEAK'}")
