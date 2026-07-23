"""
#93 — THE KILL TELESCOPING INVARIANT Z(p) (pnp design step; L3T3 pattern → render on CX's foundation).

TARGET: sourceClearedResid_ignoresEscaped — at a fresh (cleared=0) node q, layer S:
  IgnoresCoords (foldResid d q ∘ couplingClear d q) (layerCoords d S ∖ blockCoords d S).
CX's reduction (CapDescent.lean): via foldResid_layerHomogeneous' the KILL ⟺ each escaped coord's
coefficient vanishes on couplingClear-cleared inputs; the coefficient factors through ANCESTOR couplings
(multi-layer, route (a), pnp 81ba59d2b) which couplingClear zeroes.

THE INVARIANT (telescoping, path-level; the L3T3-scale design):
  Z(p) := couplingCoords d p ∪ escapedBelow(p),
  escapedBelow(p) := ⋃_{M=1}^{S_p} escaped(M)   ∪   ( escaped(S_p+1) if c_p ≥ widthMinUpto d (S_p+1) ),
  escaped(M) := layerCoords d M ∖ blockCoords d M = {(M,r,c): widthMinUpto d M ≤ c < d M}.
  INVARIANT Z: `foldResid d p j, evaluated on couplingClear-d-p-cleared inputs, IGNORES Z(p)` (∀ j).

WHY THIS SHAPE (discovered from the witness trace):
  * escaped(M) enters Z at the LAST clear of layer M−1 (when c reaches widthMinUpto d M = the rollover
    threshold), NOT at the rollover — the layer-(M−1) recoord (ii) shear that writes the escaped layer-M
    column has coefficients = layer-(M−1) couplings, and by then ALL of layer M−1's couplings are accumulated.
  * across ROLLOVER Z is UNCHANGED (CX: blockBlowupMap ∅ = id ⟹ foldResid unchanged; escaped(M) already
    entered at the prior last-clear) — so at the fresh child (c=0, layer S) escaped(S) ∈ Z = THE KILL.
  * the conditional escaped(S_p+1) term is what CARRIES escaped across the last-clear→rollover boundary.

VERIFY: (V1) Z(p) ⊆ ignored-set(p) at EVERY node (foldResid∘couplingClear genuinely ignores Z); the KILL
escaped(S) ⊆ Z at every fresh node. (V2) the per-transition telescoping (δ=1/δ=0 add coupling + the
conditional escaped; rollover unchanged) holds as stated. Witnesses: (2,3,3,3) [escape L1,L2; single-recoord
fails here], (2,3,2,2) [escape L1], (2,4,3,3) [wide escape], (2,2,2) [last-layer boundary, no escape].
"""
import sympy as sp, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, coreGen, Phi_p, wmu, blockCoords
from capstone_locus_core import couplingCoords, couplingClear

def layerCoords(d, S):
    return {(S, r, c) for r in range(d[S + 1]) for c in range(d[S])}

def escaped(d, M):
    N = len(d) - 1
    if M >= N:
        return set()
    return layerCoords(d, M) - blockCoords(d, M)

def state_of(d, br, i):
    """(layer, cleared) after prefix br[:i]."""
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

def Zinv(d, br, i, coords):
    S, c = state_of(d, br, i)
    return couplingCoords(d, br[:i], coords) | escapedBelow(d, S, c)

def ignored_set(d, path, u, coords):
    clr = couplingClear(d, path, u, coords)
    res = [sp.expand(f) for f in coreGen(Phi_p(clr, d, path, True), d)]
    read = set()
    for f in res:
        for k in coords:
            if u[k] in f.free_symbols:
                read.add(k)
    return coords - read

def run(d):
    N, u = dims_coords(d); coords = set(u.keys()); edges, meta = oracle_edges(d)
    br = [e for e in edges if e[0] != "terminal"]
    print(f"\n{'='*84}\nd={d}   escaped by layer: " +
          ", ".join(f"L{M}:{len(escaped(d,M))}" for M in range(N)))
    ok_V1 = True; ok_kill = True
    for i in range(len(br) + 1):
        S, c = state_of(d, br, i)
        Z = Zinv(d, br, i, coords)
        ign = ignored_set(d, br[:i], u, coords)
        subset = Z <= ign
        ok_V1 &= subset
        lab = br[i - 1][0] if i > 0 else "root"
        fresh = (c == 0)
        killrow = ""
        if fresh and S < N:
            escS = escaped(d, S)
            killok = escS <= Z
            ok_kill &= killok
            killrow = f"  KILL escaped(S={S})⊆Z: {killok}"
        flag = "" if subset else "  <<< Z ⊄ ignored"
        print(f"  node{i:2d} [{lab:8s}] S={S} c={c}: Z⊆ignored={subset}{flag}{killrow}")
    print(f"  (V1) Z(p) ⊆ ignored at every node: {ok_V1};  KILL escaped(S)⊆Z at every fresh node: {ok_kill}")
    return ok_V1 and ok_kill

def telescoping_check(d):
    """(V2) per-transition: δ=1/δ=0 ⟹ Z grows by belowPivotCol ∪ (conditional escaped); rollover ⟹ Z\\cc unchanged."""
    N, u = dims_coords(d); coords = set(u.keys()); edges, meta = oracle_edges(d)
    br = [e for e in edges if e[0] != "terminal"]
    ok = True
    for i in range(len(br)):
        Zp = escapedBelow(d, *state_of(d, br, i))            # escaped-part only (couplingCoords telescopes trivially by def)
        Zc = escapedBelow(d, *state_of(d, br, i + 1))
        e = br[i]
        if e[0] == "rollover":
            good = (Zc == Zp)                                 # rollover: escaped-part UNCHANGED
        else:
            # a clear: escaped-part grows only by escaped(S+1) exactly when c+1 reaches wmu(S+1)
            S, c = state_of(d, br, i)
            grew = Zc - Zp
            expect = escaped(d, S + 1) if (S + 1 <= N and (c + (1 if e[0] in ("case2","case12") else 0)) >= wmu(d, S + 1)
                                           and c < wmu(d, S + 1)) else set()
            good = (grew == expect)
        ok &= good
        if not good:
            print(f"    telescoping MISMATCH at node{i} [{e[0]}]: grew {sorted(Zc-Zp)}")
    print(f"  (V2) telescoping (escaped-part transitions as stated): {ok}")
    return ok

def mechanism_check(d):
    """(V3) THE RENDER'S KEY SUB-LEMMA (the escaped-absorption step): at the LAST clear of a layer S (c
    reaching wmu(S+1)), the coefficient of each escaped(S+1) coord in the RAW foldResid (∂/∂u_e) lies in the
    ideal ⟨couplingCoords d p⟩ — so couplingClear (setting couplings=0) kills it. This is CX's trace made
    general (coeff factors through ancestor couplings) AND route-(a) (multiple ancestor layers)."""
    N, u = dims_coords(d); coords = set(u.keys()); edges, meta = oracle_edges(d); allv = list(u.values())
    br = [e for e in edges if e[0] != "terminal"]
    checked = 0; ok = True
    for i in range(1, len(br) + 1):
        S, c = state_of(d, br, i)
        if S + 1 > N or not (c >= wmu(d, S + 1)) or not escaped(d, S + 1):
            continue                                          # only last-clear nodes with a fresh escape
        path = br[:i]
        cc = couplingCoords(d, path, coords)
        gens = [u[k] for k in cc]
        raw = [sp.expand(f) for f in coreGen(Phi_p(u, d, path, True), d)]   # RAW foldResid (no clear)
        G = sp.groebner([g for g in gens], *allv, order='grevlex') if gens else None
        for e in escaped(d, S + 1):
            for f in raw:
                ce = sp.expand(f.coeff(u[e], 1))              # coefficient of the escaped coord (deg-1)
                if ce == 0:
                    continue
                inideal = (G is not None) and (sp.expand(G.reduce(ce)[1]) == 0)
                checked += 1; ok &= inideal
                if not inideal:
                    print(f"    MECH FAIL node{i} escaped {e}: coeff {ce} ∉ ⟨couplingCoords⟩")
    print(f"  (V3) escaped-coeff ∈ ⟨couplingCoords⟩ at last-clear nodes ({checked} nonzero coeffs): {ok}")
    return ok

if __name__ == "__main__":
    res = {}
    for d in [(2, 3, 3, 3), (2, 3, 2, 2), (2, 4, 3, 3), (2, 2, 2)]:
        v1 = run(d); v2 = telescoping_check(d); v3 = mechanism_check(d)
        res[d] = v1 and v2 and v3
    print(f"\n{'#'*84}\nKILL INVARIANT Z(p): V1 (⊆ignored + KILL) ∧ V2 (telescoping) all witnesses: {all(res.values())}")
    for d, v in res.items():
        print(f"  {d}: {'OK' if v else 'FAIL'}")
    assert all(res.values())
