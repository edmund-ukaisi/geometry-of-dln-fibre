"""
CAPSTONE SPLIT — CHART-FRAME (pnp-transport, task #68).

Tests the EXACT `MergeBoostSplit` predicate on the CONCRETE foldResid recursion, in the
frame L4D pinned (MonumentAtlas.lean:474-488):

    foldResid d (canonFlatten d) p  u  =  coreGen d (canonFlatten d) ( T_1 ( T_2 ( ... T_n(u) ) ) )

where T_1..T_n are the ANCESTOR edge transforms of the branch root->p (T_1 = root edge,
OUTERMOST/applied-last), each T = blockBlowupCoordQuot(pivot)∘edgeShearRaw (δ=1) or
blockBlowupMap(center,pivot)∘edgeShearRaw (δ=0).  The TARGET is the PARENT residual
foldResid(...p), split over the CHILD case11 edge's center.

THE FRAME FIX (my prior capstone_invariant_witness.py error): I evaluated RAW coreGen (no
ancestor transforms) and saw the extra block factoring through DIFFERENT raw coords per slot,
"no single e₂".  The ancestor transforms are exactly what install the single-e₂ factoring:
`u e₂` reads slot canonPivotOf in foldResid's ARGUMENT frame — the value branch-(i) wrote there
(the reused exceptional).  This script contrasts RAW (fails) vs TRANSFORMED (passes).

MergeBoostSplit (MergeBoostSplit.lean:26):
    ∀ j, ∃ α β, α,β ContinuousOn V ∧ α,β IgnoresCoords center ∧
      resid j u = (∑_{i∈part} α_i u · u_i)  +  u_{e₂} · (∑_{i∈extra} β_i u · u_i)
with e₂ = canonPivotOf, part = supportAt ∩ ed.center, extra = supportAt ∖ ed.center,
center = ed.center, V = foldRegion(...p).

Concrete sufficient test (well-defined because PerLayerDeg1From ⟹ resid is LINEAR in the support
layer, so c_i := ∂resid/∂u_i is free of support coords, canonical):
  (L)  resid j is degree-1 in the support coords: resid j = ∑_{i∈support} c_i·u_i, c_i support-free.
  (B)  for i∈extra: c_i divisible by u_{e₂}  (c_i.subs(u_{e₂},0) == 0, polynomial ⟹ u_{e₂}|c_i).
  (C)  center-ignoring: α_i := c_i (i∈part) free of center coords; β_i := c_i/u_{e₂} (i∈extra)
       free of center coords.
"""
import sympy as sp

# ---------------- flat coords, matrices, coreGen ----------------
def build(d):
    N = len(d) - 1
    u = {}
    for L in range(N):
        for r in range(d[L + 1]):
            for c in range(d[L]):
                u[(L, r, c)] = sp.Symbol(f"u_{L}_{r}_{c}")
    return N, u

def mat(u, d, L):
    return sp.Matrix(d[L + 1], d[L], lambda r, c: u[(L, r, c)])

def coreGen(u, d):
    """entries of A_{N-1}···A_1 A_0 (last layer leftmost); the k-th flat entry."""
    N = len(d) - 1
    M = mat(u, d, N - 1)
    for L in range(N - 2, -1, -1):
        M = M * mat(u, d, L)
    return [M[i, j] for i in range(M.rows) for j in range(M.cols)]

def widthMinUpto(d, n):
    N = len(d) - 1
    return min(d[i] for i in range(0, min(n, N - 1) + 1))

def blockCoords(d, S):
    """layer-S coords with col < widthMinUpto(S)."""
    wmu = widthMinUpto(d, S)
    return {(S, r, c) for r in range(d[S + 1]) for c in range(d[S]) if c < wmu}

def layerCoords(d, S):
    return {(S, r, c) for r in range(d[S + 1]) for c in range(d[S])}

def supportAt(d, S, J):
    N = len(d) - 1
    if J == 0:
        return blockCoords(d, S)
    elif S + 1 < N:
        return layerCoords(d, S + 1)
    else:
        return set()

# ---------------- fold transforms (canonFlatten model) ----------------
def edgeShearRaw(u, d, case, s_layer, s_cleared):
    """edgeShearRaw: id at case11/rollover; blockShear (Schur recoord) at case12/case2.
       blockShear φ writes -u_{r,cl}·u_{cl,c} on interior (row>cl, col>cl) at layer s_layer."""
    if case in ("case11", "rollover"):
        return dict(u)
    out = dict(u)
    N = len(d) - 1
    if s_layer < N:
        for r in range(d[s_layer + 1]):
            for c in range(d[s_layer]):
                if r > s_cleared and c > s_cleared:
                    out[(s_layer, r, c)] = (u[(s_layer, r, c)]
                                            - u[(s_layer, r, s_cleared)] * u[(s_layer, s_cleared, c)])
    return out

def apply_edge(u, d, case, s_layer, s_cleared, pivot, center, delta):
    """foldResid child arg = (δ=1) blockBlowupCoordQuot(pivot)∘shear  OR
                             (δ=0) blockBlowupMap(center,pivot)∘shear   (blow-up OUTERMOST)."""
    w = edgeShearRaw(u, d, case, s_layer, s_cleared)
    out = {}
    for k in u:
        if case == "rollover":
            out[k] = w[k]
        elif delta == 1:                       # blockBlowupCoordQuot: pivot->1, else w_k
            out[k] = sp.Integer(1) if k == pivot else w[k]
        else:                                   # blockBlowupMap(center,pivot): pivot->w_p, center->w_p·w_k
            if k == pivot:
                out[k] = w[pivot]
            elif k in center:
                out[k] = w[pivot] * w[k]
            else:
                out[k] = w[k]
    return out

def foldResid_parent(u, d, parent_edges):
    """coreGen ∘ T_1 ∘ ... ∘ T_n ; parent_edges listed root-first, T_1 outermost (applied last)."""
    v = dict(u)
    for (case, sl, sc, piv, cen, delta) in reversed(parent_edges):
        v = apply_edge(v, d, case, sl, sc, piv, cen, delta)
    return coreGen(v, d)

# ---------------- the split test ----------------
def test_split(resid, u, d, support, part, extra, center, e2, label, verbose=True):
    """Returns True iff every slot satisfies MergeBoostSplit with the given data."""
    ue2 = u[e2]
    support_syms = {u[c] for c in support}
    center_syms = {u[c] for c in center}
    ok_all = True
    fail_notes = []
    for j, f in enumerate(resid):
        fe = sp.expand(f)
        if fe == 0 or fe == 1:
            continue
        # (L) linearity in support: reconstruct ∑ c_i u_i and check exact + c_i support-free
        recon = sp.Integer(0)
        c = {}
        for i in support:
            ci = sp.expand(fe.coeff(u[i], 1))
            c[i] = ci
            recon += ci * u[i]
        lin_ok = sp.expand(fe - recon) == 0
        cfree_ok = all(len(sp.expand(c[i]).free_symbols & support_syms) == 0 for i in support)
        # (B) extra coeffs divisible by u_e2
        divB_ok = True
        for i in extra:
            if sp.expand(c[i].subs(ue2, 0)) != 0:
                divB_ok = False
        # (C) center-ignoring: α_i=c_i (part) free of center; β_i=c_i/ue2 (extra) free of center
        cignore_ok = True
        for i in part:
            if len(sp.expand(c[i]).free_symbols & center_syms) != 0:
                cignore_ok = False
        for i in extra:
            beta = sp.expand(sp.cancel(c[i] / ue2)) if c[i] != 0 else sp.Integer(0)
            # ensure exact polynomial quotient
            if sp.expand(beta * ue2 - c[i]) != 0:
                cignore_ok = False
            if len(beta.free_symbols & center_syms) != 0:
                cignore_ok = False
        slot_ok = lin_ok and cfree_ok and divB_ok and cignore_ok
        ok_all = ok_all and slot_ok
        if not slot_ok:
            fail_notes.append((j, dict(lin=lin_ok, cfree=cfree_ok, divB=divB_ok, cign=cignore_ok),
                               {str(u[i]): sp.expand(c[i]) for i in support}))
        if verbose:
            tag = "OK " if slot_ok else "**FAIL**"
            print(f"    slot {j}: {tag} lin={lin_ok} cfree={cfree_ok} extra|u_e2={divB_ok} center-ign={cignore_ok}")
    print(f"  [{label}] SPLIT {'HOLDS' if ok_all else 'FAILS'} "
          f"(e₂={e2}, part={sorted(part)}, extra={sorted(extra)})")
    if not ok_all and verbose:
        for (j, flags, cs) in fail_notes[:3]:
            print(f"      fail slot {j} {flags}; coeffs {cs}")
    return ok_all

# =====================================================================
#  WITNESS 1 — (2,2,2,2): case11 deep-merge at layer 1 reusing layer-0 divisor
# =====================================================================
def witness_2222():
    print("=" * 78)
    print("WITNESS 1: d=(2,2,2,2) — case11 deep-merge at L1 reusing the layer-0 divisor")
    d = (2, 2, 2, 2)
    N, u = build(d)
    # PARENT branch root->p: clear layer 0 (case2 δ=1, case2 δ=0), rollover to layer 1.
    parent = [
        ("case2",    0, 0, (0, 0, 0), set(),           1),
        ("case2",    0, 1, (0, 1, 1), {(0, 1, 1)},     0),
        ("rollover", 0, 2, None,      set(),           0),
    ]
    # child case11 edge off p (state L1,cl0): reuses divisor born at (0,1,1); center per canonCenterOf
    e2 = (0, 1, 1)                      # canonPivotOf = reused divisor birth corner (layer 0)
    center = {(0, 1, 1), (1, 0, 0), (1, 1, 0)}   # {pivot} ∪ runLen(=1)-capped col-0 block, full rows
    S, J = 1, 0
    support = supportAt(d, S, J)        # blockCoords d 1 = all layer-1 coords
    part = support & center
    extra = support - center
    print(f"  support(=blockCoords L1) = {sorted(support)}")
    print(f"  center = {sorted(center)},  e₂={e2}")
    print(f"  part = supp∩center = {sorted(part)},  extra = supp∖center = {sorted(extra)}")
    assert e2 in center and e2 not in part and not (extra & center)

    print("\n  -- RAW coreGen (NO ancestor transforms) — the FRAME-WRONG evaluation:")
    raw = coreGen(u, d)
    ok_raw = test_split(raw, u, d, support, part, extra, center, e2, "RAW", verbose=False)

    print("\n  -- foldResid(p) = coreGen ∘ (ancestor transforms) — the CORRECT chart frame:")
    fr = foldResid_parent(u, d, parent)
    ok_tr = test_split(fr, u, d, support, part, extra, center, e2, "TRANSFORMED")
    return ok_raw, ok_tr

# =====================================================================
#  WITNESS 2 — (3,3,2,2): WIDER + double-boost region (runLen>1 merge)
# =====================================================================
def witness_3322():
    print("=" * 78)
    print("WITNESS 2: d=(3,3,2,2) — wider layer-1, case11 merge (runLen structure)")
    d = (3, 3, 2, 2)
    N, u = build(d)
    # PARENT: clear layer 0 (3 clears: δ=1 then δ=0 δ=0), rollover to layer 1.
    parent = [
        ("case2",    0, 0, (0, 0, 0), set(),                 1),
        ("case2",    0, 1, (0, 1, 1), {(0, 1, 1), (0, 2, 1)}, 0),
        ("case2",    0, 2, (0, 2, 2), {(0, 2, 2)},            0),
        ("rollover", 0, 3, None,      set(),                 0),
    ]
    e2 = (0, 2, 2)                       # reuse the last layer-0 divisor birth corner
    S, J = 1, 0
    support = supportAt(d, S, J)         # blockCoords d 1: layer-1, col<widthMinUpto(1)=min(3,3)=3 (wait d1=3,d0=3)
    # widthMinUpto(1)=min(d0,d1)=min(3,3)=3 but layer-1 cols ∈ Fin d_1 = Fin 3, and d_2=2 rows.
    # runLen=1 merge: center = {pivot} ∪ {layer1, col 0, all rows}
    center = {e2} | {(1, r, 0) for r in range(d[2])}
    part = support & center
    extra = support - center
    print(f"  support(=blockCoords L1) = {sorted(support)}")
    print(f"  center = {sorted(center)},  e₂={e2}")
    print(f"  part = {sorted(part)},  extra = {sorted(extra)}")
    assert e2 in center and e2 not in part and not (extra & center)
    fr = foldResid_parent(u, d, parent)
    ok = test_split(fr, u, d, support, part, extra, center, e2, "TRANSFORMED (3,3,2,2)")
    return ok

# =====================================================================
#  KILLED-BY-e — a generic (scrambling) flatten breaks the split
# =====================================================================
def killed_by_e():
    print("=" * 78)
    print("KILLED-BY-e: replace canonFlatten by a within-layer SCRAMBLER e — split must BREAK")
    d = (2, 2, 2, 2)
    N, u = build(d)
    # scrambler: mix the two columns of each layer's matrix (a linear iso, NOT block-respecting
    # in the way canonFlatten is). Concretely replace A_L by A_L·G with G a fixed 2x2 mix on the
    # INPUT (column) index -> couples layer-L col-0 and col-1 in each product entry.
    G = sp.Matrix([[1, 1], [0, 1]])       # unipotent column mix (the (1,1,1)-scrambler analogue)
    def coreGen_scr(uu):
        M = mat(uu, d, N - 1)
        for L in range(N - 2, -1, -1):
            M = M * (mat(uu, d, L) * G)
        return [M[i, j] for i in range(M.rows) for j in range(M.cols)]
    parent = [
        ("case2",    0, 0, (0, 0, 0), set(),           1),
        ("case2",    0, 1, (0, 1, 1), {(0, 1, 1)},     0),
        ("rollover", 0, 2, None,      set(),           0),
    ]
    e2 = (0, 1, 1)
    center = {(0, 1, 1), (1, 0, 0), (1, 1, 0)}
    support = supportAt(d, 1, 0); part = support & center; extra = support - center
    # compose ancestor transforms then apply scrambled coreGen
    v = dict(u)
    for (case, sl, sc, piv, cen, delta) in reversed(parent):
        v = apply_edge(v, d, case, sl, sc, piv, cen, delta)
    fr = coreGen_scr(v)
    ok = test_split(fr, u, d, support, part, extra, center, e2, "SCRAMBLED-e", verbose=False)
    print(f"  (expected FAILS — canonFlatten-specific; ∀e form is FALSE / KILLED-BY-e)")
    return ok

if __name__ == "__main__":
    r_raw, r_tr = witness_2222()
    ok2 = witness_3322()
    ok_scr = killed_by_e()
    print("=" * 78)
    print("SUMMARY")
    print(f"  (2,2,2,2) RAW coreGen split      : {'HOLDS' if r_raw else 'FAILS'}  (frame-wrong; expect FAILS)")
    print(f"  (2,2,2,2) foldResid(p) split     : {'HOLDS' if r_tr else 'FAILS'}  (chart frame; expect HOLDS)")
    print(f"  (3,3,2,2) foldResid(p) split     : {'HOLDS' if ok2 else 'FAILS'}  (wider; expect HOLDS)")
    print(f"  KILLED-BY-e scrambled split      : {'HOLDS' if ok_scr else 'FAILS'}  (expect FAILS)")
    verdict = (not r_raw) and r_tr and ok2 and (not ok_scr)
    print(f"\n  CERTIFICATE FRAME {'CONFIRMED' if verdict else 'NOT yet confirmed — inspect above'}")
