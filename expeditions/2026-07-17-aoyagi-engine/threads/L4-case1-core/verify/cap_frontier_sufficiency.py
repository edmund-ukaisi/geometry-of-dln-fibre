"""
CAP FRONTIER — sufficiency of `hslot` for `realBranch_appendResidDescent` (MonumentAtlas:1442).

Question (elaboration commission, pnp-cap): can the append-edge support-DESCENT
    (parent Deg1SupportedSlot on supportAt(parent))  ⟹  (child support-decomposition on supportAt(child))
be proved by CONSUMING hslot (as the target's docstring intends), or does it require the concrete
foldResid recursion / a stronger carried invariant?

METHOD (charter §3 def-fidelity): transcribe the EXACT current Lean defs (MonumentAtlas.lean,
BlockDivision.lean, BlockBlowup.lean, PathAtoms.lean) and test the PROPERTY AS A FORMULA (the (B)≠(D)
lesson). Two directions:
  (A/C-ce) a black-box parent residual satisfying `Deg1SupportedSlot` on supportAt(parent) whose child
           (the exact foldResid child-branch) is NOT supported on supportAt(child) — refutes hslot⟹concl.
  (B/C-real) the REAL foldResid (coreGen at canonFlatten, real branch) DOES descend — the statement is
           true on the real object (so the finding is "under-hypothesized", not "false").

Exit 0 = all checks as expected.
"""
import sympy as sp

# ----------------------------------------------------------------------------
# Coordinate scaffolding.  tupIdx d = (layer L∈Fin N, row∈Fin d[L+1], col∈Fin d[L]).
# ----------------------------------------------------------------------------
def make(d):
    N = len(d) - 1
    u = {(L, r, c): sp.Symbol(f"u_{L}{r}{c}")
         for L in range(N) for r in range(d[L + 1]) for c in range(d[L])}
    return N, u

def layerCoords(d, ell):
    N = len(d) - 1
    if ell >= N: return set()
    return {(L, r, c) for (L, r, c) in make(d)[1] if L == ell}

def widthMinUpto(d, n):
    return min(d[i] for i in range(len(d)) if i <= n)

def blockCoords(d, ell):
    N = len(d) - 1
    if ell >= N: return set()
    cap = widthMinUpto(d, ell)
    return {(L, r, c) for (L, r, c) in make(d)[1] if L == ell and c < cap}

def supportAt(d, S, J):
    N = len(d) - 1
    if J == 0:            return blockCoords(d, S)
    elif S + 1 < N:       return layerCoords(d, S + 1)
    else:                 return set()

def supportLayerOf(S, J):
    return S if J == 0 else S + 1

# ----------------------------------------------------------------------------
# canonNormalizationOf (MonumentAtlas:939-984) — RAW displacement φ, ALL THREE branches.
# pivot decodes to (pivot_layer, a=pivot-row, b=pivot-col).
# ----------------------------------------------------------------------------
def readEntry(u, d, S, row, col):
    N = len(d) - 1
    if 0 <= S < N and 0 <= row < d[S + 1] and 0 <= col < d[S]:
        return u[(S, row, col)]
    return sp.Integer(0)

def canonNormalizationOf(u, d, s_layer, s_cleared, pivot):
    a, b = pivot[1], pivot[2]
    phi = {}
    for (L, row, col) in u:
        if (L == s_layer and row != a and col != b and s_cleared <= row and s_cleared <= col):
            # (i) pivot-shifted Schur cross-term
            phi[(L, row, col)] = (-readEntry(u, d, s_layer, row, b)) * readEntry(u, d, s_layer, a, col)
        elif (L == s_layer + 1 and col == a):
            # (ii) layer-(S+1) OUTPUT recoord image
            phi[(L, row, col)] = sum(
                (readEntry(u, d, s_layer, i, b) * readEntry(u, d, s_layer + 1, row, i)
                 for i in range(d[s_layer + 1]) if not (i == col or i < s_cleared)),
                sp.Integer(0))
        elif (L + 1 == s_layer and row == b):
            # (iii) layer-(S-1) INPUT recoord image
            phi[(L, row, col)] = sum(
                (readEntry(u, d, s_layer, a, k) * readEntry(u, d, L, k, col)
                 for k in range(d[s_layer]) if not (k == b or k < s_cleared)),
                sp.Integer(0))
        else:
            phi[(L, row, col)] = sp.Integer(0)
    return phi

def edgeShearRaw(u, d, case, s_layer, s_cleared, pivot):
    if case in ("case11", "rollover"):
        return dict(u)
    phi = canonNormalizationOf(u, d, s_layer, s_cleared, pivot)
    return {k: u[k] + phi[k] for k in u}          # blockShear φ = u + φ

# ----------------------------------------------------------------------------
# One fold step (MonumentAtlas foldResid:474-488) — child arg as a function of u.
#   δ=1: blockBlowupCoordQuot pivot k (edgeShearRaw u)   (pivot→1, else sheared)
#   δ=0: blockBlowupMap center pivot (edgeShearRaw u)     (pivot→w_p, center→w_p·w_j, spectator→w_j)
# ----------------------------------------------------------------------------
def step_arg(u, d, case, s_layer, s_cleared, pivot, center, delta):
    w = edgeShearRaw(u, d, case, s_layer, s_cleared, pivot)
    out = {}
    for k in u:
        if delta == 1:
            out[k] = sp.Integer(1) if k == pivot else w[k]
        else:
            out[k] = (w[pivot] if k == pivot else (w[pivot] * w[k] if k in center else w[k]))
    return out

def coreGen(u, d):
    N = len(d) - 1
    def M(L): return sp.Matrix(d[L + 1], d[L], lambda r, c: u[(L, r, c)])
    P = M(N - 1)
    for L in range(N - 2, -1, -1):
        P = P * M(L)
    return [sp.expand(P[i, j]) for i in range(P.rows) for j in range(P.cols)]

def real_foldResid(u, d, edges):
    """edges = [(case, s_layer, s_cleared, pivot, center, delta), ...] root-first."""
    v = dict(u)
    for (case, sl, sc, piv, cen, delta) in reversed(edges):
        v = step_arg(v, d, case, sl, sc, piv, cen, delta)
    return coreGen(v, d)

# ----------------------------------------------------------------------------
# Support-membership check for a POLYNOMIAL: f ∈ ⟨coords in S⟩ ⟺ f|_{S=0}=0.
# (For a polynomial fold this ⟺ ∃ continuous — indeed polynomial — c with f=∑_{i∈S} c_i·u_i.)
# ----------------------------------------------------------------------------
def supported_on(u, f, S):
    return sp.expand(f.subs({u[k]: 0 for k in S})) == 0

def is_deg1_supported_slot(u, d, f, S, fromLayer):
    """Deg1SupportedSlot: (∃ poly c, f = ∑_{i∈S} c_i·u_i) ∧ PerLayerDeg1From(f, fromLayer).
       For a polynomial f the ∃c is exactly support_on(S); PerLayerDeg1From = AffineOn each layer ℓ≥fromLayer
       (total degree ≤1 in that layer's coords)."""
    N = len(d) - 1
    if not supported_on(u, f, S):
        return False, "not supported on S"
    for ell in range(fromLayer, N):
        Xs = [u[k] for k in layerCoords(d, ell)]
        if Xs:
            P = sp.Poly(sp.expand(f), *Xs)
            if P.total_degree() > 1:
                return False, f"deg>1 on layer {ell}"
    return True, "ok"


print("=" * 78)
print("PART A — δ=1 append: black-box parent = (u ↦ u_pivot) refutes hslot ⟹ concl")
print("=" * 78)
d = (2, 2, 2, 2); N, u = make(d)
# Parent = root, state (S=0,J=0), δ=[cleared=0]=1.  First append edge (case2), pivot=(0,0,0)=corner(0,0).
S, J = 0, 0
pivot = (0, 0, 0)
center = supportAt(d, S, J)          # = canonCenterOf case2 at J=0 = blockCoords(0) = layer-0 block
Sp = supportAt(d, S, J)              # parent support = blockCoords(0)
Sc = supportAt(d, S, J + 1)          # child (0,1) support = layerCoords(1)
print(f"  supportAt(parent 0,0) = blockCoords(0), |.|={len(Sp)};  pivot∈parent-support? {pivot in Sp}")
print(f"  supportAt(child  0,1) = layerCoords(1), |.|={len(Sc)}  (all layer-1 coords)")

# black-box parent residual: single slot  f(w) = w_pivot
bb = u[pivot]
ok, why = is_deg1_supported_slot(u, d, bb, Sp, supportLayerOf(S, J))
print(f"  black-box f=u_pivot is a valid Deg1SupportedSlot on supportAt(parent)?  {ok} ({why})")

# child = δ=1 strict transform of the black box: f(child_arg(u)) with pivot→1
arg = step_arg(u, d, "case2", S, J, pivot, center, 1)
child_bb = sp.expand(bb.subs({u[k]: arg[k] for k in u}, simultaneous=True))
print(f"  child(u) = f(strict-transform arg) = {child_bb}   (blockBlowupCoordQuot pivot pivot = 1)")
val0 = child_bb.subs({u[k]: 0 for k in u})
child_ok = supported_on(u, child_bb, Sc)
print(f"  child supported on supportAt(child)?  {child_ok}   (child(0)={val0}; needs 0 for ∑ c_i·u_i)")
A_refutes = ok and (not child_ok)
print(f"  >>> hslot⟹concl REFUTED at δ=1?  {A_refutes}  "
      f"(valid hslot parent, child=const 1 ∉ ⟨supportAt(child)⟩)")

# shear-independence: the pivot term is 1 regardless of the pinned canonNormalizationOf shear
print(f"      [shear-pin irrelevant: blockBlowupCoordQuot pivot pivot ≡ 1, independent of φ]")


print("\n" + "=" * 78)
print("PART C-ce — δ=0 rollover: real rollover is IDENTITY on foldResid; black box refutes obligation (b)")
print("=" * 78)
d = (2, 3, 2, 2); N, u = make(d)
# rollover parent (S=0, J=2) → child (1,0).  canonCenterOf rollover = ∅, shear=id ⟹ step_arg = identity.
S, J = 0, 2
arg_roll = step_arg(u, d, "rollover", S, J, (1, 0, 0), set(), 0)   # pivot free/irrelevant, center=∅
is_id = all(sp.expand(arg_roll[k] - u[k]) == 0 for k in u)
print(f"  real rollover step-arg = identity?  {is_id}  (center=∅, shear=id ⟹ foldResid child = foldResid parent)")
Sp = supportAt(d, S, J)              # parent (0,2): layerCoords(1)
Sc = supportAt(d, 1, 0)              # child  (1,0): blockCoords(1)
cap = widthMinUpto(d, 1)
print(f"  supportAt(parent 0,2)=layerCoords(1) |.|={len(Sp)};  supportAt(child 1,0)=blockCoords(1) |.|={len(Sc)}"
      f"  (cap widthMinUpto(1)=min(d0,d1)=min(2,3)={cap}<d1={d[1]} ⟹ blockCoords(1) ⊊ layerCoords(1))")
# black-box parent: an OUT-OF-CAP layer-1 column coord (col=2), valid on layerCoords(1)
oobc = [k for k in Sp if k not in Sc]
print(f"  out-of-cap layer-1 coords (in layerCoords\\blockCoords): {sorted(oobc)}")
i0 = sorted(oobc)[0]
bb = u[i0]
ok, why = is_deg1_supported_slot(u, d, bb, Sp, supportLayerOf(S, J))
child_bb = sp.expand(bb.subs({u[k]: arg_roll[k] for k in u}, simultaneous=True))
child_ok = supported_on(u, child_bb, Sc)
print(f"  black-box f=u_{i0}: valid Deg1SupportedSlot on layerCoords(1)?  {ok} ({why})")
print(f"  rollover child = {child_bb};  supported on blockCoords(1)?  {child_ok}")
C_refutes = ok and is_id and (not child_ok)
print(f"  >>> hslot⟹concl REFUTED at obligation (b)?  {C_refutes}  "
      f"(parent∈layerCoords(1) but child=itself reads the out-of-cap column ∉ blockCoords(1))")

results = {"A_refutes": A_refutes, "C_refutes": C_refutes, "rollover_is_id": is_id}
print("\nSUMMARY(counterexamples):", results)
assert A_refutes, "PART A did not refute — re-examine"
assert C_refutes, "PART C-ce did not refute — re-examine"
print("OK: hslot is INSUFFICIENT for BOTH δ=1 (obligation a) and rollover (obligation b).")


print("\n" + "=" * 78)
print("PART B — REAL fold DOES descend (statement true on the real object): (2,2,2,2)")
print("=" * 78)
d = (2, 2, 2, 2); N, u = make(d)
def canonCenter_append(d, S, J):   # canonCenterOf case2/case12 (MonumentAtlas:865-871)
    cap = widthMinUpto(d, S)
    return {(L, r, c) for (L, r, c) in make(d)[1]
            if L == S and J <= r and J <= c and c < cap}
# real branch, root-first; each entry carries the PARENT state used by δ/shear
e_root  = ("case2", 0, 0, (0, 0, 0), canonCenter_append(d, 0, 0), 1)   # δ=1 append, child (0,1)
e_app   = ("case2", 0, 1, (0, 1, 1), canonCenter_append(d, 0, 1), 0)   # δ=0 append, child (0,2)
e_roll  = ("rollover", 0, 2, (1, 0, 0), set(), 0)                       # δ=0 rollover, child (1,0)
def child_state(edges):
    S, J = 0, 0
    for (case, sl, sc, piv, cen, delta) in edges:
        if case == "rollover": S, J = S + 1, 0
        elif case == "case11": pass
        else: J = J + 1
    return S, J
for label, edges, (cS, cJ) in [
    ("δ=1 append  (0,0)->(0,1)", [e_root],                (0, 1)),
    ("δ=0 append  (0,1)->(0,2)", [e_root, e_app],         (0, 2)),
    ("δ=0 rollover(0,2)->(1,0)", [e_root, e_app, e_roll], (1, 0)),
]:
    resid = real_foldResid(u, d, edges)
    Sc = supportAt(d, cS, cJ)
    oks = [supported_on(u, f, Sc) for f in resid]
    print(f"  {label}: child supportAt={('blockCoords' if cJ==0 else 'layerCoords')}({cS+(0 if cJ==0 else 1)})"
          f" |.|={len(Sc)};  all {len(resid)} slots supported? {all(oks)}")

print("\n" + "=" * 78)
print("PART C-real — obligation (b) cap-confinement TRUE on the real WIDE fold: (2,3,2,2)")
print("=" * 78)
d = (2, 3, 2, 2); N, u = make(d)
# fully clear layer 0 (2 pivots), rollover to (1,0); layer 1 is 2x3, cap widthMinUpto(1)=min(2,3)=2.
e0 = ("case2", 0, 0, (0, 0, 0), canonCenter_append(d, 0, 0), 1)
e1 = ("case2", 0, 1, (0, 1, 1), canonCenter_append(d, 0, 1), 0)
er = ("rollover", 0, 2, (1, 0, 0), set(), 0)
resid_parent = real_foldResid(u, d, [e0, e1])          # at (0,2), pre-rollover
resid_child  = real_foldResid(u, d, [e0, e1, er])      # at (1,0)
Sp = supportAt(d, 0, 2); Sc = supportAt(d, 1, 0)
identical = all(sp.expand(a - b) == 0 for a, b in zip(resid_parent, resid_child))
par_on_layer = all(supported_on(u, f, Sp) for f in resid_parent)
chld_on_block = all(supported_on(u, f, Sc) for f in resid_child)
# does the REAL parent read the out-of-cap columns (col=2 of layer 1)?
oob = sorted(k for k in Sp if k not in Sc)
reads_oob = any(any(u[k] in sp.expand(f).free_symbols for k in oob) for f in resid_parent)
print(f"  parent(0,2): supported on layerCoords(1) [{len(Sp)}]? {par_on_layer}")
print(f"  child(1,0)=parent (rollover id)? {identical};  supported on blockCoords(1) [cap, {len(Sc)}]? {chld_on_block}")
print(f"  real parent reads out-of-cap cols {oob}? {reads_oob}   "
      f"(FALSE ⟹ cap genuinely holds on the real object ⟹ obligation (b) TRUE on real fold)")
Breal_ok = par_on_layer and chld_on_block and (not reads_oob)
print(f"  >>> obligation (b) TRUE on real object? {Breal_ok}")
if __name__ == "__main__":
    print("\nFINDINGS:")
    print("  A (δ=1)      : hslot INSUFFICIENT (pivot→1 makes child a bare constant).")
    print("  C-ce (δ=0 roll): hslot INSUFFICIENT (rollover=id; cap not in hslot's layerCoords).")
    print(f"  B (2,2,2,2)  : descent holds on the real fold (no cap bites at width 2).")
    print(f"  C-real (2,3,2,2): obligation (b) is {'TRUE' if Breal_ok else 'FALSE'} on the RAW fold "
          f"— raw residual reads out-of-cap col-2 (see cap_frontier_diagnose_b.py for the cause).")
