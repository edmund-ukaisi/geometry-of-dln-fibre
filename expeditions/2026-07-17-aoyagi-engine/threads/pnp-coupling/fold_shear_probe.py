#!/usr/bin/env python3
"""
pnp-coupling adjudication (exact algebra): does pinning the per-step shear to canonShearOf SUPPLY the
prepared/cofactor structure the residual needs so BOTH proof gaps close?

We fold the ACTUAL Lean object foldResid (pullback of coreGen through the exact operations) on
d=(2,2,2,2), N=3, along a real branch, and MEASURE at each node:
  * per-layer total degree of every residual entry (the PerLayerDeg1From content);
  * whether the child residual is Deg1-supported on supportAt(child) (the ∃c support-decomp).
We do the whole fold TWICE: shear = canonShearOf (the pin) vs shear = identity (R_bad proxy), and
diff. This isolates exactly what canonShearOf supplies.

Exact operations, faithful to the Lean defs:
  coreGen[i][j]        = (A_{N-1}...A_1 A_0)[i][j],  A_s entries = layer-s coords  (MULTI-AFFINE).
  blockBlowupMap(C,p)  : p->w_p ; k in C\\{p} -> w_p*w_k ; else w_k.
  canonShearOf(S,J)    : coord (S,row,col) with row>J,col>J  gets  -w_(S,row,J)*w_(S,J,col) added
                         (Schur), else 0.   blockShear(phi): w -> w + phi(w).
  stepMap              = blockBlowupMap(C,p) o blockShear(canonShearOf)      (delta=0 pullback).
  qm                   = ( k -> if k=p then 1 else blockShear(canonShearOf)(w)_k )   (delta=1 strict).
  foldResid step delta=1 : child(u) = parent(qm u)
              delta=0 : child(u) = parent(stepMap u)
  edgeδ = (cleared == 0).
"""
import sympy as sp
from itertools import product as iprod

N = 3                      # d=(2,2,2,2): layers 0,1,2 ; each block 2x2
W = 2                      # uniform width
layers = range(N)
def coord(s, r, c): return sp.Symbol(f"u_{s}_{r}_{c}")
COORDS = {(s, r, c): coord(s, r, c) for s in layers for r in range(W) for c in range(W)}
ALL = list(COORDS.values())

def layer_syms(s):  return [COORDS[(s, r, c)] for r in range(W) for c in range(W)]

# ---- coreGen : entries of A_{N-1}...A_1 A_0  (A_s = layer-s 2x2 matrix) --------------------------
def Amat(s): return sp.Matrix(W, W, lambda r, c: COORDS[(s, r, c)])
Prod = Amat(N-1)
for s in range(N-2, -1, -1):
    Prod = Prod * Amat(s)
Prod = sp.expand(Prod)
coreGen = [Prod[i, j] for i in range(W) for j in range(W)]   # the residual family at root

# ---- exact operations ---------------------------------------------------------------------------
def canon_shear_disp(S, J):
    """phi = canonShearOf(S,J): dict coord->displacement expression (Schur cross term)."""
    disp = {}
    for r in range(W):
        for c in range(W):
            if r > J and c > J:
                disp[(S, r, c)] = -COORDS[(S, r, J)] * COORDS[(S, J, c)]
    return disp

def block_shear_subs(S, J, use_canon):
    """substitution dict implementing w -> w + phi(w) (canon) or identity."""
    if not use_canon:
        return {}
    d = canon_shear_disp(S, J)
    return {COORDS[k]: COORDS[k] + v for k, v in d.items()}

def center_case2(S, J):
    """canonCenterOf case2/case12: layer-S block rows>=J, cols>=J (col<widthMin=W)."""
    return [(S, r, c) for r in range(W) for c in range(W) if r >= J and c >= J]

def pivot_diag(S, J):
    return (S, J, J)

def stepmap_subs(S, J, use_canon):
    """stepMap = blockBlowupMap(center,pivot) o blockShear(phi).  Returns coord-value dict on ORIGINAL
    coords: value = blockBlowupMap applied to the sheared point."""
    sh = block_shear_subs(S, J, use_canon)          # w -> sheared value (as expr in COORDS)
    def sheared(k): return COORDS[k] if COORDS[k] not in sh else sh[COORDS[k]]
    # more robust: sheared value of coord k
    def shear_val(k):
        base = COORDS[k]
        return base + (-COORDS[(S, k[1], J)]*COORDS[(S, J, k[2])] if (use_canon and k[0]==S and k[1]>J and k[2]>J) else 0)
    C = set(center_case2(S, J)); p = pivot_diag(S, J)
    out = {}
    for k in COORDS:
        v = shear_val(k)                            # blockShear first
        if k == p:
            out[COORDS[k]] = shear_val(p)           # pivot: blowup sends p-> w_p (its sheared value)
        elif k in C:
            out[COORDS[k]] = shear_val(p) * v       # center: w_p * w_k
        else:
            out[COORDS[k]] = v                       # spectator
    return out

def qm_subs(S, J, use_canon):
    """qm = strict transform: pivot->1 ; else sheared value.  (blockBlowupCoordQuot o blockShear)."""
    p = pivot_diag(S, J)
    def shear_val(k):
        base = COORDS[k]
        return base + (-COORDS[(S, k[1], J)]*COORDS[(S, J, k[2])] if (use_canon and k[0]==S and k[1]>J and k[2]>J) else 0)
    out = {}
    for k in COORDS:
        out[COORDS[k]] = sp.Integer(1) if k == p else shear_val(k)
    return out

# ---- degree diagnostics -------------------------------------------------------------------------
def layer_degrees(expr, s):
    """max total degree of any monomial of expr in the layer-s coords."""
    expr = sp.expand(expr)
    syms = layer_syms(s)
    p = sp.Poly(expr, *ALL) if expr != 0 else None
    if p is None: return 0
    idx = [ALL.index(x) for x in syms]
    best = 0
    for monom in p.monoms():
        best = max(best, sum(monom[i] for i in idx))
    return best

def deg1_supported_on(expr, support_coords):
    """check expr = sum_{i in support} c_i * u_i with c_i IGNORING support (i.e. total degree in
    support coords is <=1 AND the constant (support->0) term is 0)."""
    expr = sp.expand(expr)
    sup = [COORDS[k] for k in support_coords]
    # vanish at support -> 0
    z = {x: 0 for x in sup}
    if sp.expand(expr.subs(z)) != 0:
        return False, "nonzero at support=0"
    # each monomial has total support-degree <=1
    if expr == 0:
        return True, "zero"
    p = sp.Poly(expr, *ALL)
    idx = [ALL.index(x) for x in sup]
    for monom in p.monoms():
        if sum(monom[i] for i in idx) > 1:
            return False, f"support-degree {sum(monom[i] for i in idx)}>1"
    return True, "ok"

# ---- supportAt (Lean def) -----------------------------------------------------------------------
def block_coords(s):
    if s >= N: return []
    return [(s, r, c) for r in range(W) for c in range(W)]   # widthMin=W, full block

def support_at(S, J):
    if J == 0: return block_coords(S)
    if S + 1 < N: return block_coords(S + 1)
    return []

def support_layer_of(S, J):
    return S if J == 0 else S + 1

# ---- the fold along a real branch ---------------------------------------------------------------
# branch: for each layer S=0,1  do  (S,cleared=0) delta=1 clear ; (S,cleared=1) delta=0 clear ; rollover.
# (layer 2 = last, S+1=N: terminal; we stop after entering it.)  We track the residual family.
def run(use_canon, verbose=True):
    resid = list(coreGen)                    # foldResid at root (list of exprs)
    tag = "canonShearOf" if use_canon else "IDENTITY-shear"
    print("\n" + "="*90)
    print(f"FOLD with shear = {tag}")
    print("="*90)
    # root node state (layer 0, cleared 0)
    verdicts = []
    def report(name, S, J):
        # per-layer degrees + Deg1 on supportAt(S,J)
        degs = {s: max(layer_degrees(r, s) for r in resid) for s in layers}
        fl = support_layer_of(S, J)
        # per-layer deg1 from fromLayer up:
        bad_layers = [s for s in layers if s >= fl and degs[s] > 1]
        sup = support_at(S, J)
        d1 = [deg1_supported_on(r, sup) for r in resid]
        d1ok = all(x[0] for x in d1)
        print(f"  node {name} state(S={S},J={J})  fromLayer={fl}  supportAt=layer"
              f"{'∅' if not sup else sup[0][0]}")
        print(f"      per-layer max degrees {degs}   deg>1 at layer>=fromLayer: {bad_layers or 'NONE'}")
        print(f"      Deg1-supported on supportAt : {d1ok}"
              + ("" if d1ok else f"   [{[x[1] for x in d1 if not x[0]]}]"))
        verdicts.append((name, d1ok, bad_layers))
        return d1ok, bad_layers

    report("ROOT", 0, 0)
    # ---- layer 0 entry: delta=1 clear at (0,0) ----
    sub = qm_subs(0, 0, use_canon)
    resid = [sp.expand(r.subs(sub, simultaneous=True)) for r in resid]
    report("after L0 δ=1 clear -> (0,cleared1)", 0, 1)
    # ---- layer 0 second clear at cleared=1 : delta=0 pullback ----
    sub = stepmap_subs(0, 1, use_canon)
    resid = [sp.expand(r.subs(sub, simultaneous=True)) for r in resid]
    report("after L0 δ=0 clear -> (0,cleared2)", 0, 2)
    # ---- rollover to layer 1 (cleared reset 0) : residual unchanged (relabel) ----
    report("rollover -> (1,cleared0)", 1, 0)
    # ---- layer 1 entry: delta=1 clear at (1,0) ----
    sub = qm_subs(1, 0, use_canon)
    resid = [sp.expand(r.subs(sub, simultaneous=True)) for r in resid]
    report("after L1 δ=1 clear -> (1,cleared1)", 1, 1)
    # ---- layer 1 second clear cleared=1 : delta=0 ----
    sub = stepmap_subs(1, 1, use_canon)
    resid = [sp.expand(r.subs(sub, simultaneous=True)) for r in resid]
    report("after L1 δ=0 clear -> (1,cleared2)", 1, 2)
    return verdicts

vc = run(True)
vi = run(False)

print("\n" + "="*90)
print("DIFF (canonShearOf vs identity) — where does the shear BITE?")
print("="*90)
for (nc, okc, badc), (ni, oki, badi) in zip(vc, vi):
    flag = "" if (okc == oki and badc == badi) else "   <<< DIFFERS"
    print(f"  {nc:40s}  canon:(Deg1={okc},bad{badc})  ident:(Deg1={oki},bad{badi}){flag}")
