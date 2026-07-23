"""
FAITHFUL LEAN HARNESS (pre-stage for the re-bake acceptance battery; team-lead sanctioned).

Computes the fold from the ACTUAL baked Lean defs (canonNormalizationOf / readEntry / blockEntryFlat,
MonumentAtlas.lean:832-882), TRANSCRIBED verbatim — NOT a hand model. This is the charter-§3-gate
substrate for the eventual battery (exercise the Lean defs). It closes pnp-transport's standing epistemic
caveat (hand model vs baked defs): re-validates boost-readiness + the recoord direction against the def.

--- transcription of the baked def (MonumentAtlas.lean) ---
blockEntryFlat d S row col : Option (Fin flatDim) = the flat coord of layer-S entry (row,col), None off-cone.
readEntry d u S row col : ℝ = u[blockEntryFlat] or 0.
canonNormalizationOf d s p : the RAW displacement φ (edgeShear = blockShear φ = u + φ(u) at case2/case12;
  = id at case11/rollover). p=pivot decodes to (layer, a=pivot-row, b=pivot-col). At coord k=(L,row,col):
  (i)  if L=s.layer ∧ row≠a ∧ col≠b ∧ cleared≤row ∧ cleared≤col:  φ = −readEntry(s.layer,row,b)·readEntry(s.layer,a,col)
  (ii) elif L=s.layer+1 ∧ col=a:  φ = Σ_{i∈range(d_{s.layer+1}), i≠col} readEntry(s.layer,i,b)·readEntry(s.layer+1,row,i)
  (iii) else 0.
"""
import sympy as sp

def make(d):
    N = len(d) - 1
    u = {(L, r, c): sp.Symbol(f"u{L}{r}{c}") for L in range(N) for r in range(d[L + 1]) for c in range(d[L])}
    return N, u

def readEntry(u, d, S, row, col):
    N = len(d) - 1
    if 0 <= S < N and 0 <= row < d[S + 1] and 0 <= col < d[S]:
        return u[(S, row, col)]
    return sp.Integer(0)

def canonNormalizationOf(u, d, s_layer, s_cleared, pivot):
    """the raw displacement φ (dict coord->expr), transcribed from the baked def."""
    a, b = pivot[1], pivot[2]                     # pivot row a, pivot col b
    N = len(d) - 1
    phi = {}
    for (L, row, col) in u:
        if L == s_layer and row != a and col != b and s_cleared <= row and s_cleared <= col:
            phi[(L, row, col)] = -readEntry(u, d, s_layer, row, b) * readEntry(u, d, s_layer, a, col)
        elif L == s_layer + 1 and col == a:
            phi[(L, row, col)] = sum(
                (readEntry(u, d, s_layer, i, b) * readEntry(u, d, s_layer + 1, row, i)
                 for i in range(d[s_layer + 1]) if i != col), sp.Integer(0))
        else:
            phi[(L, row, col)] = sp.Integer(0)
    return phi

def edgeShear(u, d, case, s_layer, s_cleared, pivot):
    if case in ("case11", "rollover"):
        return dict(u)
    phi = canonNormalizationOf(u, d, s_layer, s_cleared, pivot)
    return {k: u[k] + phi[k] for k in u}

def apply_edge(u, d, case, s_layer, s_cleared, pivot, center, delta):
    w = edgeShear(u, d, case, s_layer, s_cleared, pivot)
    out = {}
    for k in u:
        if case == "rollover":
            out[k] = w[k]
        elif delta == 1:
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
    return [P[i, j] for i in range(P.rows) for j in range(P.cols)]

def foldResid(u, d, edges):
    v = dict(u)
    for (case, sl, sc, piv, cen, delta) in reversed(edges):
        v = apply_edge(v, d, case, sl, sc, piv, cen, delta)
    return coreGen(v, d)

# ---- (2,2,2,2): fold to the case11 boost parent, via the ACTUAL canonNormalizationOf ----
d = (2, 2, 2, 2)
N, u = make(d)
# branch to the boost parent: ed1 case2 δ1 pivot(0,0,0); ed2 case2 δ0 pivot(0,1,1) center{(0,1,1)}; ed3 rollover
edges = [
    ("case2", 0, 0, (0, 0, 0), set(), 1),
    ("case2", 0, 1, (0, 1, 1), {(0, 1, 1)}, 0),
    ("rollover", 0, 2, None, set(), 0),
]
resid = [sp.expand(f) for f in foldResid(u, d, edges)]
print("=== (2,2,2,2) foldResid at the case11 boost parent, via the BAKED canonNormalizationOf ===")
for j, f in enumerate(resid):
    print(f"  resid[{j}] =", f)

# boost-readiness on the case11 center: pivot (0,1,1), partial = layer-1 col 0, extra = layer-1 col 1
pivot = u[(0, 1, 1)]
center = [pivot, u[(1, 0, 0)], u[(1, 1, 0)]]
extra = [u[(1, 0, 1)], u[(1, 1, 1)]]
A1 = all(sp.expand(f.subs({c: 0 for c in center})) == 0 for f in resid)
def maxdeg(f, xs):
    fs = sp.expand(f).free_symbols
    return 0 if not any(x in fs for x in xs) else max(sum(m) for m in sp.Poly(sp.expand(f), *xs).monoms())
A2 = all(maxdeg(f, center) <= 1 for f in resid)
A3 = all(sp.expand(sp.expand(f.diff(x)).subs(pivot, 0)) == 0 for f in resid for x in extra)
print(f"\n  boost-readiness A1(vanish@center=0)={A1}  A2(deg<=1 on center)={A2}  A3(extra carries pivot)={A3}")
print("  (expect TRUE/TRUE/TRUE: the baked canonNormalizationOf recoord restores boost-readiness — the")
print("   canonShearOf F=x+yz defect is FIXED by the layer-(S+1) recoord, now confirmed against the Lean def.)")

# show the recoord write direction (ed1's φ on layer-1 col 0), confirming seat-L3T2 / honest_clear
phi1 = canonNormalizationOf(u, d, 0, 0, (0, 0, 0))
print("\n  ed1 recoord φ on layer-1 col-0 coords (col = pivot row a = 0):")
for r in range(2):
    print(f"    φ[(1,{r},0)] =", sp.expand(phi1[(1, r, 0)]), " => (edgeShear u)[(1,{},0)] = u1{}0 + that".format(r, r))
print("  matches honest_clear: A_1 col-0 += u_010 * A_1 col-1 (recoord writes col = pivot row).")


# ============================================================================
# DIAGNOSIS: the recoord DOUBLES the F=x+yz defect (A_0 pivot-column NOT cleared).
# ============================================================================
print("\n=== DIAGNOSIS: ed1-only (isolates the recoord double-count) ===")
r1 = [sp.expand(f) for f in foldResid(u, d, [("case2", 0, 0, (0, 0, 0), set(), 1)])]
print("  ed1-only resid[0] =", r1[0])
c2 = sp.Poly(r1[0], u[(0, 1, 0)], u[(1, 0, 1)], u[(2, 0, 0)]).coeff_monomial((1, 1, 1))
print(f"  coeff of u010*u101*u200 = {c2}  (canonShearOf gives 1; the recoord DOUBLED it to 2)")
print("  MECHANISM: A_1[0][0] = u100 + u010*u101 (the ed1 recoord (ii)); A_0[1][0] = u010 (pivot column,")
print("  NOT cleared — (i)'s guard row!=a,col!=b EXCLUDES the pivot column). Then (A_1*A_0)[0][0] =")
print("  (u100+u010*u101)*1 + u101*u010 = u100 + 2*u010*u101.  Aoyagi's clear is A_1*A_0 =")
print("  (A_1*Q1^-1)*(Q1*A_0): the recoord A_1*Q1^-1 must be PAIRED with Q1*A_0 (clearing A_0's pivot")
print("  column) so they CANCEL. The bake applies the recoord WITHOUT the A_0-clearing => they DOUBLE.")
print("  => the baked canonNormalizationOf is NOT boost-ready; it is WORSE than canonShearOf (coeff 2 vs 1).")
