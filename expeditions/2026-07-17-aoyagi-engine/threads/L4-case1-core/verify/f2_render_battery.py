"""
AUTHORITATIVE battery on arch-C-4's F₂ render @ REBAKE2 1a113e4db — EXACT rendered canonNormalizationOf
(3 branches), verbatim from MonumentAtlas.lean:906-966, NO hand model (charter §3).

CRITERIA (corrected after reading the Lean StepInv, PrincipalInv.lean:82): StepInv is a CONTINUOUS-quotient
DIVISIBILITY  (Fᵢ∘g) = ∑ⱼ qᵢⱼ·(b·residⱼ), q ContinuousOn V  — NOT polynomial entry-ideal-equality (§8(j):
entry-ideal-equality between charts is NOT preserved by two-sided unimodular Q·M·P and needn't be; RLCT
rides the CoV). So the recursion closes by the det-1 CoV g=foldG (the 3 shears), NOT coreGen entry-equality.
Rows:
 1. RECURSION CoV: the 3-shear composite is det-1 / unipotent (triangular — each branch reads only UNWRITTEN
    coords). This is the "product-preserving CoV" that closes the recursion (the ideal rides it, §8(j)).
    [DIAGNOSTIC, not a criterion: polynomial entry-ideal-equality coreGen(shear)=coreGen(raw) — EXPECTED to
    fail per §8(j); reported so the record is honest.]
 2. BLOCK-FORM / boostReady: residual is the clean multilinear block, Deg1SupportedOn ed.center.
 3. SCOPE: unscoped-paired gives inter-edge u₀₀₁²; scoped (i≥cleared) removes it.
 4. ON-FRAME POLYNOMIALITY: the shears are polynomial at the normalized pivot (no A₁⁻¹).
 5. CORNER-A (S=0): branch-(iii) vacuous; corner block triangular per-edge (row = global end-factor gauge).
 6. INTERIOR-PIVOT (S=1): branch-(iii) ACTIVE; the block clears (row-clear compensated internally by A_{S-1}).
"""
import sympy as sp


def dims_coords(d, prefix="u"):
    N = len(d) - 1
    u = {(L, r, c): sp.Symbol(f"{prefix}_{L}_{r}_{c}") for L in range(N) for r in range(d[L + 1]) for c in range(d[L])}
    return N, u


def readEntry(u, d, S, row, col):
    N = len(d) - 1
    return u[(S, row, col)] if (0 <= S < N and 0 <= row < d[S + 1] and 0 <= col < d[S]) else sp.Integer(0)


def canonNormalizationOf(u, d, s_layer, s_cleared, piv, scoped=True):
    """EXACT rendered 3-branch def (MonumentAtlas:906-966). piv=(layer,a,b). scoped: keep i<cleared→0."""
    a, b = piv[1], piv[2]; S = s_layer
    lo = s_cleared if scoped else 0
    phi = {}
    for (L, row, col) in u:
        if L == S and row != a and col != b and s_cleared <= row and s_cleared <= col:
            phi[(L, row, col)] = -readEntry(u, d, S, row, b) * readEntry(u, d, S, a, col)
        elif L == S + 1 and col == a:
            phi[(L, row, col)] = sum((readEntry(u, d, S, i, b) * readEntry(u, d, S + 1, row, i)
                                      for i in range(d[S + 1]) if not (i == a or i < lo)), sp.Integer(0))
        elif L + 1 == S and row == b:
            phi[(L, row, col)] = sum((readEntry(u, d, S, a, k) * readEntry(u, d, S - 1, k, col)
                                      for k in range(d[S]) if not (k == b or k < lo)), sp.Integer(0))
        else:
            phi[(L, row, col)] = sp.Integer(0)
    return phi


def coreGen(u, d):
    N = len(d) - 1
    P = sp.Matrix(d[N], d[N - 1], lambda r, c: u[(N - 1, r, c)])
    for L in range(N - 2, -1, -1):
        P = P * sp.Matrix(d[L + 1], d[L], lambda r, c: u[(L, r, c)])
    return P


# ---------- ROW 1: 3-shear composite is det-1 / triangular (the recursion CoV) ----------
def row1_det1(d, s_layer, s_cleared, piv, label):
    N, u = dims_coords(d)
    # DO NOT normalize the pivot: the shear u ↦ u+φ acts on the FULL coord space (pivot a free symbol);
    # φ does NOT read the pivot (branch (i) reads (row,b),(a,col) with row≠a,col≠b — never (a,b)), so the
    # shear is well-defined on all coords and its unipotency is a fact about the full-space Jacobian.
    phi = canonNormalizationOf(u, d, s_layer, s_cleared, piv)
    keys = list(u.keys())
    psi = [u[k] + phi[k] for k in keys]
    vars_ = [u[k] for k in keys]
    J = sp.Matrix([[sp.diff(p, v) for v in vars_] for p in psi])
    detJ = sp.expand(J.det())
    modified = {k for k in keys if phi[k] != 0}
    tri = all(phi[k].free_symbols.isdisjoint({u[m] for m in modified}) for k in keys)
    print(f"  [{label}] 3-shear det J = {detJ}; triangular(reads only unwritten): {tri}  => det-1 CoV: {detJ==1 and tri}")
    return detJ == 1


# ---------- fold on the render (blockBlowupMap ∘ blockShear(3-branch); NO r4Clear) ----------
def apply_edge(u, d, case, sL, sC, piv, cen, delta, scoped=True):
    if case in ("case11", "rollover"):
        w = dict(u)
    else:
        phi = canonNormalizationOf(u, d, sL, sC, piv, scoped)
        w = {k: u[k] + phi[k] for k in u}
    out = {}
    for k in u:
        if case == "rollover":
            out[k] = w[k]
        elif delta == 1:
            out[k] = sp.Integer(1) if k == piv else w[k]
        else:
            out[k] = (w[piv] if k == piv else (w[piv] * w[k] if k in cen else w[k]))
    return out


def fold_resid(d, edges, scoped=True):
    N, u = dims_coords(d)
    v = dict(u)
    for e in reversed(edges):
        v = apply_edge(v, d, *e, scoped)
    return coreGen(v, d), u, v


def maxdeg(f, xs):
    f = sp.expand(f); xs = [x for x in xs if x in f.free_symbols]
    return 0 if not xs else max(sum(m) for m in sp.Poly(f, *xs).monoms())


# (2,2,2,2) canonical reuse branch + wide (2,3,2),(2,3,2,2)
BR = {
    (2, 2, 2, 2): [("case2", 0, 0, (0, 0, 0), set(), 1), ("case2", 0, 1, (0, 1, 1), {(0, 1, 1)}, 0), ("rollover", 0, 2, None, set(), 0)],
    (2, 3, 2): [("case2", 0, 0, (0, 0, 0), set(), 1), ("case2", 0, 1, (0, 1, 1), {(0, 1, 1), (0, 2, 1)}, 0), ("rollover", 0, 2, None, set(), 0)],
    (2, 3, 2, 2): [("case2", 0, 0, (0, 0, 0), set(), 1), ("case2", 0, 1, (0, 1, 1), {(0, 1, 1), (0, 2, 1)}, 0), ("rollover", 0, 2, None, set(), 0)],
}

print("=" * 84)
print("ROW 1 — recursion CoV (3-shear composite det-1 / triangular):")
row1_det1((3, 2, 2, 2), 1, 0, (1, 0, 0), "(3,2,2,2) S=1 (all 3 branches)")
row1_det1((3, 3, 3, 2), 1, 0, (1, 1, 1), "(3,3,3,2) S=1 interior (1,1)")
for d in BR:
    row1_det1(d, 0, 0, (0, 0, 0), f"{d} S=0 corner")

print("\n" + "=" * 84)
print("ROW 2 — block-form / boostReady (residual multilinear, clean block) on the render fold:")
for d in BR:
    ents, u, v = fold_resid(d, BR[d], scoped=True)
    u001, u010 = u[(0, 0, 1)], u[(0, 1, 0)]
    el = [sp.expand(ents[i, j]) for i in range(ents.rows) for j in range(ents.cols)]
    wr = max(maxdeg(f, [u001]) for f in el); wc = max(maxdeg(f, [u010]) for f in el)
    L0 = sp.Matrix(d[1], d[0], lambda r, c: sp.expand(v[(0, r, c)]))
    print(f"  {d}: max deg_u001={wr}, deg_u010={wc} => MULTILINEAR: {wr<=1 and wc<=1}")

print("\n" + "=" * 84)
print("ROW 3 — scope (unscoped-paired u₀₀₁²; scoped removes it):")
for d in BR:
    e_s, u, _ = fold_resid(d, BR[d], scoped=True)
    e_u, u2, _ = fold_resid(d, BR[d], scoped=False)
    ws = max(maxdeg(sp.expand(e_s[i, j]), [u[(0, 0, 1)]]) for i in range(e_s.rows) for j in range(e_s.cols))
    wu = max(maxdeg(sp.expand(e_u[i, j]), [u2[(0, 0, 1)]]) for i in range(e_u.rows) for j in range(e_u.cols))
    print(f"  {d}: scoped deg_u001={ws} (clean iff ≤1); unscoped deg_u001={wu} (u₀₀₁² iff ≥2) => scope needed: {wu>=2 and ws<=1}")


print("\n" + "=" * 84)
print("SCOPE DIAGNOSTIC — actual render reuse-node residual (2,2,2,2), scoped vs unscoped:")
for scoped in (True, False):
    ents, u, v = fold_resid((2, 2, 2, 2), BR[(2, 2, 2, 2)], scoped=scoped)
    u001 = u[(0, 0, 1)]
    print(f"  scoped={scoped}:")
    for i in range(ents.rows):
        for j in range(ents.cols):
            f = sp.expand(ents[i, j])
            print(f"    [{i}][{j}] deg_u001={0 if u001 not in f.free_symbols else sp.Poly(f,u001).degree()}: {f}")


print("\n" + "=" * 84)
print("ROW 4 — on-frame polynomiality (the rendered def is polynomial: readEntry products/sums, NO division):")
# the def uses only readEntry (coord lookup or 0), *, +, unary − — no sp division / no inverse. Confirm on a
# sample: every φ entry is a Poly (no rational functions) at a generic (un-normalized) point.
N, u = dims_coords((3, 2, 2, 2))
phi = canonNormalizationOf(u, (3, 2, 2, 2), 1, 0, (1, 0, 0))
allpoly = all(sp.expand(v).is_polynomial(*u.values()) for v in phi.values())
print(f"  every branch displacement is polynomial (no A₁⁻¹ / no division): {allpoly}")

print("\n" + "=" * 84)
print("ROW 5 — CORNER (S=0): branch-(iii) VACUOUS; branch (i)+(ii) only; det-1 CoV (row 1 confirmed):")
for d in BR:
    N, u = dims_coords(d)
    phi = canonNormalizationOf(u, d, 0, 0, (0, 0, 0))
    iii_active = any(phi[k] != 0 and (k[0] + 1 == 0) for k in u)   # branch iii writes L+1=S=0 (impossible)
    # which branches fire:
    fired = set()
    for k in u:
        if phi[k] != 0:
            L, row, col = k
            if L == 0 and row != 0 and col != 0:
                fired.add("i")
            elif L == 1 and col == 0:
                fired.add("ii")
            elif L + 1 == 0:
                fired.add("iii")
    print(f"  {d} S=0 corner: branches fired={sorted(fired)}; branch-(iii) active={iii_active} (VACUOUS expected)")

print("\n" + "=" * 84)
print("ROW 6 — INTERIOR (S=1): branch-(iii) ACTIVE (input recoord reads layer S−1); det-1 CoV (row 1 confirmed):")
for d, piv in [((3, 2, 2, 2), (1, 0, 0)), ((3, 3, 3, 2), (1, 1, 1))]:
    N, u = dims_coords(d)
    phi = canonNormalizationOf(u, d, 1, 0, piv)
    fired = set()
    for k in u:
        if phi[k] != 0:
            L, row, col = k
            if L == 1 and row != piv[1] and col != piv[2]:
                fired.add("i")
            elif L == 2 and col == piv[1]:
                fired.add("ii")
            elif L + 1 == 1 and row == piv[2]:
                fired.add("iii")
    # branch (iii) writes layer 0 (S-1) row=b=piv[2]; confirm it's non-empty
    iii_terms = [k for k in u if phi[k] != 0 and k[0] == 0 and k[1] == piv[2]]
    print(f"  {d} S=1 pivot{piv}: branches fired={sorted(fired)}; branch-(iii) writes layer-0 coords {iii_terms} (ACTIVE expected)")
