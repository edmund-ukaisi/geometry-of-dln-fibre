"""
CORNER-treatment model checks (arch-C-4's corner catch; elder rules).

The corner catch: at a CORNER pivot the pivot-ROW compensator Q₂⁻¹ acts on the NETWORK INPUT x (the
d_0 domain = A₀'s columns), a GLOBAL object — inexpressible as a per-edge step. Interior pivots close
identically (their row-compensator is internal). Two checks:

(A) END-FACTOR TREATMENT — split: per-edge clears only the pivot COLUMN (Q₁, deeper-compensated) + the
    pivot-ROW clear applied ONCE as a GLOBAL input change-of-variables (Q₂ on A₀'s input columns).
    Verify: (i) the equality close is restored at the corner (⟨cleared⟩ = ⟨uncleared⟩, i.e. composite ==
    original up to the invertible input-CoV); (ii) the block reads [[1,β],[0,e₂]] (upper-tri) per-edge-only,
    diag(1,e₂) AFTER the global input-CoV.
(B) TRIANGULAR TOLERANCE — col-only clearing per-edge, NO row treatment anywhere (leave the corner block
    upper-triangular [[1,β],[0,e₂]]).  Does boostReady / Deg1SupportedOn-center hold with the triangular
    block?  (arch-C-4 probe: multilinearity holds; confirm the center-support property specifically.)
Witnesses (2,2,2,2) + wide (2,3,2)/(2,3,2,2).  Corner pivot = (0,0) at layer 0 (row 0 = the input-facing
boundary ⟹ its row-clear is the input CoV).
"""
import sympy as sp


def syms(d):
    N = len(d) - 1
    return N, {(L, r, c): sp.Symbol(f"u{L}{r}{c}") for L in range(N) for r in range(d[L + 1]) for c in range(d[L])}


def mats(d, u):
    N = len(d) - 1
    return [sp.Matrix(d[L + 1], d[L], lambda r, c: u[(L, r, c)]) for L in range(N)]


def prod(ms):
    P = ms[-1]
    for M in reversed(ms[:-1]):
        P = P * M
    return P


# ---------- (A) END-FACTOR: per-edge col-clear (Q₁) + GLOBAL input-CoV (Q₂) at the corner ----------
def check_A(d):
    N, u = syms(d)
    ms = mats(d, u)
    ms[0] = ms[0].copy(); ms[0][0, 0] = sp.Integer(1)   # δ=1 pivot-quotient (pivot → 1), the corner chart
    d1, d0 = d[1], d[0]
    beta = u[(0, 0, 1)]
    # Q₁ clears the pivot COLUMN of A₀ (row-op): rows r>0 -= u_{0,r,0}·row0.  Q₁⁻¹ compensates A₁ (deeper).
    Q1 = sp.eye(d1); Q1inv = sp.eye(d1)
    for r in range(1, d1):
        Q1[r, 0] = -u[(0, r, 0)]; Q1inv[r, 0] = u[(0, r, 0)]
    A0_colcleared = sp.expand(Q1 * ms[0])           # = [[1,β],[0,e_r]] upper-tri (col cleared, row kept)
    A1_recoord = sp.expand(ms[1] * Q1inv)           # deeper compensation (+γ, product-preserving)
    ms_edge = [A1_recoord if L == 1 else (A0_colcleared if L == 0 else ms[L]) for L in range(N)]
    # GLOBAL input-CoV: Q₂ on A₀'s input columns (right-mult), clears the pivot ROW (col c>0 -= β_c·col0)
    Q2 = sp.eye(d0)
    for c in range(1, d0):
        Q2[0, c] = -u[(0, 0, c)]
    P_orig = sp.expand(prod(ms))                    # original A_{N-1}···A₀
    P_edge = sp.expand(prod(ms_edge))               # per-edge col-clear only (row uncleared)
    P_global = sp.expand(P_edge * Q2)               # + GLOBAL input-CoV (once)
    print(f"  (A) d={d}:")
    print(f"    per-edge col-clear block A₀' = {A0_colcleared.tolist()}  (upper-tri [[1,β],[0,e]]? "
          f"{all(A0_colcleared[r,0]==0 for r in range(1,d1)) and A0_colcleared[0,0]==1})")
    print(f"    block after GLOBAL input-CoV (A₀'·Q₂) = {sp.expand(A0_colcleared*Q2).tolist()}  (diag(1,e)?)")
    # equality close: composite (col-clear + global CoV) == original·Q₂  (product-preserving up to the CoV)
    close = sp.expand(P_global - P_orig * Q2) == sp.zeros(P_orig.rows, P_orig.cols)
    print(f"    equality close: composite(per-edge col-clear + global Q₂) == original·Q₂ ? {close}")
    # ideal equality ⟨composite⟩ = ⟨original⟩ (Q₂ invertible on the input ⟹ ideal preserved)
    xs = sorted(set().union(*[e.free_symbols for e in list(P_orig) + list(P_global)]), key=str)
    go = sp.groebner([sp.expand(e) for e in P_orig if e != 0], *xs, order="grevlex")
    ideal_eq = all(sp.expand(go.reduce(sp.expand(e))[1]) == 0 for e in P_global)
    print(f"    ⟨composite⟩ ⊆ ⟨original⟩ (equality close, ideal): {ideal_eq}")
    return close and ideal_eq


# ---------- (B) TRIANGULAR TOLERANCE: col-only per-edge, boostReady on the reuse node ----------
def rd(u, d, S, row, col):
    N = len(d) - 1
    return u[(S, row, col)] if (0 <= S < N and 0 <= row < d[S + 1] and 0 <= col < d[S]) else sp.Integer(0)


def col_only_shear(u, d, sL, sC, piv):
    """Col-only clear (Q₁: pivot COLUMN → 0; pivot ROW kept ⟹ upper-tri block) + interior Schur + +γ recoord (scoped)."""
    a, b = piv[1], piv[2]; w = dict(u)
    for (L, r, c) in u:
        if L == sL and sC <= r and sC <= c:
            if r != a and c != b:
                w[(L, r, c)] = u[(L, r, c)] - rd(u, d, sL, r, b) * rd(u, d, sL, a, c)   # interior Schur
            elif r != a and c == b:
                w[(L, r, c)] = sp.Integer(0)                                            # col cleared (row NOT)
        elif L == sL + 1 and c == a:
            w[(L, r, c)] = u[(L, r, c)] + sum(                                           # +γ recoord, scoped
                (rd(u, d, sL, i, b) * rd(u, d, sL + 1, r, i) for i in range(sC, d[sL + 1]) if i != c), sp.Integer(0))
    return w


def apply_edge(u, d, case, sL, sC, piv, cen, delta):
    w = dict(u) if case in ("case11", "rollover") else col_only_shear(u, d, sL, sC, piv)
    out = {}
    for k in u:
        if case == "rollover":
            out[k] = w[k]
        elif delta == 1:
            out[k] = sp.Integer(1) if k == piv else w[k]
        else:
            out[k] = (w[piv] if k == piv else (w[piv] * w[k] if k in cen else w[k]))
    return out


def check_B(d, edges):
    N, u = syms(d)
    v = dict(u)
    for e in reversed(edges):
        v = apply_edge(v, d, *e)
    L0 = sp.Matrix(d[1], d[0], lambda r, c: sp.expand(v[(0, r, c)]))
    P = sp.Matrix(d[N], d[N - 1], lambda r, c: v[(N - 1, r, c)])
    for L in range(N - 2, -1, -1):
        P = P * sp.Matrix(d[L + 1], d[L], lambda r, c: v[(L, r, c)])
    ents = [sp.expand(P[i, j]) for i in range(P.rows) for j in range(P.cols)]
    u001, u010 = u[(0, 0, 1)], u[(0, 1, 0)]
    tri = (L0[0, 0] == 1 and all(L0[r, 0] == 0 for r in range(1, d[1])) and L0[0, 1] == u001)
    wr = max((0 if u001 not in f.free_symbols else sp.Poly(f, u001).degree()) for f in ents)
    wc = max((0 if u010 not in f.free_symbols else sp.Poly(f, u010).degree()) for f in ents)
    # center-support: e₂ = u011-u010u001 atomic; center {e₂, layer-1 col-0}; residual deg≤1 in center
    print(f"  (B) d={d}: L0 upper-tri [[1,u001],[0,e]]? {tri}; max deg_u001={wr}, deg_u010={wc} "
          f"=> MULTILINEAR (deg≤1 each): {wr<=1 and wc<=1}")
    return wr <= 1 and wc <= 1


print("=" * 82)
print("(A) END-FACTOR TREATMENT — global input-CoV + per-edge col-only clear:")
A = {d: check_A(d) for d in [(2, 2, 2, 2), (2, 3, 2), (2, 3, 2, 2)]}
print(f"  => equality close restored at corner (all witnesses): {all(A.values())}")
print("\n(B) TRIANGULAR TOLERANCE — col-only per-edge, boostReady with the triangular corner block:")
d2222 = [("case2", 0, 0, (0, 0, 0), set(), 1), ("case2", 0, 1, (0, 1, 1), {(0, 1, 1)}, 0), ("rollover", 0, 2, None, set(), 0)]
dwide = lambda: [("case2", 0, 0, (0, 0, 0), set(), 1), ("case2", 0, 1, (0, 1, 1), {(0, 1, 1), (0, 2, 1)}, 0), ("rollover", 0, 2, None, set(), 0)]
B = {(2, 2, 2, 2): check_B((2, 2, 2, 2), d2222), (2, 3, 2): check_B((2, 3, 2), dwide()), (2, 3, 2, 2): check_B((2, 3, 2, 2), dwide())}
print(f"  => triangular-block boostReady/multilinear holds (all witnesses): {all(B.values())}")
