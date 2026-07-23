"""
DECISIVE r4Clear-bridge soundness WITH branch-(ii) recoord (seat-L4D's owed Gröbner check).

seat-L4D's NAIVE bridge (r4clear_bridge_soundness.py, RAW A₁, no recoord) found uncleared ∈ ⟨cleared⟩
FALSE on the E_J (col-0) entries: remainder γ·(A₂A₁)_{·,1}. That model OMITS branch-(ii)'s A₁ recoord
(A₁ → A₁·Q₁, the γ/pivot-COLUMN handler). The failing remainder is a γ·(2nd col) term, so branch-(ii)
plausibly absorbs it. This is the DEFINITIVE check: apply the §8(m) recoord to A₁ in BOTH uncleared and
cleared (the recoord is part of σu, common to both; r4Clear is the only difference), then Gröbner-test
uncleared ∈ ⟨cleared⟩ over ℚ[u].

  uncleared A₀ = pivot cross intact ([[1,β],[γ_i,e_i]]);  cleared A₀ = cross zeroed ([[1,0],[0,e_i]]).
  A₁' = A₁·Q₁ (branch-ii): §8(m) −γ, SCOPED cleared≤i.  For ed1 (cleared=0) scope = all i≠pivotcol.
  coreGen = A_{N-1}···A₁·A₀.
VERDICT: recoord absorbs the E_J remainder ⟹ bridge sound (bounded +1 frontier). Persists ⟹ §7 obstruction.
"""
import sympy as sp


def make(d):
    N = len(d) - 1
    u = {(L, r, c): sp.Symbol(f"u{L}{r}{c}") for L in range(N) for r in range(d[L + 1]) for c in range(d[L])}
    return N, u


def A1_recoord(d, u, sign, scoped, cleared):
    """A₁' = A₁·Q₁: branch-(ii) recoord of layer 1 for the ed1 pivot (0,0). col-0 += sign·Σ_i u_{0,i,0}·col_i.
    §8(m): sign=-1, scoped => i ≥ cleared. For ed1 cleared=0 the scope is all i≠0."""
    d1, d2 = d[1], d[0]  # A1 is d[2] x d[1]
    r2 = d[2]
    A1 = sp.Matrix(r2, d[1], lambda r, c: u[(1, r, c)])
    lo = cleared if scoped else 0
    A1p = A1.copy()
    for r in range(r2):
        A1p[r, 0] = A1[r, 0] + sign * sum((u[(0, i, 0)] * A1[r, i] for i in range(lo, d[1]) if i != 0), sp.Integer(0))
    return A1p


def blocks(d, u):
    """uncleared / cleared layer-0 A₀ (d[1] x d[0]) for the ed1 pivot (0,0). d[0]=2 assumed (single interior col)."""
    d1 = d[1]
    beta = u[(0, 0, 1)]
    A0u = sp.zeros(d1, 2); A0c = sp.zeros(d1, 2)
    A0u[0, 0] = 1; A0c[0, 0] = 1
    A0u[0, 1] = beta                       # pivot row (β) — cleared zeroes it
    for r in range(1, d1):
        gamma = u[(0, r, 0)]               # pivot column (γ_r)
        e = u[(0, r, 1)] - gamma * beta    # interior Schur e_r
        A0u[r, 0] = gamma; A0u[r, 1] = e
        A0c[r, 0] = 0;     A0c[r, 1] = e
    return A0u, A0c


def coreGen_from(d, u, A1p, A0):
    N = len(d) - 1
    P = A1p * A0                                    # (d2 x d1)(d1 x d0)
    for L in range(2, N):
        AL = sp.Matrix(d[L + 1], d[L], lambda r, c: u[(L, r, c)])
        P = AL * P
    return [sp.expand(P[i, j]) for i in range(P.rows) for j in range(P.cols)], P.rows, P.cols


def membership(d, sign, scoped, label):
    N, u = make(d)
    A1p = A1_recoord(d, u, sign, scoped, cleared=0)
    A0u, A0c = blocks(d, u)
    Pu, nr, nc = coreGen_from(d, u, A1p, A0u)
    Pc, _, _ = coreGen_from(d, u, A1p, A0c)
    xs = sorted(set().union(*[g.free_symbols for g in Pu + Pc]), key=str)
    gb = sp.groebner([g for g in Pc if g != 0], *xs, order="grevlex")
    print(f"  [{label}]")
    allok = True
    for idx, g in enumerate(Pu):
        i, j = idx // nc, idx % nc
        rem = sp.expand(gb.reduce(sp.expand(g))[1])
        member = rem == 0
        allok = allok and member
        col = "col-0/E_J" if j == 0 else "col-1/D_J"
        print(f"    P_uncl[{i}][{j}] ({col}) member={member}" + ("" if member else f"  rem={rem}"))
    print(f"    => uncleared ⊆ ⟨cleared⟩ ALL entries: {allok}")
    return allok


for d in [(2, 2, 2, 2), (2, 3, 2), (2, 3, 2, 2)]:
    print("=" * 80)
    print(f"d = {d}")
    print(" NAIVE reference (no recoord, sign=0):")
    membership(d, 0, False, "no recoord")
    print(" §8(m) recoord (sign=-1, scoped i≥cleared):")
    r_m = membership(d, -1, True, "-γ scoped (§8(m))")
    print(" +γ recoord (sign=+1, scoped) — sign sanity:")
    membership(d, +1, True, "+γ scoped")
    print(" -γ UNscoped (sign=-1, all i) — scope sanity:")
    membership(d, -1, False, "-γ unscoped")


# ============================================================================================
# FULL-FAITHFUL contrast: does the product-preserving R4 (Q1·A0·Q2 + BOTH compensators A1·Q1^{-1}
# and Q2^{-1} input-side) satisfy the bridge, isolating the missing Q2^{-1} as the fix? (2,2,2,2)
# ============================================================================================
print("\n" + "#" * 80)
print("FULL-FAITHFUL contrast (2,2,2,2): render r4Clear (lossy) vs faithful Q1·A0·Q2 (product-preserving)")
u = {(0,0,1):sp.Symbol('u001'),(0,1,0):sp.Symbol('u010'),(0,1,1):sp.Symbol('u011')}
b, g, u011 = u[(0,0,1)], u[(0,1,0)], u[(0,1,1)]
A2 = sp.Matrix(2,2,lambda r,c: sp.Symbol(f'u2{r}{c}'))
A1 = sp.Matrix(2,2,lambda r,c: sp.Symbol(f'u1{r}{c}'))
e2 = u011 - g*b
A0_raw  = sp.Matrix([[1,b],[g,u011]])                       # raw block (pivot=1)
uncleared = sp.expand(A2*A1*A0_raw)                          # = the parent residual (raw product)
Q1 = sp.Matrix([[1,0],[-g,1]]); Q1inv = sp.Matrix([[1,0],[g,1]])
Q2 = sp.Matrix([[1,-b],[0,1]]); Q2inv = sp.Matrix([[1,b],[0,1]])
# (A) full faithful: A0 -> Q1·A0·Q2 = diag(1,e2); A1 -> A1·Q1^{-1}; input -> Q2^{-1}
faithful_clear = sp.expand(A2 * (A1*Q1inv) * (Q1*A0_raw*Q2) * Q2inv)
print(f"  (A) faithful cleared == uncleared (product-preserving)?  {sp.expand(faithful_clear - uncleared) == sp.zeros(2,2)}")
print("      => ⟨faithful cleared⟩ = ⟨uncleared⟩, so uncleared ∈ ⟨cleared⟩ TRIVIALLY (bridge holds).")
# (B) render r4Clear: A1 -> A1·Q1 (−γ recoord), A0 -> diag(1,e2) [literal cross-zero], NO Q2^{-1}
render_clear = sp.expand(A2 * (A1*Q1) * sp.diag(1,e2))
xs = sorted(set().union(*[f.free_symbols for f in list(uncleared)+list(render_clear)]), key=str)
gbR = sp.groebner([f for f in list(render_clear) if f!=0], *xs, order='grevlex')
okB = all(sp.expand(gbR.reduce(sp.expand(uncleared[i,j]))[1])==0 for i in range(2) for j in range(2))
print(f"  (B) render r4Clear (−γ recoord, diag literal-zero, NO Q2^-1): uncleared ∈ ⟨cleared⟩?  {okB}")
# (C) render r4Clear + ONLY Q2^{-1} input added (keep −γ recoord + literal-zero) — does the input alone fix?
renderC = sp.expand(A2 * (A1*Q1) * sp.diag(1,e2) * Q2inv)
gbC = sp.groebner([f for f in list(renderC) if f!=0], *xs, order='grevlex')
okC = all(sp.expand(gbC.reduce(sp.expand(uncleared[i,j]))[1])==0 for i in range(2) for j in range(2))
print(f"  (C) render + Q2^-1 input (keep −γ recoord + literal-zero): uncleared ∈ ⟨cleared⟩?  {okC}")
# (D) faithful recoord (+γ = Q1^{-1}) + literal-zero diag + Q2^{-1} input — the +γ vs −γ isolation
renderD = sp.expand(A2 * (A1*Q1inv) * sp.diag(1,e2) * Q2inv)
gbD = sp.groebner([f for f in list(renderD) if f!=0], *xs, order='grevlex')
okD = all(sp.expand(gbD.reduce(sp.expand(uncleared[i,j]))[1])==0 for i in range(2) for j in range(2))
print(f"  (D) +γ recoord (Q1^-1) + diag literal-zero + Q2^-1 input: uncleared ∈ ⟨cleared⟩?  {okD}")
print("\n  READ: (A) faithful = uncleared (holds). (B) render-as-is FAILS. (C)/(D) isolate whether the")
print("  input-side Q2^-1 and/or the recoord SIGN is the missing piece — the precise §7 fold-touch.")
