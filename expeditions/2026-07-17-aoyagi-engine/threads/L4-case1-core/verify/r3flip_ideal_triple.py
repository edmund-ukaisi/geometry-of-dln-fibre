"""
R3-FLIP Gröbner triple (seat-L4D §7 fork, elder council datum).

R3 = flip the SIGN of canonNormalizationOf branch (ii), the layer-(S+1) recoord:
  baked  (+γ): A_{S+1} -> A_{S+1}·Q1^{-1}   (col0 += Σ_r u_{0,r,0}·col_r)   [current def]
  R3-flip(−γ): A_{S+1} -> A_{S+1}·Q1         (col0 -= Σ_r u_{0,r,0}·col_r)
Branch (i) Schur cross-term UNCHANGED in both; A_0 pivot column NOT cleared in either (that's the
whole point — R3 is a pure coordinate SHEAR, no rank-reducing clear).

We build all residuals in ONE common ring {A2, A1(original u1rc), u001, u010, u020, e2, e3}:
  A0_eff (baked/R3):  [[1, u001],[u_{0,r,0}, e_r]]      (pivot col KEPT)
  A0_eff (honest-U):  [[1, u001],[0,        e_r]]       (Q1 clears pivot col; U puts u001 in row0)
  A1_eff (baked/hon): A1·Q1^{-1}  (+γ);   A1_eff (R3):  A1·Q1  (−γ)
  residual = A2·A1_eff·A0_eff  (or A1_eff·A0_eff when N=2).
Three questions: (a) <R3 residual> = <honest> as IDEALS? (b) does R3's residual monomialise
(the col-0 leakage cancels to the clean deeper coord)? (c) is the R3 shear unipotent (M_{s,k})?
"""
import sympy as sp


def resid(d, mode):
    """mode in {baked, r3, honestU, honest0}. Returns (entries, ring_syms, A0_block, A1_eff)."""
    N = len(d) - 1
    d0, d1, d2 = d[0], d[1], d[2]
    assert d0 == 2
    u001 = sp.Symbol("u001")
    col = {r: sp.Symbol(f"u0{r}0") for r in range(1, d1)}          # pivot-column coords u_{0,r,0}
    e = {r: sp.Symbol(f"e{r+1}") for r in range(1, d1)}           # Schur exceptionals e2,e3,...
    A1 = sp.Matrix(d2, d1, lambda r, c: sp.Symbol(f"u1{r}{c}"))    # ORIGINAL layer-1 entries
    # A1_eff: Q1^{-1} = I + Σ_r u_{0,r,0} E_{r,0}  (col0 += Σ u0r0·col_r); Q1 = I − (that)
    sgn = -1 if mode == "r3" else +1
    A1_eff = A1.copy()
    for r in range(1, d1):
        A1_eff[:, 0] = A1_eff[:, 0] + sgn * col[r] * A1[:, r]
    # A0_eff (d1 x d0)
    B = sp.zeros(d1, d0)
    B[0, 0] = 1
    B[0, 1] = 0 if mode == "honest0" else u001
    for r in range(1, d1):
        B[r, 1] = e[r]
        B[r, 0] = 0 if mode in ("honestU", "honest0") else col[r]
    P = A1_eff * B                                                # d2 x d0
    for L in range(2, N):
        AL = sp.Matrix(d[L + 1], d[L], lambda r, c: sp.Symbol(f"u{L}{r}{c}"))
        P = AL * P
    ents = [sp.expand(P[i, j]) for i in range(P.rows) for j in range(P.cols)]
    syms = set()
    for g in ents:
        syms |= g.free_symbols
    return ents, sorted(syms, key=str), B, A1_eff


def ideal_equal(A, B, ring, label):
    A = [g for g in map(sp.expand, A) if g != 0]
    B = [g for g in map(sp.expand, B) if g != 0]
    GA = sp.groebner(A, *ring, order="grevlex")
    GB = sp.groebner(B, *ring, order="grevlex")
    ab = all(GB.reduce(g)[1] == 0 for g in A)
    ba = all(GA.reduce(g)[1] == 0 for g in B)
    print(f"    [{label}]  ⊆:{ab}  ⊇:{ba}  EQUAL: {ab and ba}")
    return ab and ba


def unipotent_r3(d):
    """R3 shear on the FULL flat coords (ed1, pivot (0,0)): is u -> u+φ_flip det-1 + triangular?"""
    N = len(d) - 1
    u = {(L, r, c): sp.Symbol(f"v{L}{r}{c}") for L in range(N) for r in range(d[L + 1]) for c in range(d[L])}

    def rd(S, row, cc):
        return u[(S, row, cc)] if (0 <= S < N and 0 <= row < d[S + 1] and 0 <= cc < d[S]) else sp.Integer(0)
    a, b = 0, 0
    phi = {}
    for (L, r, c) in u:
        if L == 0 and r != a and c != b and 0 <= r and 0 <= c:
            phi[(L, r, c)] = -rd(0, r, b) * rd(0, a, c)
        elif L == 1 and c == a:
            phi[(L, r, c)] = -sum((rd(0, i, b) * rd(1, r, i) for i in range(d[1]) if i != c), sp.Integer(0))  # −γ FLIP
        else:
            phi[(L, r, c)] = sp.Integer(0)
    keys = list(u.keys())
    psi = [u[k] + phi[k] for k in keys]
    J = sp.Matrix([[sp.diff(p, u[k2]) for k2 in keys] for p in psi])
    modified = {k for k in keys if phi[k] != 0}
    tri = all(phi[k].free_symbols.isdisjoint({u[m] for m in modified}) for k in keys)
    detJ = sp.expand(J.det())
    print(f"    R3 shear: det J = {detJ}, triangular(modified⊥support): {tri}  => globally invertible: {detJ == 1 and tri}")


for d in [(2, 2, 2, 2), (2, 3, 2), (2, 3, 2, 2)]:
    print("=" * 80)
    print(f"d = {d}")
    baked, ring_b, Bb, _ = resid(d, "baked")
    r3, ring_r, Br3, A1e = resid(d, "r3")
    honU, _, BhU, _ = resid(d, "honestU")
    hon0, _, Bh0, _ = resid(d, "honest0")
    ring = sorted(set(ring_b) | set(ring_r), key=str)
    print("  residual entries (col-0 = clean deeper coord if leakage cancels):")
    print("   baked   :", baked)
    print("   R3-flip :", r3)
    print("   honestU :", honU)
    print("  A0_eff block  baked/R3 =", Bb.tolist(), "  honestU =", BhU.tolist())
    print("  (a) IDEAL-equality:")
    ideal_equal(r3, honU, ring, "R3   vs honest-with-U")
    ideal_equal(r3, hon0, ring, "R3   vs honest-no-U ")
    ideal_equal(baked, honU, ring, "baked vs honest-with-U")
    ideal_equal(r3, baked, ring, "R3   vs baked        ")
    print("  (b) monomialisation — does R3 residual col-0 reduce to the clean deeper coord?")
    print("      R3 col-0 entries:", [r3[i] for i in range(len(r3)) if i % d[0] == 0])
    print("  (c) M_{s,k} / unipotency of the R3 shear:")
    unipotent_r3(d)
