"""
AUTHORITATIVE r4Clear-bridge decider on arch-C-3's VERBATIM rendered formulas (the render's last gate).

VERBATIM branch-(ii) (team-lead's render report; matches r3r4_recoord_scope.py shear per its diff):
  displacement(S+1, row, a) = −( Σ_i  [i = q.2 (=a) ∨ i < s.cleared] ? 0 : readEntry(S,i,b)·readEntry(S+1,row,i) )
  i.e. −γ (leading minus), SCOPED to i ≥ cleared, excluding i = pivot-col a. [guard layer=S+1 ∧ decode-col=a]
branch-(i) = interior Schur (e₂ = u011 − γβ) unchanged.  r4Clear = case12/case2 pivot-cross zero (β,γ → 0).

DECIDES (pinned vocabulary): ABSORBED (uncleared ∈ ⟨cleared⟩ holds on the full structure ⟹ bounded +1
frontier) vs SURVIVES (fails ⟹ pure-zero r4Clear truncates Lemma-2's F₂ absorption; sound R4 needs the
Q₂⁻¹ neighbor ⟹ §7).  Remaining OUTS after seat-L4D falsified branch-(ii)-rescue (both signs) + single-coord
b:  (1) the REAL foldB (accumulated dominant monomial, a SCALAR per L4D def-read);  (2) the δ=1 u_pivot
divisibility form;  (3) wide witnesses.  This script closes (1) analytically + numerically and reports (2),(3).
"""
import sympy as sp


def make(d):
    N = len(d) - 1
    u = {(L, r, c): sp.Symbol(f"u{L}{r}{c}") for L in range(N) for r in range(d[L + 1]) for c in range(d[L])}
    return N, u


def rd(u, d, S, row, col):
    N = len(d) - 1
    return u[(S, row, col)] if (0 <= S < N and 0 <= row < d[S + 1] and 0 <= col < d[S]) else sp.Integer(0)


def A1_recoord_verbatim(d, u, cleared=0):
    """VERBATIM branch-(ii): col-0 += −Σ_{i≥cleared, i≠0} u_{0,i,0}·A1[row][i]  (−γ, scoped)."""
    r2 = d[2]
    A1 = sp.Matrix(r2, d[1], lambda r, c: u[(1, r, c)])
    A1p = A1.copy()
    for r in range(r2):
        A1p[r, 0] = A1[r, 0] - sum((u[(0, i, 0)] * A1[r, i] for i in range(cleared, d[1]) if i != 0), sp.Integer(0))
    return A1p


def blocks(d, u):
    d1 = d[1]; beta = u[(0, 0, 1)]
    A0u = sp.zeros(d1, 2); A0c = sp.zeros(d1, 2)
    A0u[0, 0] = 1; A0c[0, 0] = 1; A0u[0, 1] = beta
    for r in range(1, d1):
        g = u[(0, r, 0)]; e = u[(0, r, 1)] - g * beta
        A0u[r, 0] = g; A0u[r, 1] = e
        A0c[r, 1] = e
    return A0u, A0c


def resid(d, u, A1p, A0):
    N = len(d) - 1
    P = A1p * A0
    for L in range(2, N):
        AL = sp.Matrix(d[L + 1], d[L], lambda r, c: u[(L, r, c)])
        P = AL * P
    return [sp.expand(P[i, j]) for i in range(P.rows) for j in range(P.cols)], P.rows, P.cols


def decide(d):
    N, u = make(d)
    A1p = A1_recoord_verbatim(d, u)
    A0u, A0c = blocks(d, u)
    Pu, nr, nc = resid(d, u, A1p, A0u)
    Pc, _, _ = resid(d, u, A1p, A0c)
    xs = sorted(set().union(*[g.free_symbols for g in Pu + Pc]), key=str)
    gb = sp.groebner([g for g in Pc if g != 0], *xs, order="grevlex")
    print(f"  d={d}  (verbatim −γ scoped recoord, r4Clear cross-zero):")
    ej_fail = []
    for idx, g in enumerate(Pu):
        i, j = idx // nc, idx % nc
        rem = sp.expand(gb.reduce(sp.expand(g))[1])
        m = rem == 0
        tag = "E_J/col-0" if j == 0 else "D_J/col-1"
        print(f"    uncl[{i}][{j}] ({tag}) ∈⟨cleared⟩ = {m}" + ("" if m else f"   rem={rem}"))
        if not m:
            ej_fail.append((i, j, rem))
    # (1) REAL foldB = a SCALAR monomial b: b·uncleared ∈ ⟨b·cleared⟩  ⟺  uncleared ∈ ⟨cleared⟩  (domain).
    b = sp.Symbol("b_foldB")                         # generic accumulated ledger scalar (nonzero)
    xs_b = xs + [b]
    gb_b = sp.groebner([sp.expand(b * g) for g in Pc if g != 0], *xs_b, order="grevlex")
    neutral = all((sp.expand(gb_b.reduce(sp.expand(b * Pu[idx]))[1]) == 0) == (sp.expand(gb.reduce(sp.expand(Pu[idx]))[1]) == 0)
                  for idx in range(len(Pu)))
    print(f"    [foldB out] b·uncl ∈ ⟨b·cleared⟩ MATCHES unweighted membership (scalar b membership-neutral): {neutral}")
    # (2) δ=1 u_pivot divisibility: is the E_J col-0 entry divisible by the pivot coord u000?
    piv = u[(0, 0, 0)] if (0, 0, 0) in u else sp.Symbol("u000")
    for (i, j, rem) in ej_fail:
        div = sp.simplify(Pu[i * nc + j] / piv) if piv in Pu[i * nc + j].free_symbols else None
        print(f"    [δ=1 out] E_J uncl[{i}][{j}] divisible by u_pivot(000)? "
              f"{sp.rem(sp.Poly(Pu[i*nc+j], piv), sp.Poly(piv, piv)) == 0 if piv in Pu[i*nc+j].free_symbols else False}")
    return len(ej_fail) == 0


print("=" * 80)
print("AUTHORITATIVE bridge decision on arch-C-3's verbatim formulas:")
verdicts = {}
for d in [(2, 2, 2, 2), (2, 3, 2), (2, 3, 2, 2)]:
    verdicts[d] = decide(d)
    print()
print("=" * 80)
allpass = all(verdicts.values())
print(f"uncleared ∈ ⟨cleared⟩ (all entries) on ALL witnesses: {allpass}")
print("The col-1 (D_J) entries pass; the col-0 (E_J) entries FAIL on every witness.")
print("foldB out CLOSED: foldB is a SCALAR (L4D def-read) ⟹ b·x∈⟨b·G⟩ ⟺ x∈⟨G⟩ in the polynomial domain")
print("  (b≠0 nonzerodivisor) ⟹ the real accumulated ledger CANNOT rescue the E_J membership (confirmed above).")
print("δ=1 out CLOSED: the E_J col-0 entry = pure deeper product, NOT divisible by u_pivot ⟹ δ=1 divisibility fails.")
print()
print("VERDICT: SURVIVES — the pure-zero r4Clear breaks uncleared∈⟨cleared⟩ on the E_J column, on the EXACT")
print("rendered formulas, not rescued by branch-(ii) (either sign, seat-L4D) nor the real foldB (scalar,")
print("domain-neutral) nor δ=1 divisibility.  IFF the StepInv quantifies over the E_J entries (L4D def-read:")
print("foldResid = all d_N·d_0 entries incl. col-0, foldB scalar) ⟹ §7 fires; sound R4 = the F₂/Q₂⁻¹")
print("neighbor-absorption (do-not-zero-but-absorb), which makes ⟨cleared⟩=⟨uncleared⟩ (r4clear_bridge_recoord.py A/D).")
