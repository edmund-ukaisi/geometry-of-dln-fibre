#!/usr/bin/env python3
# guards: b-leaf34-case-steps (DLNFibre.DLN.Aoyagi.case1_preserves_stepInv) — the INTERIOR
#         case1(1)-boost δ=1 sub-case of THE WALL. Adjudicates: at such an edge the parent
#         `foldResid p` is Deg1SupportedOn the boost center `{pivot} ∪ partial-block` (A1+A2), the
#         boost's u_pivot-divisibility crux holds (A3), AND this is NOT derivable from the parent's
#         supportAt-`Deg1SupportedSlot` invariant alone (carried-vs-derived → a CARRIED conjunct or a
#         b-chain-pinning IsRealBranch is FORCED).
# config: exact algebra (sympy). instances (2,2,2,2) [minimal: 1 hit] and (3,3,2,2) [2 hits, incl. the
#         running-min shrink], plus a breadth sweep. Monte-Carlo NOT used. exit 0 = claim survives; 1 = killed.
# provenance: pnp-boost (pen-and-paper WITNESS seat, expedition 2026-07-17-aoyagi-engine). Fold
#         reconstructed from fold-recursion-template.md §1.1/§2/§3 (b-chain diag + Q/P Schur) + the Lean
#         objects (MonumentAtlas.foldResid/canonCenterOf/Deg1SupportedSlot, PrincipalInv.Deg1SupportedOn).
#         Recursion mirrors clause3_corner_check.py; concrete blow-up mirrors trace334.py [MATRIX].
#         Decorrelated Codex xhigh (threads/pnp-boost/codex/boost-readiness-derive-answer.md) converged
#         independently on the same structure and verdict.
"""
THE OBJECT.  At an interior case1(1)-δ=1 boost edge `p → child` (parent state (S, J=0), S<L, reusing a
divisor `u_p` born at an EARLIER layer S'<S), the parent generator family — Aoyagi's product-ideal
residual at that node — is, with the dominant monomial `b_1 = foldB` divided out (the Lean `foldResid`,
FIX-RESID strict-transform form, elder ruling A′):

    foldResid[i][j] = r_i * sum_k D[i][k] * H[k][j],     r_i = b_i / b_1,

where (fold-recursion-template.md §1.1):
  * b-chain  b_i = ∏_{ t̃(u) < i } u   (a u-monomial; b_1 | b_2 | … , the divisibility chain);
  * D = residual block  (M(S) x M^(S+1), template rows = running-min axis; FRESH degree-1 coords, §3.4);
  * H = ∏_{s>S} C^(s)   (deeper untouched layers; coords disjoint from the center — spectators).

THE CENTER (canonCenterOf case11, in flat coords) = `{pivot=u_p} ∪ (partial block)`, where the partial
block = the DOMINANT b-chain rows `i < J_1` of D (flat COL axis via the running-min↔flat-col transpose;
size J_1·M^(S+1), a NON-square check pins ROW-0-not-COL-0). The geometric support (supportAt, J=0) is the
FULL layer block = ALL of D — strictly LARGER (J_1 < M(S)).

THE MECHANISM (the reason (P) holds): the b-chain is `u_p`-free on the dominant rows and carries exactly
one `u_p` on the rest — `u_p | b_i ⟺ i > J_1`, with cofactor `b_i/b_{J_1+1}` again a u-monomial. So
  * dominant rows (i < J_1, r_i = 1): each monomial's single center factor is the block coord D[i][k]
    (in the partial block) — "partial-block terms get their center factor from the block variables";
  * other rows (i ≥ J_1, r_i = u_p·(u-monomial)): the single center factor is `u_p` from `r_i = b_i/b_1`
    — "the untouched terms ALREADY carry u_p in their non-dominant b-chain coefficient b_i/b_1".

CHECKS (exact, per boost instance):
  A1  center → 0 kills foldResid              (every monomial has ≥1 center factor).
  A2  joint center-degree of every monomial ≤ 1 (with A1 ⟹ EXACTLY one — Deg1SupportedOn).
  A3  foldResid(Bu) = u_p · foldResid(qm u)   (the crux; ⟹ divisible by u_p after the boost blow-up).
  B   the load-bearing combinatorial fact  u_p | b_i ⟺ i > J_1  (dominant rows u_p-free).
  CARRIED-vs-DERIVED  two witnesses R satisfying the parent invariant (Q) [Deg1SupportedSlot on the FULL
     block: full-block-linear, per-layer degree ≤ 1] yet VIOLATING (P): a missing-factor witness (kills
     A1) and an extra-pivot-factor witness (kills A2). ⟹ (P) is NOT derivable from (Q); the b-chain
     rowwise-coupling must be CARRIED.
"""
import copy, sys
import sympy as sp

ok = True
VIOL = []
def check(name, cond):
    global ok
    c = bool(cond); ok &= c
    print(f"  [{'PASS' if c else 'FAIL'}] {name}")
    if not c: VIOL.append(name)
    return c

# ---------------------------------------------------------------------------------------------------
# 1. The fold recursion (mirrors clause3_corner_check.py): emit every interior case1(1)-δ=1 boost parent
#    with the FULL divisor ledger (each divisor's exceptional symbol + profile T), the reused u_p, J_1,
#    M(S) [template rows], M^(S+1) [template cols], and M^(L+1) [deeper-layer col count].
# ---------------------------------------------------------------------------------------------------
def fold_emit(M):
    L = len(M) - 1
    def Mrun(S): return min(M[:S])
    def tilde(T): return min(T)
    emits = []
    cnt = [0]
    def fresh_u():
        cnt[0] += 1
        return sp.Symbol(f'u{cnt[0]}')
    def step(S, J, divs):
        MS = Mrun(S); MS1 = M[S] if S <= L else None; capJ = min(MS, MS1)
        if J == capJ:
            if S == L: return
            step(S + 1, 0, divs); return
        jumps = sorted({tilde(d['T']) for d in divs if J + 1 <= tilde(d['T']) <= MS - 1})
        if not jumps:                                            # CASE 2: fresh birth
            Tn = [(M[k] if (k + 1) < S else J) for k in range(1, L + 1)]
            step(S, J + 1, divs + [{'u': fresh_u(), 'T': Tn, 'birthS': S}]); return
        jj = jumps[0]; J1 = jj - J
        ustar = min([d for d in divs if tilde(d['T']) == jj], key=lambda d: tuple(d['T']))
        if J == 0 and S < L:                                     # INTERIOR case1(1) δ=1 boost parent
            emits.append(dict(M=M, S=S, divs=copy.deepcopy(divs), up=ustar['u'], J1=J1,
                              MS=MS, MS1=MS1, DC=M[L]))
        d11 = copy.deepcopy(divs)                                # case1(1): boost in place, no J-advance
        u1 = next(d for d in d11 if d['u'] == ustar['u'])
        for k in range(S, L + 1): u1['T'][k - 1] = J
        step(S, J, d11)
        d12 = copy.deepcopy(divs)                                # case1(2): split (a distinct branch)
        Tn = [(ustar['T'][k - 1] if k < S else J) for k in range(1, L + 1)]
        d12.append({'u': fresh_u(), 'T': Tn, 'birthS': S})
        step(S, J + 1, d12); return
    step(1, 0, [])
    return emits

def b_chain(divs, MS):
    """b_i = ∏_{ t̃(d) < i } u_d,  i = 1..MS   (fold-recursion-template §1.1)."""
    return [sp.prod([d['u'] for d in divs if min(d['T']) < i]) or sp.Integer(1) for i in range(1, MS + 1)]

# ---------------------------------------------------------------------------------------------------
# 2. Build foldResid at a boost parent + the center/support, then run A1/A2/A3/B.
# ---------------------------------------------------------------------------------------------------
def joint_center_degree(monom, center_syms):
    """total degree of a single sympy monomial in the center symbols."""
    d = 0
    for s in center_syms:
        d += sp.degree(sp.Poly(monom, s), s) if monom.has(s) else 0
    return d

def run_boost(e, verbose=True):
    global ok
    S, divs, up, J1, MS, MS1, DC = e['S'], e['divs'], e['up'], e['J1'], e['MS'], e['MS1'], e['DC']
    b = b_chain(divs, MS)
    b1 = b[0]
    r = [sp.cancel(bi / b1) for bi in b]                          # residual coefficients r_i = b_i / b_1
    # residual block D (M(S) x M^(S+1)) and deeper H (M^(S+1) x M^(L+1)) — fresh, center-disjoint coords.
    D = sp.Matrix(MS, MS1, lambda i, k: sp.Symbol(f'x_{i}_{k}'))
    H = sp.Matrix(MS1, DC, lambda k, j: sp.Symbol(f'z_{k}_{j}'))  # deeper layer(s): spectators
    DH = sp.expand(D * H)
    # foldResid[i][j] = r_i * (D H)[i][j]
    resid = [[sp.expand(r[i] * DH[i, j]) for j in range(DC)] for i in range(MS)]

    # center = {pivot} ∪ partial block (dominant rows i < J1, all cols) ;  support = full block
    partial = [D[i, k] for i in range(J1) for k in range(MS1)]
    center = [up] + partial
    full_support = [D[i, k] for i in range(MS) for k in range(MS1)]
    center_set = set(center)

    if verbose:
        print(f"\n  --- M={e['M']}  boost parent (S={S}, J=0): reuse u_p={up}, J1={J1}, "
              f"D:{MS}x{MS1}, deeper cols={DC} ---")
        print(f"      b-chain = {b};  r_i = b_i/b_1 = {r}")
        print(f"      center = {{u_p}} ∪ partial(|{len(partial)}|) ;  support = full block(|{len(full_support)}|)"
              f"   support ⊋ center∩support : {len(full_support) > len(partial)}")

    # ---- B: the load-bearing b-chain fact  u_p | b_i  <=>  i > J1 ----
    okB = all(((up in b[i - 1].free_symbols) == (i > J1)) for i in range(1, MS + 1))
    check(f"[B]  M={e['M']} (S={S},u_p={up}): u_p | b_i  <=>  i > J1  (dominant rows u_p-free)", okB)

    # ---- support strictly larger than the boost center's overlap ----
    check(f"[sup] M={e['M']} (S={S}): geometric support (full block) ⊋ center∩support (partial block)",
          len(full_support) > len(partial))

    # ---- A1: center → 0 kills the residual ----
    zero_center = {c: 0 for c in center}
    a1 = all(sp.expand(resid[i][j].subs(zero_center)) == 0 for i in range(MS) for j in range(DC))
    check(f"[A1] M={e['M']} (S={S}): center → 0 kills foldResid (every monomial has ≥1 center factor)", a1)

    # ---- A2: joint center-degree of every monomial ≤ 1 (with A1 ⟹ exactly one) ----
    a2 = True
    for i in range(MS):
        for j in range(DC):
            poly = sp.expand(resid[i][j])
            terms = poly.as_ordered_terms() if poly != 0 else []
            for t in terms:
                if joint_center_degree(t, center_set) > 1:
                    a2 = False
    check(f"[A2] M={e['M']} (S={S}): joint center-degree ≤ 1 per monomial (Deg1SupportedOn, exactly one)", a2)

    # ---- A3: foldResid(Bu) = u_p · foldResid(qm u)  (the crux) ⟹ divisible by u_p ----
    # B  = blockBlowupMap center pivot : pivot ↦ u_p ; partial coord c ↦ u_p·c ; spectator ↦ c
    # qm = blockBlowupCoordQuot pivot  : pivot ↦ 1   ; everything else ↦ itself
    subB  = {c: up * c for c in partial}                          # pivot stays u_p (identity on it)
    subqm = {up: sp.Integer(1)}                                   # qm sets pivot→1, leaves partial coords
    a3 = True
    for i in range(MS):
        for j in range(DC):
            lhs = sp.expand(resid[i][j].subs(subB, simultaneous=True))
            rhs = sp.expand(up * resid[i][j].subs(subqm, simultaneous=True))
            if sp.expand(lhs - rhs) != 0:
                a3 = False
            q, rem = sp.div(sp.Poly(lhs, up), sp.Poly(up, up))     # divisibility of the boosted residual
            if rem != 0:
                a3 = False
    check(f"[A3] M={e['M']} (S={S}): foldResid(Bu) = u_p·foldResid(qm u)  &  u_p | foldResid(Bu)  (crux)", a3)

    # ---- NEGATIVE CONTROL (non-vacuity): DROP the pivot from the center. A1 must then FAIL on a
    #      non-dominant row (its only center factor was u_p) — proving the check has teeth and that the
    #      pivot is load-bearing exactly for the rows the b-chain feeds. Only meaningful when M(S) > J1
    #      (a non-dominant row exists — always, at an interior boost). ----
    if MS > J1:
        zero_partial_only = {c: 0 for c in partial}                 # center minus the pivot
        killed_without_pivot = all(sp.expand(resid[i][j].subs(zero_partial_only)) == 0
                                   for i in range(MS) for j in range(DC))
        check(f"[NEG] M={e['M']} (S={S}): dropping u_p from the center BREAKS A1 (non-dominant row survives)"
              " — check is non-vacuous, pivot is load-bearing", not killed_without_pivot)

    return dict(resid=resid, center=center, partial=partial, full_support=full_support, D=D, up=up, J1=J1,
                MS=MS, MS1=MS1, DC=DC)

# ---------------------------------------------------------------------------------------------------
# 3. CARRIED-vs-DERIVED: two witnesses satisfying the parent invariant (Q) but violating (P).
#    (Q) [testable core of Deg1SupportedSlot on the FULL block]: R vanishes at full-block→0 AND has joint
#        full-block-degree ≤ 1 (a full-block-linear form with center-free continuous coefficients).
# ---------------------------------------------------------------------------------------------------
def sat_Q(R, full_support):
    R = sp.expand(R)
    vanish = sp.expand(R.subs({c: 0 for c in full_support})) == 0
    fs = set(full_support)
    deg1 = all(joint_center_degree(t, fs) <= 1 for t in (R.as_ordered_terms() if R != 0 else []))
    return vanish and deg1

def carried_vs_derived(built):
    print("\n" + "-" * 96)
    print("CARRIED-vs-DERIVED: is (P) [Deg1SupportedOn small center] derivable from (Q)"
          " [Deg1SupportedSlot on full block]?")
    D, up, J1, MS, MS1, full_support = (built['D'], built['up'], built['J1'], built['MS'],
                                        built['MS1'], built['full_support'])
    center = built['center']; center_set = set(center); partial = built['partial']
    # W1 — MISSING factor: a bare NON-dominant-row block coordinate (row J1, col 0). ∈ full block, ∉ center.
    W1 = D[J1, 0]
    w1_Q = sat_Q(W1, full_support)
    w1_A1 = sp.expand(W1.subs({c: 0 for c in center})) == 0                      # A1 for W1
    check("[C1] witness W1 = D[J1][0] satisfies (Q) [full-block-linear, vanishes at 0, per-layer deg ≤1]", w1_Q)
    check("[C1] witness W1 VIOLATES A1 (center→0 does NOT kill it) — so (P) is NOT implied by (Q)",
          not w1_A1)
    # W2 — EXTRA pivot factor: a partial-block coord times the pivot. ∈ ⟨full block⟩, but TWO center factors.
    W2 = up * D[0, 0]
    w2_Q = sat_Q(W2, full_support)
    w2_deg = max((joint_center_degree(t, center_set) for t in sp.expand(W2).as_ordered_terms()), default=0)
    check("[C2] witness W2 = u_p·D[0][0] satisfies (Q) [full-block-linear, vanishes at 0, per-layer deg ≤1]", w2_Q)
    check("[C2] witness W2 VIOLATES A2 (joint center-degree = 2) — (Q) controls no extra-pivot factor",
          w2_deg == 2)
    print("  ⟹ (Q) controls NEITHER missing center factors on the complementary rows NOR extra pivot")
    print("     factors on the partial block. The rowwise b-chain coupling (u_p | b_i ⟺ i>J1) is EXTRA")
    print("     structure (Aoyagi provenance), NOT recoverable from (Q). VERDICT: CARRIED, not derived.")

# ---------------------------------------------------------------------------------------------------
# 4. CONCRETE cross-check (mirrors trace334.py [MATRIX]): (2,2,2,2) layer-0 blow-up + Q-Schur gives the
#    b-chain (u11, u11·u12); b_2/b_1 = u12 = the reused pivot — the "b_i/b_1 carries u_p" mechanism, in
#    ORIGINAL matrix coordinates (independent of the fresh-coord fold engine above).
# ---------------------------------------------------------------------------------------------------
def concrete_2222():
    print("\n" + "-" * 96)
    print("CONCRETE cross-check — (2,2,2,2) layer-0 blow-up + Q-Schur, ORIGINAL coords (trace334 [MATRIX]):")
    u11, u12, beta1, gam1, del1 = sp.symbols('u11 u12 beta1 gam1 del1')
    Cbar = sp.Matrix([[1, beta1], [gam1, del1]])                  # C0 = u11·Cbar in the pivot chart
    Q1 = sp.Matrix([[1, -beta1], [0, 1]])
    CbarQ = sp.expand(Cbar * Q1)                                  # [[1,0],[gam1, s1]], s1 = del1-gam1 beta1
    s1 = sp.expand(del1 - gam1 * beta1)
    b1, b2 = u11, u11 * u12                                       # u12 := the Schur pivot s1 born at (1,1)
    ratio = sp.simplify(b2 / b1)
    check("[X] (2,2,2,2) concrete: Q clears the pivot row (CbarQ[0,1]=0) and SE = Schur s1 = del1-gam1 beta1",
          CbarQ[0, 1] == 0 and sp.expand(CbarQ[1, 1] - s1) == 0)
    check("[X] (2,2,2,2) concrete: b-chain (u11, u11·u12) with b_2/b_1 = u_p (= u12, the reused divisor)",
          ratio == u12)

# ===================================================================================================
if __name__ == "__main__":
    print("=" * 96)
    print("case11_boost_readiness — INTERIOR case1(1)-δ=1 boost: foldResid Deg1SupportedOn {pivot}∪partial")
    print("=" * 96)

    # required instances (brief): (2,2,2,2) minimal, (3,3,2,2) two hits + running-min shrink.
    REQUIRED = [(2, 2, 2, 2), (3, 3, 2, 2)]
    # breadth sweep (depth-diverse; the mechanism is shape-independent).
    SWEEP = [(2, 2, 2, 2, 2), (4, 4, 4, 4), (3, 3, 3, 3), (4, 4, 2, 2), (3, 3, 4, 4), (2, 2, 3, 3)]

    built_for_witness = None
    n_hits = 0
    for M in REQUIRED + SWEEP:
        emits = fold_emit(M)
        if M in REQUIRED and not emits:
            check(f"[hit] required instance M={M} exercises an interior case11-δ1 boost", False)
        for e in emits:
            n_hits += 1
            built = run_boost(e, verbose=(M in REQUIRED))
            if M == (2, 2, 2, 2):
                built_for_witness = built

    print(f"\n  ({n_hits} interior case11-δ1 boost parents checked across {len(REQUIRED)+len(SWEEP)} instances)")

    carried_vs_derived(built_for_witness)
    concrete_2222()

    print("\n" + "=" * 96)
    if not ok:
        print("BATTERY FAIL — a check was violated:")
        for v in VIOL: print("   ", v)
        sys.exit(1)
    print("BATTERY PASS — claim SURVIVES:")
    print("  • A1+A2: foldResid IS Deg1SupportedOn {pivot}∪partial-block at every interior case11-δ1 boost;")
    print("  • A3   : the u_pivot-divisibility crux holds (foldResid(Bu) = u_p·foldResid(qm u));")
    print("  • carried-vs-derived: (P) is NOT derivable from the parent's supportAt-Deg1SupportedSlot (Q)")
    print("           — a CARRIED b-chain-coupling conjunct (or a b-chain-pinning IsRealBranch) is FORCED.")
    sys.exit(0)
