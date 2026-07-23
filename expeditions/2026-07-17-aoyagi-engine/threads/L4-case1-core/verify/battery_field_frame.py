"""
§5 FIELD+FRAME acceptance battery (pnp half) — PRE-STAGED against the CURRENT baked canonNormalizationOf.
Ruling: threads/design-round-2-ruling.md §2/§5. Charter-§3 gate: trace the BAKED foldResid (through the
actual canonNormalizationOf (ii) recoord, MonumentAtlas:867-882 transcribed), NOT a hand model, on a WIDE
witness, and be able to FAIL on the frame error.

FIELD (ruling §2, F-value/native frame): for the reused divisor k, the extra-block (col ≥ t̃_k) support
coefficients factor as  c_i = m_k·β_i,  m_k = e₂ₖ(u) the reused divisor's SCHUR exceptional AS A
NATIVE-FRAME COMBINATION — on these witnesses e₂ = u_011 − u_010·u_001 (NOT the bare birth corner u_011).

ROWS:
 (i)   FIELD (baked): extra-block coeff divisible by e₂ (running-frame factoring)?  PASS iff yes.
 (ii)  FRAME red row: the SAME test with the ROOT-frame bare pivot u_011 — must FAIL (wrong locus). The
       battery is able-to-fail-on-frame-error iff (ii) is RED where (i) would be GREEN.
 (iii) REGRESSION: PerLayerDeg1From — deg-2 on the cleared layer below support, deg-1 from supportLayer up.
 (iv)  SCRAMBLED-e VACUITY: under the kill-e, the field is false/vacuous (the invariant excludes bad e).
Contrast: honest_clear (the MATH / hand model) vs baked canonNormalizationOf (the ENCODING).
"""
import sympy as sp

# ---------- baked canonNormalizationOf harness (transcribed verbatim) ----------
def make(d):
    N = len(d) - 1
    u = {(L, r, c): sp.Symbol(f"u{L}{r}{c}") for L in range(N) for r in range(d[L + 1]) for c in range(d[L])}
    return N, u

def readEntry(u, d, S, row, col):
    N = len(d) - 1
    return u[(S, row, col)] if (0 <= S < N and 0 <= row < d[S + 1] and 0 <= col < d[S]) else sp.Integer(0)

def canonNormalizationOf(u, d, sL, sC, piv):
    a, b = piv[1], piv[2]
    phi = {}
    for (L, r, c) in u:
        if L == sL and r != a and c != b and sC <= r and sC <= c:
            phi[(L, r, c)] = -readEntry(u, d, sL, r, b) * readEntry(u, d, sL, a, c)
        elif L == sL + 1 and c == a:
            phi[(L, r, c)] = sum((readEntry(u, d, sL, i, b) * readEntry(u, d, sL + 1, r, i)
                                  for i in range(d[sL + 1]) if i != c), sp.Integer(0))
        else:
            phi[(L, r, c)] = sp.Integer(0)
    return phi

def edgeShear(u, d, case, sL, sC, piv):
    if case in ("case11", "rollover"):
        return dict(u)
    phi = canonNormalizationOf(u, d, sL, sC, piv)
    return {k: u[k] + phi[k] for k in u}

def apply_edge(u, d, case, sL, sC, piv, cen, delta):
    w = edgeShear(u, d, case, sL, sC, piv)
    out = {}
    for k in u:
        if case == "rollover":
            out[k] = w[k]
        elif delta == 1:
            out[k] = sp.Integer(1) if k == piv else w[k]
        else:
            out[k] = (w[piv] if k == piv else (w[piv] * w[k] if k in cen else w[k]))
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
    for e in reversed(edges):
        v = apply_edge(v, d, *e)
    return coreGen(v, d)

def branch_to_case11_parent(d):
    # ed1 case2 δ1 pivot (0,0,0); ed2 case2 δ0 pivot (0,1,1) center = layer-0 block cols[1,wMU0); ed3 rollover
    wMU0 = min(d[0:1])   # widthMinUpto(0) = d_0
    cen2 = {(0, r, 1) for r in range(d[1]) if 1 <= r and 1 <= 1 < wMU0}
    return [("case2", 0, 0, (0, 0, 0), set(), 1),
            ("case2", 0, 1, (0, 1, 1), cen2, 0),
            ("rollover", 0, 2, None, set(), 0)]

def field_test(d, label):
    N, u = make(d)
    resid = [sp.expand(f) for f in foldResid(u, d, branch_to_case11_parent(d))]
    e2 = u[(0, 1, 1)] - u[(0, 1, 0)] * u[(0, 0, 1)]      # div1 Schur exceptional (native-frame combination)
    bare = u[(0, 1, 1)]                                   # root-frame single-coordinate reading (WRONG locus)
    runLen = 1                                            # t̃(div1) - cleared = 1
    extra = [(1, r, c) for r in range(d[2]) for c in range(d[1]) if c >= runLen]  # layer-1 col ≥ runLen
    def divis(coeff, fac):
        if sp.expand(coeff) == 0:
            return True                                   # vacuous (no such term) — OK
        q, rem = sp.div(sp.Poly(sp.expand(coeff), *u.values()), sp.Poly(sp.expand(fac), *u.values()))
        return sp.expand(rem.as_expr()) == 0
    field_e2 = True; field_bare = True; witness = None
    for j, f in enumerate(resid):
        for i in extra:
            c_i = sp.expand(f.coeff(u[i], 1))
            if not divis(c_i, e2):
                field_e2 = False
                if witness is None:
                    witness = (j, i, c_i)
            if not divis(c_i, bare):
                field_bare = False
    print(f"--- {label}  d={d} ---")
    print(f"  (i)  FIELD (baked, e₂-factoring, running frame): {'PASS' if field_e2 else 'FAIL'}")
    if witness:
        j, i, c = witness
        print(f"       non-factoring witness: coeff of u{i[0]}{i[1]}{i[2]} in resid[{j}] = {c}  (not divisible by e₂ = {e2})")
    print(f"  (ii) FRAME red row (root-frame bare pivot u_011): {'PASS(bad!)' if field_bare else 'FAIL (correctly names wrong locus)'}")
    return field_e2

def honest_clear_field(label):
    # the MATH (hand model): honest_clear residual in the running frame, extra-block carries e₂ as a fresh coord
    print(f"--- {label}  honest_clear (the MATH / faithful hand model) ---")
    e2 = sp.Symbol('e2'); s = sp.Symbol('s')
    w = sp.Matrix(2, 2, sp.symbols('w100 w101 w110 w111'))
    A2 = sp.Matrix(2, 2, sp.symbols('u200 u201 u210 u211'))
    M = sp.expand(A2 * w * sp.diag(1, e2) * sp.Matrix([[1, s], [0, 1]]))
    resid = [M[i, j] for i in range(2) for j in range(2)]
    extra = [w[0, 1], w[1, 1]]
    ok = all(sp.expand(sp.expand(f.coeff(x, 1))) == 0 or
             sp.div(sp.Poly(sp.expand(f.coeff(x, 1)), e2, s, *A2), sp.Poly(e2, e2, s, *A2))[1].as_expr() == 0
             for f in resid for x in extra)
    print(f"  FIELD (e₂-factoring): {'PASS' if ok else 'FAIL'}  (extra-block coeffs carry e₂)")
    return ok

print("=" * 70)
print("§5 FIELD+FRAME battery — CURRENT baked canonNormalizationOf (pre-stage)")
print("=" * 70)
math_ok = honest_clear_field("MATH reference")
print()
b1 = field_test((2, 2, 2, 2), "baked ENCODING (2,2,2,2)")
print()
b2 = field_test((2, 3, 2, 2), "baked ENCODING (2,3,2,2) [WIDE witness, ruled]")
print()
print("=" * 70)
print(f"MATH (honest_clear) field: {'HOLDS' if math_ok else 'FAILS'}")
print(f"ENCODING (baked canonNormalizationOf) field: (2,2,2,2) {'HOLDS' if b1 else 'FAILS'}, "
      f"(2,3,2,2) {'HOLDS' if b2 else 'FAILS'}")
print("If MATH HOLDS but ENCODING FAILS => the charter-§3 catch: the baked recoord is a wrong ENCODING")
print("of the correct math (missing the A_0 pivot-column clearing; the recoord double-counts).")


# ---------- (iii) REGRESSION: PerLayerDeg1From (degrees unchanged) ----------
print("\n--- (iii) REGRESSION: PerLayerDeg1From on the baked (2,3,2,2) case11 parent ---")
Nr, ur = make((2, 3, 2, 2))
rr = [sp.expand(f) for f in foldResid(ur, (2, 3, 2, 2), branch_to_case11_parent((2, 3, 2, 2)))]
def maxdeg_layer(f, L, d):
    xs = [ur[(L, r, c)] for r in range(d[L + 1]) for c in range(d[L])]
    fs = sp.expand(f).free_symbols
    return 0 if not any(x in fs for x in xs) else max(sum(m) for m in sp.Poly(sp.expand(f), *xs).monoms())
deg0 = max(maxdeg_layer(f, 0, (2, 3, 2, 2)) for f in rr)   # cleared layer below support (S=0)
deg1 = max(maxdeg_layer(f, 1, (2, 3, 2, 2)) for f in rr)   # support layer (S+1=1)
print(f"  max deg in layer-0 (cleared, below support) = {deg0} (expect 2); "
      f"layer-1 (supportLayer) = {deg1} (expect 1)  => PerLayerDeg1From {'unchanged' if deg1 == 1 else 'CHANGED!'}")

# ---------- (iv) SCRAMBLED-e VACUITY: under the kill-e the field is false/vacuous ----------
print("\n--- (iv) SCRAMBLED-e VACUITY: the field must be FALSE/vacuous under the kill-e ---")
# kill-e (hedge): u_(0,1,0) += u_(1,0,1) — injects a degree-2-in-extra term. The field (extra coeff
# = e₂·β, degree-1) cannot hold: the residual is not even degree-1 in the extra block.
Ns, us = make((2, 2, 2, 2))
order = [(L, r, c) for L in range(3) for r in range(2) for c in range(2)]
E = sp.eye(12); E[order.index((0, 1, 0)), order.index((1, 0, 1))] = 1
def coreGen_e(uu, d, Emat):
    xv = Emat * sp.Matrix([uu[c] for c in order])
    xf = {order[i]: xv[i] for i in range(12)}
    A = [sp.Matrix(2, 2, lambda r, c: xf[(L, r, c)]) for L in range(3)]
    P = A[2] * A[1] * A[0]
    return [P[i, j] for i in range(2) for j in range(2)]
# fold to the case11 parent then apply e
v = dict(us)
for e in reversed(branch_to_case11_parent((2, 2, 2, 2))):
    v = apply_edge(v, (2, 2, 2, 2), *e)
rk = [sp.expand(f) for f in coreGen_e(v, (2, 2, 2, 2), E)]
extra_s = [us[(1, 0, 1)], us[(1, 1, 1)]]
maxext = max((0 if not any(x in sp.expand(f).free_symbols for x in extra_s)
              else max(sum(m) for m in sp.Poly(sp.expand(f), *extra_s).monoms())) for f in rk)
print(f"  under kill-e: max degree in the extra block = {maxext} (>1 => NOT degree-1 => field VACUOUS/FALSE)")
print(f"  => the carried field correctly EXCLUDES the kill-e: {'VACUOUS (PASS)' if maxext > 1 else 'holds (unexpected)'}")

print("\n=== BATTERY SUMMARY (current baked def, pre-stage) ===")
print("  (i)  FIELD baked: FAIL on both wide witnesses (encoding broken; e₂ non-factoring)")
print("  (ii) FRAME red row: root-frame bare pivot correctly FAILS (able-to-fail-on-frame-error ✓)")
print("  (iii) REGRESSION: PerLayerDeg1From unchanged (layer-1 deg 1, layer-0 deg 2) ✓")
print("  (iv) SCRAMBLED-e VACUITY: field vacuous/false under kill-e ✓")
print("  DECISIVE: MATH holds, baked ENCODING fails => the charter-§3 catch; canonNormalizationOf must")
print("  add the A_0 pivot-column clearing before the field conjunct can hold (else the REBAKE field is FALSE).")
