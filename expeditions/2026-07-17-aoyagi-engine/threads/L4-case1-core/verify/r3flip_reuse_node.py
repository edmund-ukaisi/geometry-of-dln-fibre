"""
R3-FLIP REUSE-NODE forms (elder MERGE GATE: "if the reuse node is NOT clean under R3, re-open").

The ruling (§8, 62bfa334d) adopted R3 (branch-ii sign flip, −γ) + READING B (clean-block invariant:
b's external, foldResid = clean D_J). The gate: at the case11 REUSE-PARENT node (after ed1/ed2/ed3),
are the extra-block residual coefficients CLEAN (no reused-divisor exceptional) under R3?  honest_clear's
"extras carry e2" (object A) is retracted as the +γ (baked, wrong-direction) artifact — under R3 (−γ,
her text's direction) they should be clean (object B).

We run the BAKED canonNormalizationOf fold (sign-parametrized branch ii) to node 3 (reuse parent) on
(2,2,2,2) [canonical] and (2,3,2,2) [wide], and examine the deeper (layer >= 1) coords' coefficients:
does each vanish at the reused divisor's exceptional = 0 (=> carries the b-factor, object A) or not
(=> clean, object B)?  reused divisor = div1 @ (0,1,1); its exceptional coord at node 3 is u011.
"""
import sympy as sp


def make(d):
    N = len(d) - 1
    u = {(L, r, c): sp.Symbol(f"u{L}{r}{c}") for L in range(N) for r in range(d[L + 1]) for c in range(d[L])}
    return N, u


def readEntry(u, d, S, row, col):
    N = len(d) - 1
    return u[(S, row, col)] if (0 <= S < N and 0 <= row < d[S + 1] and 0 <= col < d[S]) else sp.Integer(0)


def canonNormalizationOf(u, d, sL, sC, piv, sign):
    """sign=+1 baked (A_{S+1} Q1^{-1}); sign=-1 R3-flip (A_{S+1} Q1). branch (i) Schur unchanged."""
    a, b = piv[1], piv[2]
    phi = {}
    for (L, r, c) in u:
        if L == sL and r != a and c != b and sC <= r and sC <= c:
            phi[(L, r, c)] = -readEntry(u, d, sL, r, b) * readEntry(u, d, sL, a, c)
        elif L == sL + 1 and c == a:
            phi[(L, r, c)] = sign * sum((readEntry(u, d, sL, i, b) * readEntry(u, d, sL + 1, r, i)
                                         for i in range(d[sL + 1]) if i != c), sp.Integer(0))
        else:
            phi[(L, r, c)] = sp.Integer(0)
    return phi


def apply_edge(u, d, case, sL, sC, piv, cen, delta, sign):
    if case in ("case11", "rollover"):
        w = dict(u)
    else:
        phi = canonNormalizationOf(u, d, sL, sC, piv, sign)
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


def coreGen(u, d):
    N = len(d) - 1
    P = sp.Matrix(d[N], d[N - 1], lambda r, c: u[(N - 1, r, c)])
    for L in range(N - 2, -1, -1):
        P = P * sp.Matrix(d[L + 1], d[L], lambda r, c: u[(L, r, c)])
    return [sp.expand(P[i, j]) for i in range(P.rows) for j in range(P.cols)]


def foldResid(d, edges, sign):
    N, u = make(d)
    v = dict(u)
    for e in reversed(edges):
        v = apply_edge(v, d, *e, sign)
    return coreGen(v, d), u


def report(d, edges, reused_exc, label):
    print("=" * 80)
    print(f"{label}: d={d}  reuse-parent node = after {len(edges)} edges; reused-divisor exceptional = {reused_exc}")
    for sign, nm in [(+1, "baked (+γ)"), (-1, "R3-flip (−γ)")]:
        ents, u = foldResid(d, edges, sign)
        exc = u[reused_exc]
        print(f"\n  --- {nm} ---")
        anyA = False
        for j, f in enumerate(ents):
            f = sp.expand(f)
            # deeper coords = layer >= 1
            deeper = sorted([k for k in u if k[0] >= 1 and u[k] in f.free_symbols], key=str)
            print(f"    slot {j}: {f}")
            for k in deeper:
                coeff = sp.expand(f.coeff(u[k], 1))
                if coeff == 0:
                    continue
                carries = (sp.expand(coeff.subs(exc, 0)) != coeff)      # coeff depends on the exceptional
                vanishes = (sp.expand(coeff.subs(exc, 0)) == 0)          # coeff = exc·(...) exactly
                tag = ("carries-exc(A)" if carries else "CLEAN(B)") + (" [=exc·(.)]" if vanishes else "")
                print(f"        coeff of u{k[0]}{k[1]}{k[2]}: {coeff}   -> {tag}")
                anyA = anyA or carries
        print(f"    => {nm}: any deeper coeff carries the reused exceptional? {anyA}  "
              f"({'OBJECT A (e2-extras)' if anyA else 'OBJECT B (CLEAN — ruling confirmed)'})")
        # objective structure summary: per-entry total degree + degree in the pivot-row coord u001,
        # + does each OUTPUT ROW share a common exceptional factor (=> diag(b)·[clean], object A)?
        u001 = u[(0, 0, 1)]
        allsyms = list(u.values())
        Nd = len(d) - 1
        nrows = d[Nd]
        ncols = d[0]
        print(f"    structure: (tdeg, deg_u001) per slot; row-common-factor test:")
        for i in range(nrows):
            rowents = [sp.expand(ents[i * ncols + j]) for j in range(ncols)]
            degs = []
            for f in rowents:
                td = 0 if f == 0 else sp.Poly(f, *[s for s in allsyms if s in f.free_symbols]).total_degree()
                du = 0 if u001 not in f.free_symbols else sp.Poly(f, u001).degree()
                degs.append((td, du))
            g = rowents[0]
            for f in rowents[1:]:
                g = sp.gcd(g, f)
            print(f"      row {i}: slot-degs {degs}; row-gcd = {sp.expand(g)}  "
                  f"({'nontrivial common factor (diag(b) row-scale present)' if g != 1 else 'gcd=1 (NO row-scale b — b=1 here, so foldResid must BE the clean block)'})")


# (2,2,2,2): reuse parent = after case2 δ1 (0,0,0), case2 δ0 (0,1,1), rollover
br_2222 = [("case2", 0, 0, (0, 0, 0), set(), 1),
           ("case2", 0, 1, (0, 1, 1), {(0, 1, 1)}, 0),
           ("rollover", 0, 2, None, set(), 0)]
report((2, 2, 2, 2), br_2222, (0, 1, 1), "CANONICAL (2,2,2,2)")

# (2,3,2,2): wide; reuse parent = after case2 δ1 (0,0,0), case2 δ0 (0,1,1) center{(0,1,1),(0,2,1)}, rollover
br_2322 = [("case2", 0, 0, (0, 0, 0), set(), 1),
           ("case2", 0, 1, (0, 1, 1), {(0, 1, 1), (0, 2, 1)}, 0),
           ("rollover", 0, 2, None, set(), 0)]
report((2, 3, 2, 2), br_2322, (0, 1, 1), "WIDE (2,3,2,2)")
