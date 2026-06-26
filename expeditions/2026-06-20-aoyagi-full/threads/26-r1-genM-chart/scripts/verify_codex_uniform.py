#!/usr/bin/env python3
"""
verify_codex_uniform.py — INDEPENDENTLY verify Codex's UNIFORM closed-form chart (genM-uniform-answer.md).

Construction (Codex, derived): r_s = t_{s-1}-t_s, c_s = M_s - t_s, d_s = r_s c_s, D = sum d_s = minAdm.
Block coords with kept t_s first. For 1<=s<L:
  X_s in R^{r_s x t_s}, N_s in R^{t_s x c_s}, K_s = L_s diag(q) U_s (unit lower/upper tri, t_s x t_s).
  P_s = [I_{t_s}; X_s], Q_s = [I_{t_s} | N_s].
  C_s = P_s K_s Q_s + u [[0,0],[0,R_s]]  = [[K_s, K_s N_s],[X_s K_s, X_s K_s N_s + u R_s]]
        (M_s x M_{s+1};  R_s the r_s x c_s residual, free, with ONE distinguished slot = 1 overall).
  C_L = u R_L  (t_{L-1} x M_L).
Chaining: G_s = [[I_{t_s}, N_s],[0, I_{c_s}]] (M_s x M_s, unit-tri, det 1).  W_{s+1} in R^{c_s x M_{s+1}}.
  A^(0) = C_1;   A^(s) = G_s^{-1}[C_{s+1}; W_{s+1}] = [[C_{s+1} - N_s W_{s+1}],[W_{s+1}]]  (1<=s<L).
Then prod A = u H exactly; F = u^2 ||H||^2; |det DPhi| = |u|^{D-1} * prod|q_{s,i}|^{r_s+c_s+2(t_s-i)}.

NOTE on indexing: Codex uses 1-based boundaries s=1..L; A^(0..L-1) are the L factors. Boundary s sits
between factor (s-1) and factor s in 0-based. We implement carefully and CHECK:
  (G1) min u-degree of F == 2 (rate);  (G2) V|_{u=0} nonzero, >0 at sector;
  (G3) |det DPhi| u-exponent == minAdm-1, and det != 0 off {u=0} (the spectator q-monomial).
We verify input-count == flatDim (a genuine chart, no over/under-parametrisation).
"""
import sympy as sp
from genM_structure import all_adm, Mval


def minim(M):
    best = None; bT = None
    for T in all_adm(tuple(M)):
        v = Mval(tuple(M), T)
        if best is None or v < best:
            best = v; bT = T
    return bT, best


def unit_lower(n, fr):
    L = sp.eye(n)
    for i in range(n):
        for j in range(i):
            L[i, j] = fr()
    return L


def unit_upper(n, fr):
    U = sp.eye(n)
    for i in range(n):
        for j in range(i + 1, n):
            U[i, j] = fr()
    return U


def build_codex(M):
    M = tuple(M); L = len(M) - 1
    T, minAdm = minim(M)
    t = [M[0]] + [T[s - 1] for s in range(1, L)] + [0]   # t_0..t_L ; t_0=M_0, t_L=0; t_s=T[s-1]
    # boundary s=1..L: r_s = t_{s-1}-t_s, c_s = M_s - t_s (M_s is the row-count of factor (s-1)=A^(s-1))
    # Codex factor A^(0)=C_1 (boundary 1), A^(s)=chain(C_{s+1}) for s=1..L-1.
    u = sp.Symbol('u', positive=True)
    inputs = [u]
    cnt = sp.numbered_symbols('z')
    def fr():
        sym = sp.Symbol(str(next(cnt)), real=True); inputs.append(sym); return sym
    # residual slot fixing: one distinguished entry = 1 across all R_s; Codex puts it in R_L(1,1).
    radial_fixed = [False]
    def Rblock(rrows, ccols, is_final):
        Rb = sp.zeros(rrows, ccols)
        for i in range(rrows):
            for j in range(ccols):
                if is_final and (not radial_fixed[0]) and i == 0 and j == 0:
                    Rb[i, j] = sp.Integer(1); radial_fixed[0] = True  # distinguished slot = 1 (radial)
                else:
                    Rb[i, j] = fr()
        return Rb
    # build C_s for s=1..L. boundary s relates widths (M_{s-1} rows, M_s cols) of factor A^(s-1).
    # row-count of C_s = M_{s-1}, col-count = M_s.   t_{s-1} kept rows in, t_s kept cols out.
    C = {}
    for s in range(1, L + 1):
        rows, cols = M[s - 1], M[s]
        ts_in, ts_out = t[s - 1], t[s]
        r_s = t[s - 1] - t[s]          # newly dropped rank at this boundary
        c_s = M[s] - t[s]              # residual cols
        if s == L:
            # C_L = u * R_L  (t_{L-1} x M_L);  but rows should be M_{L-1}? Codex: C_L in R^{t_{L-1} x M_L}.
            # In the chaining, C_L plugs into A^(L-1) = [[C_L - N_{L-1} W_L],[W_L]] with t_{L-1} top rows.
            C[s] = u * Rblock(ts_in, cols, True)
        else:
            # K_s : t_{s-1} x t_{s-1}? Codex K_s is t_s x t_s (the OUTGOING kept rank). Re-read:
            # P_s=[I_{t_s};X_s] (rows: t_s + r_s = t_{s-1}); Q_s=[I_{t_s}|N_s] (cols: t_s + c_s = M_s).
            # K_s : t_s x t_s.  So C_s : (t_s+r_s) x (t_s+c_s) = t_{s-1} x M_s. Good (matches rows M_{s-1}=t_{s-1}?
            # only if M_{s-1}=t_{s-1}; but M_{s-1} >= t_{s-1}.  The EXTRA rows M_{s-1}-t_{s-1} come from the
            # chaining lift W. So C_s has t_{s-1} rows; A^(s-1) has M_{s-1} rows (C_s on top + W below).)
            ts = t[s]
            Ks = unit_lower(ts, fr) * sp.diag(*[fr() + 1 for _ in range(ts)]) * unit_upper(ts, fr)
            Xs = sp.Matrix(r_s, ts, lambda i, j: fr()) if r_s > 0 else sp.zeros(0, ts)
            Ns = sp.Matrix(ts, c_s, lambda i, j: fr()) if c_s > 0 else sp.zeros(ts, 0)
            Rs = Rblock(r_s, c_s, False) if (r_s > 0 and c_s > 0) else sp.zeros(r_s, c_s)
            Ps = sp.Matrix.vstack(sp.eye(ts), Xs)         # (ts+r_s) x ts = t_{s-1} x t_s
            Qs = sp.Matrix.hstack(sp.eye(ts), Ns)         # ts x (ts+c_s) = t_s x M_s
            base = Ps * Ks * Qs                            # t_{s-1} x M_s
            resid = sp.zeros(ts + r_s, ts + c_s)
            for i in range(r_s):
                for j in range(c_s):
                    resid[ts + i, ts + j] = u * Rs[i, j]
            C[s] = base + resid
    # store N_s for the chaining frames
    # rebuild needs N_s; recompute by re-deriving from C? simpler: store during build.
    return M, L, t, u, inputs, C, minAdm


def build_factors(M):
    """Assemble A^(0..L-1) with the chaining, returning factors + inputs + minAdm + the q-list."""
    M = tuple(M); L = len(M) - 1
    T, minAdm = minim(M)
    t = [M[0]] + [T[s - 1] for s in range(1, L)] + [0]
    u = sp.Symbol('u', positive=True)
    inputs = [u]
    cnt = sp.numbered_symbols('z')
    qsyms = []
    def fr():
        sym = sp.Symbol(str(next(cnt)), real=True); inputs.append(sym); return sym
    radial_fixed = [False]
    def Rblock(rr, cc, final):
        Rb = sp.zeros(rr, cc)
        for i in range(rr):
            for j in range(cc):
                if final and (not radial_fixed[0]) and i == 0 and j == 0:
                    Rb[i, j] = sp.Integer(1); radial_fixed[0] = True
                else:
                    Rb[i, j] = fr()
        return Rb
    Cs = {}; Ns_store = {}
    for s in range(1, L + 1):
        cols = M[s]; ts_in = t[s - 1]; ts = t[s]; r_s = t[s - 1] - t[s]; c_s = M[s] - t[s]
        if s == L:
            Cs[s] = u * Rblock(ts_in, cols, True); Ns_store[s] = None
        else:
            Ks = unit_lower(ts, fr)
            qd = [fr() + 1 for _ in range(ts)]
            for q in qd:
                qsyms.append(q)
            Ks = Ks * sp.diag(*qd) * unit_upper(ts, fr)
            Xs = sp.Matrix(r_s, ts, lambda i, j: fr()) if r_s > 0 else sp.zeros(0, ts)
            Ns = sp.Matrix(ts, c_s, lambda i, j: fr()) if c_s > 0 else sp.zeros(ts, 0)
            Ns_store[s] = Ns
            Rs = Rblock(r_s, c_s, False) if (r_s > 0 and c_s > 0) else sp.zeros(r_s, c_s)
            Ps = sp.Matrix.vstack(sp.eye(ts), Xs)
            Qs = sp.Matrix.hstack(sp.eye(ts), Ns)
            base = Ps * Ks * Qs
            resid = sp.zeros(ts + r_s, ts + c_s)
            for i in range(r_s):
                for j in range(c_s):
                    resid[ts + i, ts + j] = u * Rs[i, j]
            Cs[s] = base + resid
    # factors: A^(0) = C_1 ; A^(s) = [[C_{s+1} - N_s W_{s+1}],[W_{s+1}]] for s=1..L-1
    A = [None] * L
    A[0] = Cs[1]
    for s in range(1, L):
        rows = M[s]; cols = M[s + 1]; ts = t[s]; c_s = M[s] - t[s]
        Csp1 = Cs[s + 1]                                  # (t_s) x M_{s+1}  rows
        W = sp.Matrix(c_s, cols, lambda i, j: fr()) if c_s > 0 else sp.zeros(0, cols)
        Ns = Ns_store[s]
        top = Csp1 - (Ns * W if (Ns is not None and Ns.cols == W.rows and W.rows > 0) else sp.zeros(ts, cols))
        A[s] = sp.Matrix.vstack(top, W)
    return A, u, inputs, minAdm, t, qsyms


def verify(M, do_jac=True):
    M = tuple(M)
    A, u, inputs, minAdm, t, qsyms = build_factors(M)
    # shapes check
    shapes_ok = all(A[s].rows == M[s] and A[s].cols == M[s + 1] for s in range(len(A)))
    P = A[0]
    for s in range(1, len(A)):
        P = P * A[s]
    F = sp.expand(sum(P[i, j]**2 for i in range(P.rows) for j in range(P.cols)))
    degs = sorted(set(mm[0] for mm in sp.Poly(F, u).monoms())) if F != 0 else []
    flat = [A[s][i, j] for s in range(len(A)) for i in range(A[s].rows) for j in range(A[s].cols)]
    out = {'M': M, 'minAdm': minAdm, 'shapes_ok': shapes_ok, 'u_degs': degs,
           'flatDim': len(flat), 'ninputs': len(inputs)}
    out['G1_rate'] = (degs and degs[0] == 2)
    if out['G1_rate']:
        V = sp.expand(sp.cancel(F / u**2))
        out['V_poly'] = V.is_polynomial()
        U0 = sp.expand(V.subs(u, 0))
        out['G2_Unonzero'] = (U0 != 0)
        out['U_sector'] = sp.simplify(U0.subs({s: sp.Rational(1, 3) for s in inputs if s != u}))
    if do_jac and len(flat) == len(inputs):
        J = sp.Matrix(len(flat), len(flat), lambda r, c: sp.diff(flat[r], inputs[c]))
        det = sp.factor(sp.expand(J.det()))
        out['det'] = det
        if det != 0:
            out['det_u_exp'] = min(mm[0] for mm in sp.Poly(det, u).monoms())
            out['G3'] = (out['det_u_exp'] == minAdm - 1)
        else:
            out['G3'] = 'DET=0'
    elif do_jac:
        out['G3'] = f'dim {len(flat)} vs {len(inputs)}'
    return out


if __name__ == "__main__":
    import sys
    cases = [(3, 3, 4), (3, 3, 3, 3), (5, 3, 4), (5, 4, 3, 2)]
    if len(sys.argv) > 1:
        cases = [tuple(int(x) for x in a.split(',')) for a in sys.argv[1:]]
    for M in cases:
        r = verify(M)
        print(f"M={r['M']} minAdm={r['minAdm']} shapes_ok={r['shapes_ok']} flatDim={r['flatDim']} ninputs={r['ninputs']}")
        print(f"   u-degs={r['u_degs']} G1={r.get('G1_rate')} Vpoly={r.get('V_poly')} G2={r.get('G2_Unonzero')} U@sec={r.get('U_sector')}")
        print(f"   det={r.get('det')} u_exp={r.get('det_u_exp')} G3(want {r['minAdm']-1})={r.get('G3')}")
        print()
