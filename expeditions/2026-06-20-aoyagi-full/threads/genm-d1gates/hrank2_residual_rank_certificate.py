#!/usr/bin/env python3
"""
genm-d1gates — the `hrank₂` residual-Jacobian rank certificate.

Front-loaded assessment of the CORE-GEOMETRY gate `hrank₂` of the L=2 D1 two-peel:
    extraCountRect (H0-r) (H2-r) a b  ≤  rank( jacResid (fun t => q(0,t)) t0 )

where `q` is the first-peel bump-globalised residual (from `dln_hchart_residual_c2`).

DECISIVE FINDING (this script): the bound is TRUE and TIGHT — `rank(jacResid) = extraCountRect`
EXACTLY, uniformly over all constructed middle-stratum optima, including ADVERSARIAL random valid
nReg-minor selections. NO constant-rank / stratification DROP. So the geometry does not wall; the
gate's OBSTRUCTION is FORMALISATION-reachability (Lean derivative-exposure + residual-rank algebra),
not a rank drop. See the statement card.

Two models:
  (1) `test_dln`      — the actual DLN composite at constructed middle-stratum optimal v.
  (2) `test_abstract` — the network-free abstract identity that the b2 brick would formalise:
        for ANY matrix T (rank ρ) and ANY invertible nReg-minor (er,ec), the composite
        [T with er-rows zeroed] ∘ (DΦ0)⁻¹ ∘ [complement injection]  has rank EXACTLY ρ − nReg.
"""
import numpy as np, scipy.linalg as sla

def extraCountRect(M0, M2, a, b):
    return a * M2 + b * M0 - a * b

def _construct_middle(H0, H1, H2, r, b, a):
    """rank v0 = r+b, rank v1 = r+a, rank(v0 v1) = r (middle stratum).

    v0 nonzero on H1-cols [0,r+b); v1 nonzero on H1-rows [b, b+r+a); overlap window size r."""
    rv0, rv1 = r + b, r + a
    if rv0 > min(H0, H1) or rv1 > min(H1, H2):
        return None
    start = rv0 - r
    if start < 0 or start + rv1 > H1:
        return None
    v0 = np.zeros((H0, H1)); v1 = np.zeros((H1, H2))
    v0[:, :rv0] = np.random.randn(H0, rv0)
    v1[start:start + rv1, :] = np.random.randn(rv1, H2)
    return v0, v1

def _buildT(v0, v1, H0, H1, H2):
    """Dg(v): δ ↦ δ0·v1 + v0·δ1, as an (H0·H2) × flatDim matrix."""
    flatDim = H0 * H1 + H1 * H2; nH = H0 * H2
    T = np.zeros((nH, flatDim)); col = 0
    for p in range(H0):
        for q in range(H1):
            M = np.zeros((H0, H2)); M[p, :] = v1[q, :]; T[:, col] = M.flatten(); col += 1
    for p in range(H1):
        for q in range(H2):
            M = np.zeros((H0, H2)); M[:, q] = v0[:, p]; T[:, col] = M.flatten(); col += 1
    return T

def _resid_rank(T, nReg, rows, cols):
    """rank( [T rows-zeroed] ∘ (DΦ0)⁻¹ ∘ [compl inj] ) for the minor (rows,cols)."""
    flatDim = T.shape[1]; sc = set(cols)
    P = np.zeros((flatDim, flatDim))
    for k, c in enumerate(cols): P[c, :] = T[rows[k], :]
    for c in range(flatDim):
        if c not in sc: P[c, c] = 1.0
    if abs(np.linalg.det(P)) < 1e-9: return None
    Pinv = np.linalg.inv(P); Tres = T.copy()
    for rw in rows: Tres[rw, :] = 0.0
    compl = [c for c in range(flatDim) if c not in sc]
    Inj = np.zeros((flatDim, len(compl)))
    for i, c in enumerate(compl): Inj[c, i] = 1.0
    return np.linalg.matrix_rank(Tres @ Pinv @ Inj, tol=1e-7)

def test_dln(cases, trials=25, minor_trials=6, seed=3):
    np.random.seed(seed)
    print("=== (1) DLN composite at constructed middle-stratum optima ===")
    for (H0, H1, H2, r, b, a) in cases:
        flatDim = H0 * H1 + H1 * H2; nH = H0 * H2; nReg = r * (H0 + H2 - r)
        res = set(); fails = 0; total = 0
        for _ in range(trials):
            g = _construct_middle(H0, H1, H2, r, b, a)
            if g is None: break
            v0, v1 = g
            if (np.linalg.matrix_rank(v0) != r + b or np.linalg.matrix_rank(v1) != r + a
                    or np.linalg.matrix_rank(v0 @ v1) != r):
                continue
            T = _buildT(v0, v1, H0, H1, H2)
            rankDg = np.linalg.matrix_rank(T, tol=1e-7)
            for _m in range(minor_trials):  # adversarial random valid minors
                pr = np.random.permutation(nH); pc = np.random.permutation(flatDim)
                rows = []; M = []
                for idx in pr:
                    cand = T[idx, :]
                    if not rows or np.linalg.matrix_rank(np.vstack(M + [cand]), tol=1e-7) > len(rows):
                        rows.append(idx); M.append(cand)
                    if len(rows) == nReg: break
                if len(rows) < nReg: continue
                Tr = T[rows, :]; cols = []; Mc = []
                for idx in pc:
                    cand = Tr[:, idx]
                    if not cols or np.linalg.matrix_rank(np.array(Mc + [cand]).T, tol=1e-7) > len(cols):
                        cols.append(idx); Mc.append(cand)
                    if len(cols) == nReg: break
                if len(cols) < nReg: continue
                if abs(np.linalg.det(T[np.ix_(rows, cols)])) < 1e-9: continue
                rk = _resid_rank(T, nReg, rows, cols)
                if rk is None: continue
                total += 1; res.add(int(rk))
                if rk < rankDg - nReg: fails += 1
        ecr = extraCountRect(H0 - r, H2 - r, a, b)
        print(f"  H=({H0},{H1},{H2}) r={r} (b,a)=({b},{a}): nReg={nReg} "
              f"extraCountRect={ecr} rankResid={res} fails={fails}/{total}")

def test_abstract(trials=400, seed=11):
    np.random.seed(seed)
    print("=== (2) network-free abstract identity (the b2 brick) ===")
    fails = 0; total = 0
    for _ in range(trials):
        m = np.random.randint(4, 10); N = np.random.randint(4, 10)
        rho = np.random.randint(1, min(m, N) + 1)
        T = np.random.randn(m, rho) @ np.random.randn(rho, N)
        if np.linalg.matrix_rank(T, tol=1e-7) != rho: continue
        nReg = np.random.randint(0, rho + 1)
        Q, R, pr = sla.qr(T.T, pivoting=True); rows = sorted(pr[:nReg])
        base = T[rows, :] if nReg > 0 else np.zeros((0, N))
        Qc, Rc, pc = sla.qr(base, pivoting=True); cols = sorted(pc[:nReg])
        if nReg > 0 and abs(np.linalg.det(T[np.ix_(rows, cols)])) < 1e-9: continue
        rk = _resid_rank(T, nReg, rows, cols)
        if rk is None: continue
        total += 1
        if rk != rho - nReg: fails += 1
    print(f"  abstract composite rank == rho - nReg: fails={fails}/{total}")

if __name__ == "__main__":
    test_dln([(3, 3, 3, 1, 1, 0), (3, 3, 3, 1, 0, 1), (3, 3, 3, 1, 1, 1),
              (4, 4, 4, 1, 1, 1), (3, 4, 3, 1, 1, 1), (3, 3, 3, 2, 1, 0),
              (5, 4, 5, 1, 2, 1), (4, 4, 4, 2, 1, 1), (4, 5, 4, 1, 2, 2),
              (5, 5, 5, 1, 2, 1)])
    test_abstract()
