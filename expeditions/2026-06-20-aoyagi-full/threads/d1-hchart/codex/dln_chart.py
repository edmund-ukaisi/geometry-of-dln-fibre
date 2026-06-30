"""
Exact-algebra stress test of the DLN D1 hchart (L=2) f'-invertibility design.

Setup:
  Params (A1 in Mat_{H0 x H1}, A2 in Mat_{H1 x H2}). Flatten to R^N, N = H0*H1 + H1*H2.
  Order: first all entries of A1 (row-major), then all entries of A2 (row-major).
  Optimal v = (A1v, A2v) with A1v A2v = B.
  Tangent delta = (d1, d2). Dg(v)[delta] = d1 A2v + A1v d2  in Mat_{H0 x H2}.
  Dg(v) : R^N -> Mat_{H0 x H2} (image flattened row-major, H0*H2 components).

We build the matrix M of Dg(v): rows indexed by output entries (i,j) in [H0]x[H2],
cols indexed by the N flat input coords.

Then test the chart-design questions.
"""
import sympy as sp
from sympy import Matrix, Rational, zeros, eye
from itertools import combinations


def dg_matrix(A1v, A2v):
    """Return (M, row_index, col_index) where M is the H0H2 x N matrix of Dg(v)."""
    H0, H1 = A1v.shape
    H1b, H2 = A2v.shape
    assert H1 == H1b
    N = H0 * H1 + H1 * H2
    # column index helpers
    def c1(a, b):  # entry (a,b) of A1, a in [H0], b in [H1]
        return a * H1 + b
    def c2(a, b):  # entry (a,b) of A2, a in [H1], b in [H2]
        return H0 * H1 + a * H2 + b
    rows = []
    row_index = []
    for i in range(H0):
        for j in range(H2):
            row_index.append((i, j))
            r = [Rational(0)] * N
            # g_ij = sum_k (A1+d1)_{i k} (A2+d2)_{k j} - B_ij
            # derivative wrt d1_{i k}: A2v_{k j}
            for k in range(H1):
                r[c1(i, k)] += A2v[k, j]
            # derivative wrt d2_{k j}: A1v_{i k}
            for k in range(H1):
                r[c2(k, j)] += A1v[i, k]
            rows.append(r)
    M = Matrix(rows)
    return M, row_index, (H0, H1, H2)


def has_coord_complement(M, S_rows):
    """
    Given M (full Dg matrix, all H0H2 rows) and a chosen subset S_rows of output-rows
    (the selected gradient functionals g_S), test whether there EXISTS a coordinate
    subset P of size N - |S| such that {grad_k : k in S} union {coord funcs in P} is a
    basis of (R^N)*.

    The selected gradient functionals are the rows G = M[S_rows, :] (each is a functional
    in (R^N)*). A coordinate functional e_p^* is the p-th standard basis covector.
    {G rows} u {e_p : p in P} is a basis  <=>  the (|S|+|P|) x N matrix is invertible
    (square when |S|+|P| = N).

    Equivalent test: G has full row rank |S| (else can't even be independent), and the
    columns NOT in some complement... Concretely: a coordinate complement of size N-|S|
    exists  <=>  there is a set C of |S| columns such that G restricted to columns C is
    invertible (then P = all columns not in C). Because adding e_p for p in P =
    complement-of-C zeroes out those columns, and the determinant of the full square
    matrix factors as det(G[:,C]) up to sign.

    So: coordinate complement exists  <=>  G (rows = S) has an |S|x|S| invertible
    column-submatrix  <=>  rank(G) = |S| AND ... actually rank(G)=|S| ALWAYS gives such a
    submatrix (a maximal nonzero minor). So existence of coordinate complement is
    EQUIVALENT to G having full row rank |S|.
    """
    G = M[S_rows, :]
    return G.rank() == len(S_rows)


def find_coord_complement(M, S_rows, N):
    """Return a concrete column set C (size |S|) s.t. G[:,C] invertible; P = complement."""
    G = M[S_rows, :]
    s = len(S_rows)
    # find a maximal independent set of columns of G
    cols = []
    cur = zeros(s, 0)
    for c in range(N):
        trial = cur.row_join(G[:, c])
        if trial.rank() > cur.rank():
            cur = trial
            cols.append(c)
            if len(cols) == s:
                break
    if len(cols) < s:
        return None, None
    P = [p for p in range(N) if p not in cols]
    return cols, P


def q3_invertible_minor(M, nReg):
    """
    Q3 reframing: find an nReg x nReg invertible submatrix of M (rows = some S of outputs,
    cols = some W of input coords). Returns (S, W) or None.
    Existence follows from rank(M) >= nReg.
    """
    rank = M.rank()
    if rank < nReg:
        return None, None, rank
    # pick nReg independent rows, then nReg independent cols within them
    H0H2, N = M.shape
    # independent rows
    rsel = []
    cur = zeros(0, N)
    for i in range(H0H2):
        trial = cur.col_join(M[i, :])
        if trial.rank() > cur.rank():
            cur = trial
            rsel.append(i)
            if len(rsel) == nReg:
                break
    Msub = M[rsel, :]
    # independent cols within Msub
    csel = []
    curc = zeros(nReg, 0)
    for c in range(N):
        trial = curc.row_join(Msub[:, c])
        if trial.rank() > curc.rank():
            curc = trial
            csel.append(c)
            if len(csel) == nReg:
                break
    return rsel, csel, rank


if __name__ == "__main__":
    # Q2 witness: H = (3,3,3), r = 1
    # A1v = diag(1,1,0), A2v = diag(1,0,0), product = diag(1,0,0) = B, rank B = 1.
    H0 = H1 = H2 = 3
    A1v = sp.diag(1, 1, 0)
    A2v = sp.diag(1, 0, 0)
    B = A1v * A2v
    print("A1v =", A1v.tolist())
    print("A2v =", A2v.tolist())
    print("B = A1v A2v =", B.tolist(), " rank B =", B.rank())
    print("rk A1v =", A1v.rank(), " rk A2v =", A2v.rank())

    r = B.rank()
    nReg = r * (H0 + H2 - r)
    print("nReg =", nReg)

    M, ridx, dims = dg_matrix(A1v, A2v)
    N = H0 * H1 + H1 * H2
    print("N =", N, " M shape =", M.shape, " rank Dg(v) = nReg_v =", M.rank())
    print()
    print("M =")
    sp.pprint(M)
