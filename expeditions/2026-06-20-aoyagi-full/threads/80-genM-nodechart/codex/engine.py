"""
Radial-separability engine for the R1-LOWER interior chart (Route A / chartParamsGen).

Reconstructs the Lean `chainOfMt`/`GenBlk` chart symbolically:
  - Widths Wext (ambient = M k) and Text (compressed: Text 0 = M0, Text(k+1)=t k).
  - Per-boundary block data: Bmat, Nblk, Wblk, Rmat (interior), Rfin (leaf).
  - C k (interior, k<L) = Bmat k * chainQ(N_k) + u * Rmat k
    C L (leaf)          = u * Rfin L
    chainQ(N) = [ I_{t} | N ]   (t = Text(k+1) columns kept, residual = Wext k - Text(k+1))
  - A k = chainA(N_k, W_k, C(k+1))  (k<L)
    chainA(N,W,C) = [ C - N*W ; W ]   stacked: top Text(k+1) rows, bottom (Wext k - Text(k+1)) rows.
    A k is a (Wext k) x (Wext (k+1)) matrix.
  - chartParamsGen = (A 0, A 1, ..., A (L-1)) reindexed to M-widths; phi = paramsEquivFlat o chartParamsGen,
    paramsEquivFlat measure-preserving (det 1).  So |det Dphi| = |det D(A0,...,A_{L-1})| w.r.t. all coords.

The chart's free coordinates are: the radial pivot u (=x0), plus all the entries of the GenBlk data
matrices (Bmat, Nblk, Wblk, Rmat, Rfin) that are 'live' (i.e. symbolic, not structurally 0/1).

We build the chart output as a flat vector of all entries of A0..A_{L-1}, differentiate w.r.t. all the
free coords (one Jacobian), take det, factor it, and check:
  det = u^(minAdm-1) * (radial-independent factor)?
i.e. is d(det/u^(minAdm-1))/du == 0 exactly?
"""
import sympy as sp
from sympy import symbols, Matrix, eye, zeros, simplify, factor, diff, Rational

def chainQ(N, t, c):
    """[I_t | N] as a t x (t+c) matrix.  N is t x c."""
    Q = zeros(t, t + c)
    for i in range(t):
        Q[i, i] = 1
    for i in range(t):
        for j in range(c):
            Q[i, t + j] = N[i, j]
    return Q

def chainA(N, W, C, t, c, mprime):
    """[C - N*W ; W] as (t+c) x mprime.
       C is t x mprime ; N is t x c ; W is c x mprime.  Top t rows = C - N*W, bottom c rows = W."""
    top = C - N * W   # t x mprime
    A = zeros(t + c, mprime)
    for i in range(t):
        for j in range(mprime):
            A[i, j] = top[i, j]
    for i in range(c):
        for j in range(mprime):
            A[t + i, j] = W[i, j]
    return A

def build_chart(L, M, t, blocks, u):
    """
    L, M (list len L+1), t (list len L+1, t[0]=M[0]); blocks: dict k-> {'B','N','W','R','Rfin'} sympy Matrices.
    Returns list of A matrices A[0..L-1] (each Wext k x Wext (k+1)).
    Widths: Wext k = M[k]; Text 0 = M[0], Text(k+1)=t[k].
    """
    Wext = lambda k: M[k]
    def Text(k):
        if k == 0: return M[0]
        return t[k-1]
    # C k
    C = {}
    # leaf
    C[L] = u * blocks[L]['Rfin']   # Text L x Wext L
    # interior, descending
    for k in range(L-1, -1, -1):
        tk1 = Text(k+1)
        ck  = Wext(k) - tk1
        Q = chainQ(blocks[k]['N'], tk1, ck)         # tk1 x Wext k
        C[k] = blocks[k]['B'] * Q + u * blocks[k]['R']   # Text k x Wext k
    # A k
    A = {}
    for k in range(L):
        tk1 = Text(k+1)
        ck  = Wext(k) - tk1
        mprime = Wext(k+1)
        A[k] = chainA(blocks[k]['N'], blocks[k]['W'], C[k+1], tk1, ck, mprime)
    return A, C

def chart_vector(A, L):
    """Flatten A0..A_{L-1} into a single column vector (row-major per layer)."""
    vec = []
    for k in range(L):
        Ak = A[k]
        for i in range(Ak.rows):
            for j in range(Ak.cols):
                vec.append(Ak[i, j])
    return vec

def jac_det_analysis(vec, coords, u, minAdm, label):
    n = len(vec)
    m = len(coords)
    print(f"=== {label} ===")
    print(f"  chart output dim = {n}, free coords = {m}, expect square: {n==m}")
    if n != m:
        print(f"  !! NON-SQUARE: output {n} vs coords {m}; cannot take det directly.")
        return None
    J = sp.Matrix(n, m, lambda i, j: sp.diff(vec[i], coords[j]))
    det = J.det()
    det = sp.expand(det)
    print(f"  det computed (expanded), now factoring...")
    fdet = sp.factor(det)
    print(f"  det = {fdet}")
    # check u-power: divide by u^(minAdm-1) and test d/du == 0
    pw = minAdm - 1
    quotient = sp.simplify(det / u**pw)
    quotient = sp.expand(quotient)
    du = sp.expand(sp.diff(quotient, u))
    separates = (du == 0)
    print(f"  minAdm-1 = {pw}; quotient det/u^{pw} ; d(quotient)/du == 0 ? {separates}")
    if not separates:
        print(f"  >>> RADIAL LEAK: d(det/u^{pw})/du = {sp.factor(du)}")
    # also extract exact u-degree
    poldeg = sp.Poly(det, u).degree() if det != 0 else None
    # lowest u power present:
    print(f"  det as poly in u: degree {poldeg}")
    return {'det': det, 'fdet': fdet, 'separates': separates, 'du': du}
