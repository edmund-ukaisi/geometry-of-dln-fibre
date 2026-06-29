"""
PER-PIECE FACTORIZATION of DFrame_M  (witness/obstruction adjudication).

Mission: does the fused-frame derivative DFrame_M factor as a PRODUCT of TRIANGULAR pieces
  DFrame_M = F_radial · prod_s F_s
with (i) the product reproducing DFrame_M; (ii) each F_s triangular wrt the b-0 ordering
(output-layer-s reads input-boundaries <= s); (iii) per-piece det a UNIFORM monomial across M.

We DO NOT reproduce the bespoke Frame3333Deriv (13 SCC blocks). Instead we test the structural
claim directly on the FUSED chart Phi = flatten(build(...)), exact sympy.

The chart (families.py / radial-sep prompt conventions):
  chainQ(N_k) = [I_{T_{k+1}} | N_k]          (T_{k+1} x W_k)
  C_L = u*Rfin                                (T_L x W_L)
  C_k = B_k*chainQ(N_k) + u*R_k               (T_k x W_k),  k<L
  A_k = [ C_{k+1} - N_k*W_k ; W_k ]           (W_k x W_{k+1})
  output = (A_0..A_{L-1}) flattened.

B_k is LDU-parametrized so det-related factors are monomials. We keep B_k as a general
LOWER*UPPER (unit-diagonal L, unit-diagonal U, diagonal D) so |det B_k| = prod of D-pivots,
which is the schurChartFactor's |det K|^{...} content in monomial form.
"""
import sympy as sp
from sympy import symbols, Matrix, eye, zeros, simplify, factor, expand

# ---------- chart builders (faithful, from families.py) ----------
def chainQ(N, t, c):
    Q = zeros(t, t + c)
    for i in range(t): Q[i, i] = 1
    for j in range(c):
        for i in range(t): Q[i, t + j] = N[i, j]
    return Q

def chainA(N, W, C, t, c, mprime):
    top = C - N * W
    A = zeros(t + c, mprime)
    for i in range(t):
        for j in range(mprime): A[i, j] = top[i, j]
    for i in range(c):
        for j in range(mprime): A[t + i, j] = W[i, j]
    return A

def build(L, M, T, blocks, u):
    # M = ambient widths W_0..W_L ;  T = compressed T_0..T_L  (T_0=M_0)
    C = {}
    C[L] = u * blocks[L]['Rfin']
    for k in range(L-1, -1, -1):
        tk1 = T[k+1]; ck = M[k] - tk1
        Q = chainQ(blocks[k]['N'], tk1, ck)
        C[k] = blocks[k]['B'] * Q + u * blocks[k]['R']
    A = {}
    for k in range(L):
        tk1 = T[k+1]; ck = M[k] - tk1; mprime = M[k+1]
        A[k] = chainA(blocks[k]['N'], blocks[k]['W'], C[k+1], tk1, ck, mprime)
    return A, C

def flatten(A, L):
    vec = []
    for k in range(L):
        Ak = A[k]
        for i in range(Ak.rows):
            for j in range(Ak.cols):
                vec.append(Ak[i, j])
    return vec
