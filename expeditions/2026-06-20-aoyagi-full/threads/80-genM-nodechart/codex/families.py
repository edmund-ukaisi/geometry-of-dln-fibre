"""
Deeper-family generator for radial-separability testing.

We construct charts with the SAME structural recursion as (3,3,3,3)/genM, but vary L and widths,
and crucially the R_k (interior radial-coupling) matrices. To keep the Jacobian SQUARE we must supply
exactly flatDim = sum_k W_k*W_{k+1} free coordinates. We allocate coords as:
  - u = x0 (the radial pivot)
  - then per layer the live free entries of B_k, N_k, W_k (interior) and Rfin (leaf),
    PLUS the free-scaled entries inside R_k (the eta-type couplings).

To make this faithful AND square we follow the genM template's accounting:
  For each interior boundary k<L:  the layer A_k is W_k x W_{k+1}.
  Its free content = N_k (T_{k+1} x c_k) + W_k-lift (c_k x W_{k+1}) + the kept-block content.
  The kept block C_{k+1} is supplied by boundary k+1, so we must NOT double count: each boundary k
  "owns" exactly W_k*W_{k+1} coords. Concretely the genM template assigns to layer k the coords that
  first appear in A_k's lift rows (W_k) and the NEW content of C_{k+1} relative to deeper layers.

For the structural separability question the cleanest faithful family keeps the EXACT genM shapes.
Rather than re-derive the global coordinate accounting (the Lean-side bookkeeping), we test the
DETERMINANT FACTOR structure directly: build A_0..A_{L-1} with INDEPENDENT symbolic content in each
block, and check the radial factorization of the LAYER-GRADED determinant product.

We use TWO complementary tests:

TEST 1 (faithful square chart, hand-balanced coords): replicate genM with chosen widths so the count
balances, exactly like B_det3333.  We verify det = u^(minAdm-1) * (u-free).

TEST 2 (per-layer block determinant): the layer-filtration claim says
  det(J) = prod_k det(layer-k diagonal block),
and the radial claim says only ONE diagonal block carries u (to the front power). We test each layer's
diagonal block determinant for u-dependence in isolation, on stress configurations (t>=2 interior core
with multi-coupling R_k).
"""
import sympy as sp
from sympy import symbols, Matrix, eye, zeros

def chainQ(N, t, c):
    Q = zeros(t, t + c)
    for i in range(t):
        Q[i, i] = 1
    for j in range(c):
        for i in range(t):
            Q[i, t + j] = N[i, j]
    return Q

def chainA(N, W, C, t, c, mprime):
    top = C - N * W
    A = zeros(t + c, mprime)
    for i in range(t):
        for j in range(mprime):
            A[i, j] = top[i, j]
    for i in range(c):
        for j in range(mprime):
            A[t + i, j] = W[i, j]
    return A

def build(L, M, t, blocks, u):
    Wext = lambda k: M[k]
    def Text(k):
        return M[0] if k == 0 else t[k-1]
    C = {}
    C[L] = u * blocks[L]['Rfin']
    for k in range(L-1, -1, -1):
        tk1 = Text(k+1); ck = Wext(k) - tk1
        Q = chainQ(blocks[k]['N'], tk1, ck)
        C[k] = blocks[k]['B'] * Q + u * blocks[k]['R']
    A = {}
    for k in range(L):
        tk1 = Text(k+1); ck = Wext(k) - tk1; mprime = Wext(k+1)
        A[k] = chainA(blocks[k]['N'], blocks[k]['W'], C[k+1], tk1, ck, mprime)
    return A, C

def flatten(A, L):
    vec = []
    for k in range(L):
        Ak = A[k]
        for i in range(Ak.rows):
            for j in range(Ak.cols):
                vec.append(Ak[i,j])
    return vec

def analyze(vec, coords, u, label, pw=None):
    n, m = len(vec), len(coords)
    print(f"=== {label} ===  (output {n}, coords {m}, square={n==m})")
    if n != m:
        print("  NON-SQUARE — skipping det")
        return None
    J = sp.Matrix(n, m, lambda i,j: sp.diff(vec[i], coords[j]))
    det = sp.expand(J.det())
    if det == 0:
        print("  det == 0 (degenerate chart / coord allocation)")
        return {'det':0}
    fdet = sp.factor(det)
    print(f"  det = {fdet}")
    P = sp.Poly(det, u)
    lo = min(P.monoms(), key=lambda mm: mm[0])[0] if P.monoms() else 0
    hi = P.degree()
    print(f"  u appears with powers from {lo} to {hi}")
    sep = (lo == hi)
    print(f"  u SEPARATES as single front power? {sep}  (front power = {lo})")
    if not sep:
        q = sp.expand(det/u**lo)
        du = sp.expand(sp.diff(q, u))
        print(f"  >>> LEAK: det/u^{lo} still depends on u; d/du = {sp.factor(du)}")
    if pw is not None:
        print(f"  expected front power minAdm-1 = {pw}: match={lo==pw}")
    return {'det':det, 'fdet':fdet, 'lo':lo, 'hi':hi, 'sep':sep}
