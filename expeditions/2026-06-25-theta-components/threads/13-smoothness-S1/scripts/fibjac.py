"""
Fibre Jacobian rank + minor-unit certificate for S1.

Convention (matches Core.Setup): d = (d_0,...,d_N), N arrows, factors A_1..A_N,
  mult(A) = A_N * A_{N-1} * ... * A_1   (matrix product, right-to-left),
  A_i : (d_i) x (d_{i-1}).
Fibre target E_r = diag(I_r, 0) of shape d_N x d_0, rank exactly r.
Fibre = { A : mult(A) = E_r }, cut by the d_N * d_0 entry equations.

The differential at A:
  d(mult)_A( Adot ) = sum_i  (A_N..A_{i+1}) * Adot_i * (A_{i-1}..A_1).
Flatten to a (d_N*d_0) x (sum_i d_i d_{i-1}) matrix J = fibre Jacobian.

We want: rank(J) on the generic stratum = codim, and whether a single fixed
(codim)x(codim) minor is nonzero on the generic locus.
"""
import sympy as sp
from itertools import product as iproduct

def mk_factor_symbols(d, i):
    rows, cols = d[i+1], d[i]   # A_{i+1} is the (i+1)-th arrow? careful indexing
    return None

def mult_product(factors):
    # factors[i] is A_{i+1} (i=0..N-1), product = A_N * ... * A_1
    P = factors[-1]
    for k in range(len(factors)-2, -1, -1):
        P = P * factors[k]
    return P

def E_r(dN, d0, r):
    M = sp.zeros(dN, d0)
    for i in range(r):
        M[i, i] = 1
    return M

def build_symbolic(d):
    N = len(d) - 1
    factors = []   # factors[i] = A_{i+1}, shape d[i+1] x d[i]
    syms = []
    for i in range(N):
        rows, cols = d[i+1], d[i]
        block = sp.zeros(rows, cols)
        for a in range(rows):
            for b in range(cols):
                s = sp.Symbol(f"a{i+1}_{a}_{b}")
                block[a, b] = s
                syms.append(s)
        factors.append(block)
    return factors, syms

def fibre_jacobian(d, r):
    """Symbolic fibre Jacobian J (d_N*d_0 rows, sum d_i d_{i-1} cols) and the
    list of column symbols, plus the residual ideal generators F = mult - E."""
    N = len(d) - 1
    factors, syms = build_symbolic(d)
    P = mult_product(factors)
    E = E_r(d[N], d[0], r)
    F = P - E   # matrix of polynomials; entries are the cut equations
    Fentries = [F[a, b] for a in range(d[N]) for b in range(d[0])]
    # Jacobian: rows index Fentries, cols index syms
    J = sp.Matrix([[sp.diff(f, s) for s in syms] for f in Fentries])
    return J, syms, Fentries, factors, P

if __name__ == "__main__":
    import sys
    # quick self-test of conventions on (2,2,2): mult = A2*A1
    d = [2,2,2]; r = 1
    J, syms, F, factors, P = fibre_jacobian(d, r)
    print("d=",d,"r=",r)
    print("num cut equations (d_N*d_0) =", d[-1]*d[0])
    print("num variables (dim Rep) =", len(syms))
    print("Jacobian shape:", J.shape)
