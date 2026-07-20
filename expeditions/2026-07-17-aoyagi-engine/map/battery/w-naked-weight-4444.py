#!/usr/bin/env python3
# kills: naked-weight-route
# config: M=(4,4,4,4), t=2, a=2; det(QQ^T) = det(A2)^2 det(A3)^2 (A2 square)
# provenance: threads/00-genesis/architecture-cert.md (obligation-2 refutation, 2026-07-17)
"""The flagship-cell falsity witness. Two exact facts compose:

(1) ALGEBRA: for square A2, det(A2 A3 (A2 A3)^T) = det(A2)^2 det(A3)^2 — verified
    here in exact integer arithmetic on deterministic test matrices, so the naked
    weight SEPARATES into |det A2|^{-a} |det A3|^{-a}.
(2) ANALYSIS: {det = 0} has smooth points inside the box (diag(0,1,1,1): the
    gradient of det there is the adjugate, which is nonzero — checked exactly), so
    near it |det|^{-2} dominates a 1D |u|^{-2} integral, divergent (exact shells:
    shell k contributes >= 2^{-k-1} * 2^{2k} -> unbounded terms).
Exit 1 (killed) iff both facts verify."""
import sys, itertools
from fractions import Fraction

def det(m):
    n = len(m)
    if n == 1: return m[0][0]
    return sum((-1) ** j * m[0][j] * det([r[:j] + r[j+1:] for r in m[1:]]) for j in range(n))

def matmul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]

def transpose(a):
    return [list(r) for r in zip(*a)]

# (1) exact separability on deterministic integer matrices
ok_alg = True
for seed in range(3):
    A2 = [[(i * 7 + j * 3 + seed * 5) % 11 - 5 for j in range(4)] for i in range(4)]
    A3 = [[(i * 5 + j * 9 + seed * 7) % 13 - 6 for j in range(4)] for i in range(4)]
    Q = matmul(A2, A3)
    lhs = det(matmul(Q, transpose(Q)))
    rhs = det(A2) ** 2 * det(A3) ** 2
    ok_alg &= (lhs == rhs)

# (2) smooth point of {det=0} in the box: diag(0,1,1,1); grad det = adjugate != 0
D = [[1 if i == j and i > 0 else 0 for j in range(4)] for i in range(4)]
adj_00 = det([r[1:] for r in D[1:]])  # cofactor at (0,0) = det(I3) = 1
ok_smooth = (det(D) == 0 and adj_00 == 1)

# 1D shells for exponent 2: term_k >= 2^{-k-1} * 2^{2k} = 2^{k-1} -> unbounded
terms = [Fraction(2) ** (-k - 1) * Fraction(4) ** k for k in range(10)]
ok_div = all(terms[i + 1] > terms[i] for i in range(9))

print(f"separability(exact)={ok_alg}  smooth-zero-in-box={ok_smooth}  shells-unbounded={ok_div}")
sys.exit(1 if (ok_alg and ok_smooth and ok_div) else 0)
