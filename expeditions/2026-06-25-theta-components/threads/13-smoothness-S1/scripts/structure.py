"""
Structural read of the fibre Jacobian: dF_A(Adot) = sum_i L_i Adot_i R_i,
  L_i = A_N..A_{i+1} (d_N x d_i),  R_i = A_{i-1}..A_1 (d_{i-1} x d_0).
Image = sum_i col(L_i) (x) row(R_i)  inside Mat_{d_N x d_0}.
rank(J) = dim of this sum of "rank-1-tensor" subspaces.

We compute, at a generic top fibre point, the ranks of each L_i, R_i, and the
rank of J, to read off the mechanism.
"""
import sympy as sp
from fibjac import build_symbolic, mult_product, E_r
from r0_rank import generic_zero_product_point
from rank_points import build_point_blocktri
import random

def partials(d, factors):
    N = len(d)-1
    # L_i = A_N..A_{i+1} for i=1..N (1-based); factors[k] = A_{k+1}
    # In 0-based factor list factors[0..N-1] = A_1..A_N.
    # For arrow index j (1-based, j=1..N): L_j = product of factors[j..N-1] (A_{j+1}..A_N) left-mult
    # R_j = product of factors[0..j-2] (A_1..A_{j-1})
    Ls, Rs = [], []
    for j in range(1, N+1):
        # L_j = A_N * ... * A_{j+1}
        if j == N:
            Lj = sp.eye(d[N])
        else:
            Lj = factors[N-1]
            for k in range(N-2, j-1, -1):
                Lj = Lj * factors[k]
        # R_j = A_{j-1} * ... * A_1
        if j == 1:
            Rj = sp.eye(d[0])
        else:
            Rj = factors[j-2]
            for k in range(j-3, -1, -1):
                Rj = factors[k] * Rj
        Ls.append(Lj); Rs.append(Rj)
    return Ls, Rs

def jac_image_rank(d, r, factors):
    """Build the image subspace span of {L_i * E_{ab} * R_i} as vectors in k^{dN*d0}."""
    N = len(d)-1
    Ls, Rs = partials(d, factors)
    vecs = []
    for j in range(N):
        Lj, Rj = Ls[j], Rs[j]
        rows, cols = d[j+1], d[j]   # Adot_{j+1} is (d_{j+1} x d_j)
        for a in range(rows):
            for b in range(cols):
                Eab = sp.zeros(rows, cols); Eab[a,b] = 1
                M = Lj * Eab * Rj    # (d_N x d_0)
                vecs.append([M[x,y] for x in range(d[N]) for y in range(d[0])])
    Jimg = sp.Matrix(vecs)   # rows = directions, cols = dN*d0 entries
    return Jimg.rank(), [Lj.rank() for Lj in Ls], [Rj.rank() for Rj in Rs]

def report_r0(d, ntry=12):
    print(f"--- d={d} r=0 ---")
    from collections import Counter
    rks=[]
    for s in range(ntry):
        pt = generic_zero_product_point(d, s)
        if pt is None: continue
        if sp.simplify(mult_product(pt)) != sp.zeros(d[-1], d[0]): continue
        rk, lr, rr = jac_image_rank(d, 0, pt)
        rks.append((rk, tuple(lr), tuple(rr)))
    for item, c in Counter(rks).items():
        print(f"   rank(J)={item[0]:2d}  rank(L_i)={item[1]}  rank(R_i)={item[2]}  (x{c})")

def report_rpos(d, r, ntry=4):
    print(f"--- d={d} r={r} ---")
    N=len(d)-1
    for zf in range(N):
        pt = build_point_blocktri(d, r, zf)
        if pt is None: continue
        if sp.simplify(mult_product(pt)-E_r(d[-1],d[0],r)) != sp.zeros(d[-1],d[0]): continue
        rk, lr, rr = jac_image_rank(d, r, pt)
        print(f"   comp B_{zf}=0: rank(J)={rk}  rank(L_i)={lr}  rank(R_i)={rr}")

if __name__ == "__main__":
    report_rpos([2,2,2],1)
    report_rpos([2,2,2,2],1)
    report_rpos([3,3,3],2)
    report_r0([2,2,2,2,2])
