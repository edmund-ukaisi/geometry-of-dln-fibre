import numpy as np
from itertools import product
import sympy as sp

# (2,2,2): N=2 arrows (0->1, 1->2), dims d=(2,2,2). Diagonal case e=d.
# G_d = GL_2 x GL_2 x GL_2.  dim G = sum d_v^2 = 4+4+4 = 12.
# C^0 = prod_v Mat(d_v x d_v) = Mat2 x Mat2 x Mat2, dim = 12. (= Lie G, e=d)
# C^1 = prod_i Mat(d_{i+1} x d_i) = Mat(2x2) x Mat(2x2), dim = 4+4 = 8.
# delta^0(phi)_i = phi_{i+1} M_i - M_i phi_i  (e=d so N_i=M_i).
#
# We test the (1,1)-orbit: M = M00 + M01 + M12 + M22 (interval modules) -> orbitLinearCodim=3.
# And the zero-product locus M00^2 + M12^2 -> codim=4.
#
# Build the interval-module direct sum tuple M_i (2x2 matrices) for a given list of intervals.
# Interval module M_{a,b} on vertex set Fin 3, a<=b: dim vector = indicator [a,b]; arrow maps = identity 1
# where both endpoints in [a,b], else 0. We assemble the block-diagonal direct sum.

def interval_dimvec(a,b,Nv=3):
    return [1 if a<=w<=b else 0 for w in range(Nv)]

def interval_arrow(a,b,i):
    # arrow i: i -> i+1. map is 1x1 [[1]] if both i and i+1 in [a,b], else appropriate zero block
    src = 1 if a<=i<=b else 0
    tgt = 1 if a<=i+1<=b else 0
    if src==1 and tgt==1:
        return np.array([[1.0]])
    return np.zeros((tgt,src))

def directsum_tuple(intervals, Nv=3):
    # returns dimvec d (list len Nv) and arrow maps M[i] (matrix d_{i+1} x d_i) for i in 0..Nv-2
    d=[0]*Nv
    for (a,b) in intervals:
        dv=interval_dimvec(a,b,Nv)
        for w in range(Nv): d[w]+=dv[w]
    M=[]
    for i in range(Nv-1):
        blocks=[interval_arrow(a,b,i) for (a,b) in intervals]
        # block diagonal
        rows=sum(blk.shape[0] for blk in blocks); cols=sum(blk.shape[1] for blk in blocks)
        Mi=np.zeros((rows,cols)); r=0;c=0
        for blk in blocks:
            Mi[r:r+blk.shape[0], c:c+blk.shape[1]]=blk; r+=blk.shape[0]; c+=blk.shape[1]
        M.append(Mi)
    return d,M

def delta0_matrix(d,M,Nv=3):
    # C^0 = prod_v Mat(d_v x d_v), C^1 = prod_i Mat(d_{i+1} x d_i)
    # phi = (phi_0,...,phi_{Nv-1}), delta0(phi)_i = phi_{i+1} M_i - M_i phi_i
    dimC0=sum(dv*dv for dv in d)
    dimC1=sum(d[i+1]*d[i] for i in range(Nv-1))
    # build the linear map as a numpy matrix dimC1 x dimC0
    # index phi by (v, r, c). flatten.
    c0idx=[]
    for v in range(Nv):
        for r in range(d[v]):
            for c in range(d[v]):
                c0idx.append((v,r,c))
    c1idx=[]
    for i in range(Nv-1):
        for r in range(d[i+1]):
            for c in range(d[i]):
                c1idx.append((i,r,c))
    A=np.zeros((len(c1idx),len(c0idx)))
    for col,(v,r,c) in enumerate(c0idx):
        # phi = E_{r,c} at vertex v, zero elsewhere
        phi=[np.zeros((d[w],d[w])) for w in range(Nv)]
        phi[v][r,c]=1.0
        for i in range(Nv-1):
            val= phi[i+1]@M[i] - M[i]@phi[i]
            for rr in range(d[i+1]):
                for cc in range(d[i]):
                    row=c1idx.index((i,rr,cc))
                    A[row,col]+=val[rr,cc]
    return A,dimC0,dimC1

for name,intervals in [("(1,1)-orbit",[(0,0),(0,1),(1,2),(2,2)]),
                       ("zero-product",[(0,0),(0,0),(1,2),(1,2)])]:
    d,M=directsum_tuple(intervals)
    A,dimC0,dimC1=delta0_matrix(d,M)
    rank_delta0=np.linalg.matrix_rank(A)
    dimG=sum(dv*dv for dv in d)   # = dimC0 here (e=d)
    ker_delta0=dimC0-rank_delta0  # = finrank End(M) = finrank Hom(M,M)
    dim_OM = dimG - ker_delta0    # orbit-stabilizer prediction
    codim = dimC1 - rank_delta0   # orbitLinearCodim = dim Ext1
    print(f"{name}: d={d}")
    print(f"  dimG=sum d_v^2 = {dimG}; dimC0={dimC0}; dimC1={dimC1}")
    print(f"  rank(delta0)=finrank(range)={rank_delta0}; ker(delta0)=finrank End(M)={ker_delta0}")
    print(f"  dim O_M (= dimG - dim Stab) = {dim_OM}")
    print(f"  finrank(range delta0) = {rank_delta0}")
    print(f"  CHECK dim O_M == finrank(range delta0): {dim_OM==rank_delta0}")
    print(f"  orbitLinearCodim = dimC1 - rank = {codim}")
    print()
